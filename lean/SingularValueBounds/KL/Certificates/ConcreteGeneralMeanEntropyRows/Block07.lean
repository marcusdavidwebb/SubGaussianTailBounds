import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block00
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block01
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block02
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block06
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block08
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block09
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block10
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block11
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block12
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 490. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0490
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6490518452) (.branch 2 (.leaf 6297264631) (.leaf 6112113847))) (.branch 5 (.branch 4 (.leaf 5934622274) (.leaf 5764376856)) (.branch 6 (.leaf 5600992594) (.leaf 5444110134)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5293393619) (.leaf 5148528760)) (.branch 10 (.leaf 5009221112) (.leaf 4875194516))) (.branch 13 (.branch 12 (.leaf 4746189699) (.leaf 4621962998)) (.branch 14 (.leaf 4502285216) (.leaf 4386940569))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4275725735) (.branch 17 (.leaf 4168448983) (.leaf 4064929377))) (.branch 20 (.branch 19 (.leaf 3964996046) (.leaf 3868487514)) (.branch 21 (.leaf 3775251084) (.leaf 3685142272)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3598024282) (.leaf 3513767527)) (.branch 25 (.leaf 3432249176) (.leaf 3353352744))) (.branch 28 (.branch 27 (.leaf 3276967708) (.leaf 3202989150)) (.branch 29 (.leaf 3131317423) (.leaf 3061857848)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2994520424) (.branch 32 (.leaf 2929219559) (.leaf 2865873821))) (.branch 35 (.branch 34 (.leaf 2804405707) (.leaf 2744741420)) (.branch 36 (.leaf 2686810670) (.leaf 2630546477)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2575884996) (.leaf 2522765347)) (.branch 40 (.leaf 2471129457) (.leaf 2420921914))) (.branch 43 (.branch 42 (.leaf 2372089822) (.leaf 2324582677)) (.branch 44 (.leaf 2278352238) (.leaf 2233352414))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2189539153) (.branch 47 (.leaf 2146870339) (.leaf 2105305696))) (.branch 50 (.branch 49 (.leaf 2064806694) (.leaf 2025336465)) (.branch 51 (.leaf 1986859717) (.leaf 1949342663)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1912752940) (.leaf 1877059547)) (.branch 55 (.leaf 1842232776) (.leaf 1808244150))) (.branch 58 (.branch 57 (.leaf 1775066364) (.leaf 1742673233)) (.branch 59 (.leaf 1711039634) (.leaf 1680141462))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1649955576) (.branch 62 (.leaf 1620459762) (.leaf 1591632682))) (.branch 65 (.branch 64 (.leaf 1563453841) (.leaf 1535903545)) (.branch 66 (.leaf 1508962864) (.leaf 1482613599)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1456838249) (.leaf 1431619980)) (.branch 70 (.leaf 1406942594) (.leaf 1382790503))) (.branch 73 (.branch 72 (.leaf 1359148699) (.leaf 1336002732)) (.branch 74 (.leaf 1313338682) (.leaf 1291143140))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1269403182) (.branch 77 (.leaf 1248106353) (.leaf 1227240640))) (.branch 80 (.branch 79 (.leaf 1206794459) (.leaf 1186756636)) (.branch 81 (.leaf 1167116387) (.leaf 1147863303)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1128987336) (.leaf 1110478782)) (.branch 85 (.leaf 1092328266) (.leaf 1074526731))) (.branch 88 (.branch 87 (.leaf 1057065424) (.leaf 1039935883)) (.branch 89 (.leaf 1023129925) (.leaf 1006639635)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 990457358) (.branch 92 (.leaf 974575682) (.leaf 958987436))) (.branch 95 (.branch 94 (.leaf 943685676) (.leaf 928663676)) (.branch 96 (.leaf 913914922) (.leaf 899433101)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 885212095) (.leaf 871245974)) (.branch 100 (.leaf 857528985) (.leaf 844055552))) (.branch 103 (.branch 102 (.leaf 830820262) (.leaf 817817863)) (.branch 104 (.leaf 805043258) (.leaf 792491499))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 780157779) (.leaf 768037430)) (.branch 108 (.leaf 756125917) (.leaf 744418832))) (.branch 111 (.branch 110 (.leaf 732911890) (.leaf 721600926)) (.branch 112 (.leaf 710481889) (.leaf 699550837)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 688803939) (.leaf 678237462)) (.branch 116 (.leaf 667847774) (.leaf 657631341))) (.branch 119 (.branch 118 (.leaf 647584718) (.leaf 637704552)) (.branch 120 (.leaf 627987577) (.leaf 618430607)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 490).prefactor = (1189917262019187/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 490).cutoff/(generalMeanRows 490).c)).2 =
    (191706099288633/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 490).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 490).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 490).q*(generalMeanRows 490).c/2-2 = (72/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable139.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 490).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 490

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 490).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 490).criticalRate j.val*(generalMeanRows 490).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 490).c*(generalMeanRows 490).criticalPoint j.val)).2-
      (generalMeanRows 490).J/2-(generalMeanRows 490).error (generalMeanGrid j.val)+
      (generalMeanRows 490).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 490).c)).2-
      (generalMeanRows 490).J/2-(generalMeanRows 490).error 4 := by
  have he : (generalMeanRows 490).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 490) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 490)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0490

/-! Kernel-checked entropy margins for general spectral rectangle 491. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0491
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6115197797) (.branch 2 (.leaf 5929783039) (.leaf 5752227969))) (.branch 5 (.branch 4 (.leaf 5582098211) (.leaf 5418989607)) (.branch 6 (.leaf 5262525567) (.leaf 5112354707)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4968148734) (.leaf 4829600566)) (.branch 10 (.leaf 4696422627) (.leaf 4568345324))) (.branch 13 (.branch 12 (.leaf 4445115667) (.leaf 4326496016)) (.branch 14 (.leaf 4212262952) (.leaf 4102206243))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3996127905) (.branch 17 (.leaf 3893841345) (.leaf 3795170575))) (.branch 20 (.branch 19 (.leaf 3699949491) (.leaf 3608021217)) (.branch 21 (.leaf 3519237491) (.leaf 3433458111)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3350550416) (.leaf 3270388810)) (.branch 25 (.leaf 3192854318) (.leaf 3117834182))) (.branch 28 (.branch 27 (.leaf 3045221481) (.leaf 2974914775)) (.branch 29 (.leaf 2906817783) (.leaf 2840839077)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2776891798) (.branch 32 (.leaf 2714893394) (.leaf 2654765372))) (.branch 35 (.branch 34 (.leaf 2596433066) (.leaf 2539825426)) (.branch 36 (.leaf 2484874814) (.leaf 2431516815)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2379690064) (.leaf 2329336076)) (.branch 40 (.leaf 2280399094) (.leaf 2232825940))) (.branch 43 (.branch 42 (.leaf 2186565882) (.leaf 2141570503)) (.branch 44 (.leaf 2097793579) (.leaf 2055190966))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2013720494) (.branch 47 (.leaf 1973341865) (.leaf 1934016554))) (.branch 50 (.branch 49 (.leaf 1895707727) (.leaf 1858380148)) (.branch 51 (.leaf 1822000105) (.leaf 1786535331)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1751954934) (.leaf 1718229330)) (.branch 55 (.leaf 1685330176) (.leaf 1653230316))) (.branch 58 (.branch 57 (.leaf 1621903716) (.leaf 1591325417)) (.branch 59 (.leaf 1561471480) (.leaf 1532318939))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1503845751) (.branch 62 (.leaf 1476030762) (.leaf 1448853656))) (.branch 65 (.branch 64 (.leaf 1422294920) (.leaf 1396335807)) (.branch 66 (.leaf 1370958302) (.leaf 1346145085)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1321879501) (.leaf 1298145534)) (.branch 70 (.leaf 1274927769) (.leaf 1252211376))) (.branch 73 (.branch 72 (.leaf 1229982075) (.leaf 1208226116)) (.branch 74 (.leaf 1186930256) (.leaf 1166081734))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1145668253) (.branch 77 (.leaf 1125677957) (.leaf 1106099414))) (.branch 80 (.branch 79 (.leaf 1086921597) (.leaf 1068133867)) (.branch 81 (.leaf 1049725955) (.leaf 1031687950)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1014010281) (.leaf 996683700)) (.branch 85 (.leaf 979699277) (.leaf 963048379))) (.branch 88 (.branch 87 (.leaf 946722659) (.leaf 930714050)) (.branch 89 (.leaf 915014746) (.leaf 899617195)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 884514090) (.branch 92 (.leaf 869698358) (.leaf 855163149))) (.branch 95 (.branch 94 (.leaf 840901830) (.leaf 826907973)) (.branch 96 (.leaf 813175352) (.leaf 799697929)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 786469854) (.leaf 773485450)) (.branch 100 (.leaf 760739211) (.leaf 748225797))) (.branch 103 (.branch 102 (.leaf 735940022) (.leaf 723876854)) (.branch 104 (.leaf 712031405) (.leaf 700398929))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 688974816) (.leaf 677754584)) (.branch 108 (.leaf 666733878) (.leaf 655908464))) (.branch 111 (.branch 110 (.leaf 645274224) (.leaf 634827155)) (.branch 112 (.leaf 624563360) (.leaf 614479049)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 604570530) (.leaf 594834212)) (.branch 116 (.leaf 585266596) (.leaf 575864277))) (.branch 119 (.branch 118 (.leaf 566623934) (.leaf 557542335)) (.branch 120 (.leaf 548616327) (.leaf 539842838)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 491).prefactor = (583991030703803/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 491).cutoff/(generalMeanRows 491).c)).2 =
    (15501663676771/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 491).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 491).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 491).q*(generalMeanRows 491).c/2-2 = (61/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable006.value]
    have hcontinuation : (generalMeanRows 491).q*(generalMeanRows 491).cutoff/2-2 = (203/110:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable183.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 491).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 491

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 491).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 491).criticalRate j.val*(generalMeanRows 491).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 491).c*(generalMeanRows 491).criticalPoint j.val)).2-
      (generalMeanRows 491).J/2-(generalMeanRows 491).error (generalMeanGrid j.val)+
      (generalMeanRows 491).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 491).c)).2-
      (generalMeanRows 491).J/2-(generalMeanRows 491).error 4 := by
  have he : (generalMeanRows 491).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 491) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 491)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0491

/-! Kernel-checked entropy margins for general spectral rectangle 492. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0492
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5450915802) (.branch 2 (.leaf 5262543048) (.leaf 5082383209))) (.branch 5 (.branch 4 (.leaf 4909985988) (.leaf 4744932201)) (.branch 6 (.leaf 4586831047) (.leaf 4435317677)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4290051032) (.leaf 4150711894)) (.branch 10 (.leaf 4017001148) (.leaf 3888638207))) (.branch 13 (.branch 12 (.leaf 3765359596) (.leaf 3646917666)) (.branch 14 (.leaf 3533079431) (.leaf 3423625507))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3318349147) (.branch 17 (.leaf 3217055359) (.leaf 3119560100))) (.branch 20 (.branch 19 (.leaf 3025689536) (.leaf 2935279363)) (.branch 21 (.leaf 2848174183) (.leaf 2764226929)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2683298334) (.leaf 2605256444)) (.branch 25 (.leaf 2529976159) (.leaf 2457338818))) (.branch 28 (.branch 27 (.leaf 2387231809) (.leaf 2319548206)) (.branch 29 (.leaf 2254186432) (.leaf 2191049951)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2130046971) (.branch 32 (.leaf 2071090176) (.leaf 2014096474))) (.branch 35 (.branch 34 (.leaf 1958986756) (.leaf 1905685676)) (.branch 36 (.leaf 1854121448) (.leaf 1804225645)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1755933023) (.leaf 1709181350)) (.branch 40 (.leaf 1663911243) (.leaf 1620066018))) (.branch 43 (.branch 42 (.leaf 1577591554) (.leaf 1536436154)) (.branch 44 (.leaf 1496550423) (.leaf 1457887151))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1420401200) (.branch 47 (.leaf 1384049402) (.leaf 1348790459))) (.branch 50 (.branch 49 (.leaf 1314584851) (.leaf 1281394747)) (.branch 51 (.leaf 1249183923) (.leaf 1217917686)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1187562795) (.leaf 1158087397)) (.branch 55 (.leaf 1129460954) (.leaf 1101654188))) (.branch 58 (.branch 57 (.leaf 1074639016) (.leaf 1048388496)) (.branch 59 (.leaf 1022876775) (.leaf 998079036))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 973971451) (.branch 62 (.leaf 950531138) (.leaf 927736114))) (.branch 65 (.branch 64 (.leaf 905565257) (.leaf 883998269)) (.branch 66 (.leaf 863015633) (.leaf 842598584)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 822729074) (.leaf 803389737)) (.branch 70 (.leaf 784563867) (.leaf 766235379))) (.branch 73 (.branch 72 (.leaf 748388791) (.leaf 731009194)) (.branch 74 (.leaf 714082227) (.leaf 697594055))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 681531344) (.branch 77 (.leaf 665881247) (.leaf 650631373))) (.branch 80 (.branch 79 (.leaf 635769777) (.leaf 621284936)) (.branch 81 (.leaf 607165736) (.leaf 593401451)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 579981728) (.leaf 566896575)) (.branch 85 (.leaf 554136343) (.leaf 541691713))) (.branch 88 (.branch 87 (.leaf 529553683) (.leaf 517713556)) (.branch 89 (.leaf 506162928) (.leaf 494893675)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 483897942) (.branch 92 (.leaf 473168135) (.leaf 462696909))) (.branch 95 (.branch 94 (.leaf 452477158) (.leaf 442502007)) (.branch 96 (.leaf 432764803) (.leaf 423259105)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 413978679) (.leaf 404917488)) (.branch 100 (.leaf 396069684) (.leaf 387429603))) (.branch 103 (.branch 102 (.leaf 378991758) (.leaf 370750832)) (.branch 104 (.leaf 362701669) (.leaf 354839274))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 347158802) (.leaf 339655557)) (.branch 108 (.leaf 332324980) (.leaf 325162653))) (.branch 111 (.branch 110 (.leaf 318164287) (.leaf 311325721)) (.branch 112 (.leaf 304642914) (.leaf 298111947)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 291729012) (.leaf 285490413)) (.branch 116 (.leaf 279392560) (.leaf 273431965))) (.branch 119 (.branch 118 (.leaf 267605241) (.leaf 261909095)) (.branch 120 (.leaf 256340328) (.leaf 250895831)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 492).prefactor = (1209123154356143/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 492).cutoff/(generalMeanRows 492).c)).2 =
    (156409022861669/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 492).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 492).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 492).q*(generalMeanRows 492).c/2-2 = (13/16:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable042.value]
    have hcontinuation : (generalMeanRows 492).q*(generalMeanRows 492).cutoff/2-2 = (203/110:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable183.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 492).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 492

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 492).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 492).criticalRate j.val*(generalMeanRows 492).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 492).c*(generalMeanRows 492).criticalPoint j.val)).2-
      (generalMeanRows 492).J/2-(generalMeanRows 492).error (generalMeanGrid j.val)+
      (generalMeanRows 492).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 492).c)).2-
      (generalMeanRows 492).J/2-(generalMeanRows 492).error 4 := by
  have he : (generalMeanRows 492).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 492) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 492)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0492

/-! Kernel-checked entropy margins for general spectral rectangle 493. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0493
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5293387489) (.branch 2 (.leaf 5112960344) (.leaf 4940437115))) (.branch 5 (.branch 4 (.leaf 4775379538) (.leaf 4617379810)) (.branch 6 (.leaf 4466057922) (.leaf 4321059282)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4182052602) (.leaf 4048727988)) (.branch 10 (.leaf 3920795241) (.leaf 3797982309))) (.branch 13 (.branch 12 (.leaf 3680033899) (.leaf 3566710218)) (.branch 14 (.leaf 3457785829) (.leaf 3353048607))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3252298795) (.branch 17 (.leaf 3155348134) (.leaf 3062019068))) (.branch 20 (.branch 19 (.leaf 2972144025) (.leaf 2885564738)) (.branch 21 (.leaf 2802131641) (.leaf 2721703296)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2644145876) (.leaf 2569332679)) (.branch 25 (.leaf 2497143686) (.leaf 2427465142))) (.branch 28 (.branch 27 (.leaf 2360189181) (.leaf 2295213464)) (.branch 29 (.leaf 2232440851) (.leaf 2171779094)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2113140549) (.branch 32 (.leaf 2056441913) (.leaf 2001603970))) (.branch 35 (.branch 34 (.leaf 1948551362) (.leaf 1897212372)) (.branch 36 (.leaf 1847518718) (.leaf 1799405367)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1752810354) (.leaf 1707674614)) (.branch 40 (.leaf 1663941828) (.leaf 1621558278))) (.branch 43 (.branch 42 (.leaf 1580472702) (.leaf 1540636171)) (.branch 44 (.leaf 1502001965) (.leaf 1464525456))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1428164003) (.branch 47 (.leaf 1392876850) (.leaf 1358625027))) (.branch 50 (.branch 49 (.leaf 1325371264) (.leaf 1293079903)) (.branch 51 (.leaf 1261716819) (.leaf 1231249343)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1201646190) (.leaf 1172877393)) (.branch 55 (.leaf 1144914237) (.leaf 1117729202))) (.branch 58 (.branch 57 (.leaf 1091295901) (.leaf 1065589029)) (.branch 59 (.leaf 1040584309) (.leaf 1016258447))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 992589085) (.branch 62 (.leaf 969554755) (.leaf 947134840))) (.branch 65 (.branch 64 (.leaf 925309533) (.leaf 904059802)) (.branch 66 (.leaf 883367355) (.leaf 863214603)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 843584632) (.leaf 824461171)) (.branch 70 (.leaf 805828564) (.leaf 787671741))) (.branch 73 (.branch 72 (.leaf 769976195) (.leaf 752727957)) (.branch 74 (.leaf 735913571) (.leaf 719520071))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 703534963) (.branch 77 (.leaf 687946203) (.leaf 672742178))) (.branch 80 (.branch 79 (.leaf 657911687) (.leaf 643443925)) (.branch 81 (.leaf 629328468) (.leaf 615555251)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 602114561) (.leaf 588997016)) (.branch 85 (.leaf 576193556) (.leaf 563695429))) (.branch 88 (.branch 87 (.leaf 551494175) (.leaf 539581618)) (.branch 89 (.leaf 527949856) (.leaf 516591245)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 505498392) (.branch 92 (.leaf 494664145) (.leaf 484081585))) (.branch 95 (.branch 94 (.leaf 473744014) (.leaf 463644947)) (.branch 96 (.leaf 453778105) (.leaf 444137409)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 434716967) (.leaf 425511073)) (.branch 100 (.leaf 416514196) (.leaf 407720974))) (.branch 103 (.branch 102 (.leaf 399126210) (.leaf 390724863)) (.branch 104 (.leaf 382512046) (.leaf 374483016))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 366633173) (.leaf 358958050)) (.branch 108 (.leaf 351453314) (.leaf 344114758))) (.branch 111 (.branch 110 (.leaf 336938295) (.leaf 329919957)) (.branch 112 (.leaf 323055892) (.leaf 316342354)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 309775704) (.leaf 303352408)) (.branch 116 (.leaf 297069027) (.leaf 290922221))) (.branch 119 (.branch 118 (.leaf 284908741) (.leaf 279025425)) (.branch 120 (.leaf 273269203) (.leaf 267637083)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 493).prefactor = (4723505828352781/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 493).cutoff/(generalMeanRows 493).c)).2 =
    (67553338217461/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 493).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 493).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 493).q*(generalMeanRows 493).c/2-2 = (397/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable105.value]
    have hcontinuation : (generalMeanRows 493).q*(generalMeanRows 493).cutoff/2-2 = (23/12:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable028.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 493).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 493

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 493).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 493).criticalRate j.val*(generalMeanRows 493).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 493).c*(generalMeanRows 493).criticalPoint j.val)).2-
      (generalMeanRows 493).J/2-(generalMeanRows 493).error (generalMeanGrid j.val)+
      (generalMeanRows 493).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 493).c)).2-
      (generalMeanRows 493).J/2-(generalMeanRows 493).error 4 := by
  have he : (generalMeanRows 493).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 493) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 493)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0493

/-! Kernel-checked entropy margins for general spectral rectangle 494. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0494
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5188359274) (.branch 2 (.leaf 5015892087) (.leaf 4850995101))) (.branch 5 (.branch 4 (.leaf 4693243140) (.leaf 4542240810)) (.branch 6 (.leaf 4397619897) (.leaf 4259037052)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4126171708) (.leaf 3998724228)) (.branch 10 (.leaf 3876414229) (.leaf 3758979070))) (.branch 13 (.branch 12 (.leaf 3646172493) (.leaf 3537763384)) (.branch 14 (.leaf 3433534650) (.leaf 3333282199))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3236814008) (.branch 17 (.leaf 3143949270) (.leaf 3054517617))) (.branch 20 (.branch 19 (.leaf 2968358403) (.leaf 2885320051)) (.branch 21 (.leaf 2805259446) (.leaf 2728041381)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2653538044) (.leaf 2581628545)) (.branch 25 (.leaf 2512198474) (.leaf 2445139501))) (.branch 28 (.branch 27 (.leaf 2380348996) (.leaf 2317729680)) (.branch 29 (.leaf 2257189303) (.leaf 2198640341)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2141999716) (.branch 32 (.leaf 2087188534) (.leaf 2034131840))) (.branch 35 (.branch 34 (.leaf 1982758394) (.leaf 1933000454)) (.branch 36 (.leaf 1884793581) (.leaf 1838076452)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1792790686) (.leaf 1748880679)) (.branch 40 (.leaf 1706293455) (.leaf 1664978521))) (.branch 43 (.branch 42 (.leaf 1624887734) (.leaf 1585975170)) (.branch 44 (.leaf 1548197012) (.leaf 1511511435))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1475878500) (.branch 47 (.leaf 1441260060) (.leaf 1407619662))) (.branch 50 (.branch 49 (.leaf 1374922464) (.leaf 1343135147)) (.branch 51 (.leaf 1312225846) (.leaf 1282164067)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1252920625) (.leaf 1224467576)) (.branch 55 (.leaf 1196778155) (.leaf 1169826719))) (.branch 58 (.branch 57 (.leaf 1143588693) (.leaf 1118040515)) (.branch 59 (.leaf 1093159589) (.leaf 1068924239))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1045313663) (.branch 62 (.leaf 1022307894) (.leaf 999887758))) (.branch 65 (.branch 64 (.leaf 978034839) (.leaf 956731441)) (.branch 66 (.leaf 935960559) (.leaf 915705842)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 895951566) (.leaf 876682605)) (.branch 70 (.leaf 857884403) (.leaf 839542949))) (.branch 73 (.branch 72 (.leaf 821644754) (.leaf 804176824)) (.branch 74 (.leaf 787126644) (.leaf 770482149))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 754231712) (.branch 77 (.leaf 738364121) (.leaf 722868561))) (.branch 80 (.branch 79 (.leaf 707734600) (.leaf 692952166)) (.branch 81 (.leaf 678511542) (.leaf 664403341)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 650618498) (.leaf 637148255)) (.branch 85 (.leaf 623984149) (.leaf 611117999))) (.branch 88 (.branch 87 (.leaf 598541893) (.leaf 586248183)) (.branch 89 (.leaf 574229465) (.leaf 562478580)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 550988595) (.branch 92 (.leaf 539752799) (.leaf 528764694))) (.branch 95 (.branch 94 (.leaf 518017984) (.leaf 507506573)) (.branch 96 (.leaf 497224548) (.leaf 487166183)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 477325921) (.leaf 467698378)) (.branch 100 (.leaf 458278327) (.leaf 449060701))) (.branch 103 (.branch 102 (.leaf 440040581) (.leaf 431213190)) (.branch 104 (.leaf 422573895) (.leaf 414118193))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 405841713) (.leaf 397740207)) (.branch 108 (.leaf 389809548) (.leaf 382045727))) (.branch 111 (.branch 110 (.leaf 374444844) (.leaf 367003108)) (.branch 112 (.leaf 359716835) (.leaf 352582439)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 345596433) (.leaf 338755423)) (.branch 116 (.leaf 332056108) (.leaf 325495275))) (.branch 119 (.branch 118 (.leaf 319069793) (.leaf 312776619)) (.branch 120 (.leaf 306612784) (.leaf 300575400)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 494).prefactor = (575363324326491/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 494).cutoff/(generalMeanRows 494).c)).2 =
    (73716897525883/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 494).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 494).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 494).q*(generalMeanRows 494).c/2-2 = (3051/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable153.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 494).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 494

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 494).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 494).criticalRate j.val*(generalMeanRows 494).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 494).c*(generalMeanRows 494).criticalPoint j.val)).2-
      (generalMeanRows 494).J/2-(generalMeanRows 494).error (generalMeanGrid j.val)+
      (generalMeanRows 494).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 494).c)).2-
      (generalMeanRows 494).J/2-(generalMeanRows 494).error 4 := by
  have he : (generalMeanRows 494).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 494) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 494)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0494

/-! Kernel-checked entropy margins for general spectral rectangle 495. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0495
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5289388681) (.branch 2 (.leaf 5118390151) (.leaf 4954906622))) (.branch 5 (.branch 4 (.leaf 4798511335) (.leaf 4648807621)) (.branch 6 (.leaf 4505426276) (.leaf 4368023215)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4236277378) (.leaf 4109888844)) (.branch 10 (.leaf 3988577140) (.leaf 3872079716))) (.branch 13 (.branch 12 (.leaf 3760150560) (.leaf 3652558949)) (.branch 14 (.leaf 3549088310) (.leaf 3449535187))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3353708293) (.branch 17 (.leaf 3261427651) (.leaf 3172523803))) (.branch 20 (.branch 19 (.leaf 3086837082) (.leaf 3004216953)) (.branch 21 (.leaf 2924521396) (.leaf 2847616345)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2773375168) (.leaf 2701678183)) (.branch 25 (.leaf 2632412222) (.leaf 2565470209))) (.branch 28 (.branch 27 (.leaf 2500750790) (.leaf 2438157971)) (.branch 29 (.leaf 2377600795) (.leaf 2318993034)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2262252905) (.branch 32 (.leaf 2207302808) (.leaf 2154069075))) (.branch 35 (.branch 34 (.leaf 2102481744) (.leaf 2052474343)) (.branch 36 (.leaf 2003983689) (.leaf 1956949700)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1911315220) (.leaf 1867025855)) (.branch 40 (.leaf 1824029819) (.leaf 1782277789))) (.branch 43 (.branch 42 (.leaf 1741722771) (.leaf 1702319970)) (.branch 44 (.leaf 1664026675) (.leaf 1626802146))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1590607504) (.branch 47 (.leaf 1555405639) (.leaf 1521161112))) (.branch 50 (.branch 49 (.leaf 1487840071) (.leaf 1455410163)) (.branch 51 (.leaf 1423840463) (.leaf 1393101396)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1363164670) (.leaf 1334003210)) (.branch 55 (.leaf 1305591097) (.leaf 1277903511))) (.branch 58 (.branch 57 (.leaf 1250916673) (.leaf 1224607798)) (.branch 59 (.leaf 1198955043) (.leaf 1173937460))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1149534956) (.branch 62 (.leaf 1125728248) (.leaf 1102498827))) (.branch 65 (.branch 64 (.leaf 1079828919) (.leaf 1057701451)) (.branch 66 (.leaf 1036100018) (.leaf 1015008850)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 994412786) (.leaf 974297241)) (.branch 70 (.leaf 954648183) (.leaf 935452106))) (.branch 73 (.branch 72 (.leaf 916696009) (.leaf 898367367)) (.branch 74 (.leaf 880454116) (.leaf 862944629))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 845827697) (.branch 77 (.leaf 829092513) (.leaf 812728648))) (.branch 80 (.branch 79 (.leaf 796726043) (.leaf 781074987)) (.branch 81 (.leaf 765766104) (.leaf 750790338)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 736138942) (.leaf 721803461)) (.branch 85 (.leaf 707775722) (.leaf 694047822))) (.branch 88 (.branch 87 (.leaf 680612118) (.leaf 667461214)) (.branch 89 (.leaf 654587953) (.leaf 641985405)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 629646860) (.branch 92 (.leaf 617565821) (.leaf 605735988))) (.branch 95 (.branch 94 (.leaf 594151262) (.leaf 582805724)) (.branch 96 (.leaf 571693639) (.leaf 560809443)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 550147739) (.leaf 539703288)) (.branch 100 (.leaf 529471005) (.leaf 519445956))) (.branch 103 (.branch 102 (.leaf 509623345) (.leaf 499998516)) (.branch 104 (.leaf 490566945) (.leaf 481324235))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 472266112) (.leaf 463388421)) (.branch 108 (.leaf 454687122) (.leaf 446158282))) (.branch 111 (.branch 110 (.leaf 437798079) (.leaf 429602791)) (.branch 112 (.leaf 421568797) (.leaf 413692569)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 405970676) (.leaf 398399774)) (.branch 116 (.leaf 390976605) (.leaf 383697997))) (.branch 119 (.branch 118 (.leaf 376560857) (.leaf 369562173)) (.branch 120 (.leaf 362699007) (.leaf 355968494)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 495).prefactor = (2300093559175257/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 495).cutoff/(generalMeanRows 495).c)).2 =
    (197849889810369/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 495).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 495).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 495).q*(generalMeanRows 495).c/2-2 = (2879/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable152.value]
    have hcontinuation : (generalMeanRows 495).q*(generalMeanRows 495).cutoff/2-2 = (4082/2001:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable184.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 495).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 495

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 495).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 495).criticalRate j.val*(generalMeanRows 495).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 495).c*(generalMeanRows 495).criticalPoint j.val)).2-
      (generalMeanRows 495).J/2-(generalMeanRows 495).error (generalMeanGrid j.val)+
      (generalMeanRows 495).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 495).c)).2-
      (generalMeanRows 495).J/2-(generalMeanRows 495).error 4 := by
  have he : (generalMeanRows 495).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 495) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 495)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0495

/-! Kernel-checked entropy margins for general spectral rectangle 496. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0496
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5018310668) (.branch 2 (.leaf 4846453557) (.leaf 4682256620))) (.branch 5 (.branch 4 (.leaf 4525286331) (.leaf 4375139621)) (.branch 6 (.leaf 4231441228) (.leaf 4093841316)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3962013363) (.leaf 3835652254)) (.branch 10 (.leaf 3714472568) (.leaf 3598207037))) (.branch 13 (.branch 12 (.leaf 3486605147) (.leaf 3379431873)) (.branch 14 (.leaf 3276466527) (.leaf 3177501714))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3082342377) (.branch 17 (.leaf 2990804922) (.leaf 2902716422))) (.branch 20 (.branch 19 (.leaf 2817913881) (.leaf 2736243567)) (.branch 21 (.leaf 2657560386) (.leaf 2581727318)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2508614889) (.leaf 2438100685)) (.branch 25 (.leaf 2370068902) (.leaf 2304409934))) (.branch 28 (.branch 27 (.leaf 2241019983) (.leaf 2179800704)) (.branch 29 (.leaf 2120658872) (.leaf 2063506074)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2008258421) (.branch 32 (.leaf 1954836280) (.leaf 1903164025))) (.branch 35 (.branch 34 (.leaf 1853169803) (.leaf 1804785319)) (.branch 36 (.leaf 1757945630) (.leaf 1712588957)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1668656507) (.leaf 1626092305)) (.branch 40 (.leaf 1584843040) (.leaf 1544857918))) (.branch 43 (.branch 42 (.leaf 1506088524) (.leaf 1468488696)) (.branch 44 (.leaf 1432014400) (.leaf 1396623620))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1362276248) (.branch 47 (.leaf 1328933986) (.leaf 1296560254))) (.branch 50 (.branch 49 (.leaf 1265120092) (.leaf 1234580086)) (.branch 51 (.leaf 1204908285) (.leaf 1176074124)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1148048359) (.leaf 1120802995)) (.branch 55 (.leaf 1094311231) (.leaf 1068547393))) (.branch 58 (.branch 57 (.leaf 1043486882) (.leaf 1019106123)) (.branch 59 (.leaf 995382513) (.leaf 972294373))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 949820906) (.branch 62 (.leaf 927942152) (.leaf 906638953))) (.branch 65 (.branch 64 (.leaf 885892910) (.leaf 865686349)) (.branch 66 (.leaf 846002289) (.leaf 826824407)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 808137010) (.leaf 789925006)) (.branch 70 (.leaf 772173875) (.leaf 754869644))) (.branch 73 (.branch 72 (.leaf 737998862) (.leaf 721548579)) (.branch 74 (.leaf 705506321) (.leaf 689860068))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 674598238) (.branch 77 (.leaf 659709667) (.leaf 645183587))) (.branch 80 (.branch 79 (.leaf 631009613) (.leaf 617177725)) (.branch 81 (.leaf 603678255) (.leaf 590501867)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 577639547) (.leaf 565082591)) (.branch 85 (.leaf 552822585) (.leaf 540851403))) (.branch 88 (.branch 87 (.leaf 529161188) (.leaf 517744342)) (.branch 89 (.leaf 506593518) (.leaf 495701610)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 485061740) (.branch 92 (.leaf 474667253) (.leaf 464511704))) (.branch 95 (.branch 94 (.leaf 454588855) (.leaf 444892662)) (.branch 96 (.leaf 435417271) (.leaf 426157009)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 417106379) (.leaf 408260049)) (.branch 100 (.leaf 399612852) (.leaf 391159775))) (.branch 103 (.branch 102 (.leaf 382895955) (.leaf 374816675)) (.branch 104 (.leaf 366917356) (.leaf 359193553))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 351640952) (.leaf 344255362)) (.branch 108 (.leaf 337032714) (.leaf 329969054))) (.branch 111 (.branch 110 (.leaf 323060541) (.leaf 316303442)) (.branch 112 (.leaf 309694129) (.leaf 303229073)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 296904847) (.leaf 290718113)) (.branch 116 (.leaf 284665628) (.leaf 278744236))) (.branch 119 (.branch 118 (.leaf 272950865) (.leaf 267282527)) (.branch 120 (.leaf 261736314) (.leaf 256309394)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 496).prefactor = (4667567841579483/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 496).cutoff/(generalMeanRows 496).c)).2 =
    (91142215256391/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 496).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 496).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 496).q*(generalMeanRows 496).c/2-2 = (3223/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable132.value]
    have hcontinuation : (generalMeanRows 496).q*(generalMeanRows 496).cutoff/2-2 = (4082/2001:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable184.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 496).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 496

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 496).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 496).criticalRate j.val*(generalMeanRows 496).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 496).c*(generalMeanRows 496).criticalPoint j.val)).2-
      (generalMeanRows 496).J/2-(generalMeanRows 496).error (generalMeanGrid j.val)+
      (generalMeanRows 496).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 496).c)).2-
      (generalMeanRows 496).J/2-(generalMeanRows 496).error 4 := by
  have he : (generalMeanRows 496).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 496) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 496)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0496

/-! Kernel-checked entropy margins for general spectral rectangle 497. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0497
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5384044737) (.branch 2 (.leaf 5214776186) (.leaf 5052876879))) (.branch 5 (.branch 4 (.leaf 4897928738) (.leaf 4749543182)) (.branch 6 (.leaf 4607358544) (.leaf 4471037779)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4340266402) (.leaf 4214750647)) (.branch 10 (.leaf 4094215806) (.leaf 3978404731))) (.branch 13 (.branch 12 (.leaf 3867076480) (.leaf 3760005091)) (.branch 14 (.leaf 3656978468) (.leaf 3557797362))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3462274453) (.branch 17 (.leaf 3370233495) (.leaf 3281508550))) (.branch 20 (.branch 19 (.leaf 3195943273) (.leaf 3113390263)) (.branch 21 (.leaf 3033710460) (.leaf 2956772596)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2882452685) (.leaf 2810633550)) (.branch 25 (.leaf 2741204391) (.leaf 2674060379))) (.branch 28 (.branch 27 (.leaf 2609102285) (.leaf 2546236133)) (.branch 29 (.leaf 2485372878) (.leaf 2426428108)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2369321763) (.branch 32 (.leaf 2313977879) (.leaf 2260324343))) (.branch 35 (.branch 34 (.leaf 2208292672) (.leaf 2157817798)) (.branch 36 (.leaf 2108837874) (.leaf 2061294090)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2015130502) (.leaf 1970293867)) (.branch 40 (.leaf 1926733496) (.leaf 1884401112))) (.branch 43 (.branch 42 (.leaf 1843250717) (.leaf 1803238468)) (.branch 44 (.leaf 1764322557) (.leaf 1726463108))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1689622066) (.branch 47 (.leaf 1653763108) (.leaf 1618851544))) (.branch 50 (.branch 49 (.leaf 1584854237) (.leaf 1551739520)) (.branch 51 (.leaf 1519477118) (.leaf 1488038080)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1457394711) (.leaf 1427520502)) (.branch 55 (.leaf 1398390079) (.leaf 1369979139))) (.branch 58 (.branch 57 (.leaf 1342264402) (.leaf 1315223555)) (.branch 59 (.leaf 1288835207) (.leaf 1263078845))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1237934788) (.branch 62 (.leaf 1213384150) (.leaf 1189408799))) (.branch 65 (.branch 64 (.leaf 1165991323) (.leaf 1143114994)) (.branch 66 (.leaf 1120763736) (.leaf 1098922096)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1077575213) (.leaf 1056708791)) (.branch 70 (.leaf 1036309072) (.leaf 1016362815))) (.branch 73 (.branch 72 (.leaf 996857267) (.leaf 977780145)) (.branch 74 (.leaf 959119613) (.leaf 940864263))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 923003094) (.branch 77 (.leaf 905525497) (.leaf 888421235))) (.branch 80 (.branch 79 (.leaf 871680428) (.leaf 855293539)) (.branch 81 (.leaf 839251355) (.leaf 823544978)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 808165808) (.leaf 793105533)) (.branch 85 (.leaf 778356115) (.leaf 763909779))) (.branch 88 (.branch 87 (.leaf 749759003) (.leaf 735896507)) (.branch 89 (.leaf 722315243) (.leaf 709008386)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 695969326) (.branch 92 (.leaf 683191655) (.leaf 670669165))) (.branch 95 (.branch 94 (.leaf 658395836) (.leaf 646365832)) (.branch 96 (.leaf 634573490) (.leaf 623013315)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 611679974) (.leaf 600568292)) (.branch 100 (.leaf 589673242) (.leaf 578989939))) (.branch 103 (.branch 102 (.leaf 568513641) (.leaf 558239738)) (.branch 104 (.leaf 548163748) (.leaf 538281315))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 528588201) (.leaf 519080286)) (.branch 108 (.leaf 509753558) (.leaf 500604116))) (.branch 111 (.branch 110 (.leaf 491628161) (.leaf 482821994)) (.branch 112 (.leaf 474182015) (.leaf 465704715)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 457386677) (.leaf 449224570)) (.branch 116 (.leaf 441215150) (.leaf 433355252))) (.branch 119 (.branch 118 (.leaf 425641792) (.leaf 418071762)) (.branch 120 (.leaf 410642228) (.leaf 403350327)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 497).prefactor = (4540320064896447/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 497).cutoff/(generalMeanRows 497).c)).2 =
    (406249990515891/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 497).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 497).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 497).q*(generalMeanRows 497).c/2-2 = (1101/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable185.value]
    have hcontinuation : (generalMeanRows 497).q*(generalMeanRows 497).cutoff/2-2 = (403/198:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable186.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 497).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 497

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 497).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 497).criticalRate j.val*(generalMeanRows 497).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 497).c*(generalMeanRows 497).criticalPoint j.val)).2-
      (generalMeanRows 497).J/2-(generalMeanRows 497).error (generalMeanGrid j.val)+
      (generalMeanRows 497).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 497).c)).2-
      (generalMeanRows 497).J/2-(generalMeanRows 497).error 4 := by
  have he : (generalMeanRows 497).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 497) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 497)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0497

/-! Kernel-checked entropy margins for general spectral rectangle 498. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0498
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5107588769) (.branch 2 (.leaf 4937223163) (.leaf 4774373284))) (.branch 5 (.branch 4 (.leaf 4618614518) (.leaf 4469552100)) (.branch 6 (.leaf 4326818505) (.leaf 4190071124)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4058990186) (.leaf 3933276890)) (.branch 10 (.leaf 3812651729) (.leaf 3696852979))) (.branch 13 (.branch 12 (.leaf 3585635322) (.leaf 3478768614)) (.branch 14 (.leaf 3376036754) (.leaf 3277236657))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3182177322) (.branch 17 (.leaf 3090678974) (.leaf 3002572283))) (.branch 20 (.branch 19 (.leaf 2917697646) (.leaf 2835904526)) (.branch 21 (.leaf 2757050850) (.leaf 2681002448)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2607632535) (.leaf 2536821242)) (.branch 25 (.leaf 2468455172) (.leaf 2402426991))) (.branch 28 (.branch 27 (.leaf 2338635055) (.leaf 2276983057)) (.branch 29 (.leaf 2217379701) (.leaf 2159738403)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2103977003) (.branch 32 (.leaf 2050017512) (.leaf 1997785860))) (.branch 35 (.branch 34 (.leaf 1947211670) (.leaf 1898228048)) (.branch 36 (.leaf 1850771378) (.leaf 1804781144)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1760199749) (.leaf 1716972354)) (.branch 40 (.leaf 1675046729) (.leaf 1634373104))) (.branch 43 (.branch 42 (.leaf 1594904039) (.leaf 1556594294)) (.branch 44 (.leaf 1519400716) (.leaf 1483282124))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1448199204) (.branch 47 (.leaf 1414114413) (.leaf 1380991885))) (.branch 50 (.branch 49 (.leaf 1348797344) (.leaf 1317498023)) (.branch 51 (.leaf 1287062585) (.leaf 1257461051)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1228664733) (.leaf 1200646165)) (.branch 55 (.leaf 1173379047) (.leaf 1146838181))) (.branch 58 (.branch 57 (.leaf 1120999423) (.leaf 1095839628)) (.branch 59 (.leaf 1071336600) (.leaf 1047469050))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1024216548) (.branch 62 (.leaf 1001559486) (.leaf 979479036))) (.branch 65 (.branch 64 (.leaf 957957112) (.leaf 936976342)) (.branch 66 (.leaf 916520025) (.leaf 896572107)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 877117150) (.leaf 858140300)) (.branch 70 (.leaf 839627264) (.leaf 821564286))) (.branch 73 (.branch 72 (.leaf 803938118) (.leaf 786736000)) (.branch 74 (.leaf 769945638) (.leaf 753555186))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 737553221) (.branch 77 (.leaf 721928730) (.leaf 706671087))) (.branch 80 (.branch 79 (.leaf 691770041) (.leaf 677215698)) (.branch 81 (.leaf 662998506) (.leaf 649109239)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 635538986) (.leaf 622279138)) (.branch 85 (.leaf 609321372) (.leaf 596657641))) (.branch 88 (.branch 87 (.leaf 584280167) (.leaf 572181422)) (.branch 89 (.leaf 560354125) (.leaf 548791228)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 537485909) (.branch 92 (.leaf 526431561) (.leaf 515621787))) (.branch 95 (.branch 94 (.leaf 505050387) (.leaf 494711355)) (.branch 96 (.leaf 484598868) (.leaf 474707283)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 465031125) (.leaf 455565085)) (.branch 100 (.leaf 446304013) (.leaf 437242910))) (.branch 103 (.branch 102 (.leaf 428376924) (.leaf 419701347)) (.branch 104 (.leaf 411211604) (.leaf 402903253))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 394771980) (.leaf 386813592)) (.branch 108 (.leaf 379024014) (.leaf 371399285))) (.branch 111 (.branch 110 (.leaf 363935556) (.leaf 356629080)) (.branch 112 (.leaf 349476217) (.leaf 342473423)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 335617253) (.leaf 328904350)) (.branch 116 (.leaf 322331452) (.leaf 315895379))) (.branch 119 (.branch 118 (.leaf 309593037) (.leaf 303421413)) (.branch 120 (.leaf 297377571) (.leaf 291458655)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 498).prefactor = (4606754062629121/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 498).cutoff/(generalMeanRows 498).c)).2 =
    (187559535960359/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 498).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 498).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 498).q*(generalMeanRows 498).c/2-2 = (1237/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable167.value]
    have hcontinuation : (generalMeanRows 498).q*(generalMeanRows 498).cutoff/2-2 = (403/198:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable186.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 498).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 498

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 498).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 498).criticalRate j.val*(generalMeanRows 498).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 498).c*(generalMeanRows 498).criticalPoint j.val)).2-
      (generalMeanRows 498).J/2-(generalMeanRows 498).error (generalMeanGrid j.val)+
      (generalMeanRows 498).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 498).c)).2-
      (generalMeanRows 498).J/2-(generalMeanRows 498).error 4 := by
  have he : (generalMeanRows 498).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 498) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 498)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0498

/-! Kernel-checked entropy margins for general spectral rectangle 499. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0499
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5118049295) (.branch 2 (.leaf 4949592462) (.leaf 4788597853))) (.branch 5 (.branch 4 (.leaf 4634639645) (.leaf 4487322132)) (.branch 6 (.leaf 4346277085) (.leaf 4211161419)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4081655081) (.leaf 3957459178)) (.branch 10 (.leaf 3838294272) (.leaf 3723898857))) (.branch 13 (.branch 12 (.leaf 3614027968) (.leaf 3508451934)) (.branch 14 (.leaf 3406955234) (.leaf 3309335459))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3215402366) (.branch 17 (.leaf 3124977014) (.leaf 3037890971))) (.branch 20 (.branch 19 (.leaf 2953985589) (.leaf 2873111334)) (.branch 21 (.leaf 2795127176) (.leaf 2719900022)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2647304195) (.leaf 2577220956)) (.branch 25 (.leaf 2509538051) (.leaf 2444149310))) (.branch 28 (.branch 27 (.leaf 2380954255) (.leaf 2319857754)) (.branch 29 (.leaf 2260769686) (.leaf 2203604640)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2148281629) (.branch 32 (.leaf 2094723823) (.leaf 2042858308))) (.branch 35 (.branch 34 (.leaf 1992615849) (.leaf 1943930682)) (.branch 36 (.leaf 1896740307) (.leaf 1850985308)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1806609169) (.leaf 1763558117)) (.branch 40 (.leaf 1721780967) (.leaf 1681228974))) (.branch 43 (.branch 42 (.leaf 1641855704) (.leaf 1603616902)) (.branch 44 (.leaf 1566470376) (.leaf 1530375887))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1495295040) (.branch 47 (.leaf 1461191188) (.leaf 1428029341))) (.branch 50 (.branch 49 (.leaf 1395776074) (.leaf 1364399450)) (.branch 51 (.leaf 1333868939) (.leaf 1304155348)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1275230752) (.leaf 1247068427)) (.branch 55 (.leaf 1219642792) (.leaf 1192929348))) (.branch 58 (.branch 57 (.leaf 1166904628) (.leaf 1141546145)) (.branch 59 (.leaf 1116832338) (.leaf 1092742535))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1069256903) (.branch 62 (.leaf 1046356411) (.leaf 1024022788))) (.branch 65 (.branch 64 (.leaf 1002238490) (.leaf 980986663)) (.branch 66 (.leaf 960251114) (.leaf 940016274)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 920267172) (.leaf 900989411)) (.branch 70 (.leaf 882169133) (.leaf 863793002))) (.branch 73 (.branch 72 (.leaf 845848176) (.leaf 828322287)) (.branch 74 (.leaf 811203419) (.leaf 794480085))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 778141212) (.branch 77 (.leaf 762176122) (.leaf 746574512))) (.branch 80 (.branch 79 (.leaf 731326440) (.leaf 716422311)) (.branch 81 (.leaf 701852856) (.leaf 687609126)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 673682473) (.leaf 660064538)) (.branch 85 (.leaf 646747242) (.leaf 633722770))) (.branch 88 (.branch 87 (.leaf 620983565) (.leaf 608522312)) (.branch 89 (.leaf 596331934) (.leaf 584405577)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 572736606) (.branch 92 (.leaf 561318590) (.leaf 550145303))) (.branch 95 (.branch 94 (.leaf 539210708) (.leaf 528508951)) (.branch 96 (.leaf 518034359) (.leaf 507781428)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 497744817) (.leaf 487919344)) (.branch 100 (.leaf 478299980) (.leaf 468881841))) (.branch 103 (.branch 102 (.leaf 459660186) (.leaf 450630407)) (.branch 104 (.leaf 441788030) (.leaf 433128706))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 424648207) (.leaf 416342424)) (.branch 108 (.leaf 408207360) (.leaf 400239129))) (.branch 111 (.branch 110 (.leaf 392433951) (.leaf 384788146)) (.branch 112 (.leaf 377298133) (.leaf 369960428)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 362771638) (.leaf 355728460)) (.branch 116 (.leaf 348827675) (.leaf 342066149))) (.branch 119 (.branch 118 (.leaf 335440829) (.leaf 328948738)) (.branch 120 (.leaf 322586978) (.leaf 316352721)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 499).prefactor = (4600978192214141/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 499).cutoff/(generalMeanRows 499).c)).2 =
    (49280014170937/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 499).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 499).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 499).q*(generalMeanRows 499).c/2-2 = (1203/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable135.value]
    have hcontinuation : (generalMeanRows 499).q*(generalMeanRows 499).cutoff/2-2 = (1630/783:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable187.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 499).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 499

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 499).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 499).criticalRate j.val*(generalMeanRows 499).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 499).c*(generalMeanRows 499).criticalPoint j.val)).2-
      (generalMeanRows 499).J/2-(generalMeanRows 499).error (generalMeanGrid j.val)+
      (generalMeanRows 499).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 499).c)).2-
      (generalMeanRows 499).J/2-(generalMeanRows 499).error 4 := by
  have he : (generalMeanRows 499).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 499) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 499)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0499

/-! Kernel-checked entropy margins for general spectral rectangle 500. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0500
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5257120816) (.branch 2 (.leaf 5089166386) (.leaf 4928630950))) (.branch 5 (.branch 4 (.leaf 4775088235) (.leaf 4628142249)) (.branch 6 (.leaf 4487424638) (.leaf 4352592326)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4223325399) (.leaf 4099325215)) (.branch 10 (.leaf 3980312690) (.leaf 3866026761))) (.branch 13 (.branch 12 (.leaf 3756222994) (.leaf 3650672316)) (.branch 14 (.leaf 3549159869) (.leaf 3451483967))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3357455136) (.branch 17 (.leaf 3266895250) (.leaf 3179636726))) (.branch 20 (.branch 19 (.leaf 3095521799) (.leaf 3014401843)) (.branch 21 (.leaf 2936136760) (.leaf 2860594403)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2787650059) (.leaf 2717185958)) (.branch 25 (.leaf 2649090829) (.leaf 2583259481))) (.branch 28 (.branch 27 (.leaf 2519592423) (.leaf 2457995505)) (.branch 29 (.leaf 2398379587) (.leaf 2340660232)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2284757422) (.branch 32 (.leaf 2230595286) (.leaf 2178101858))) (.branch 35 (.branch 34 (.leaf 2127208843) (.leaf 2077851402)) (.branch 36 (.leaf 2029967948) (.leaf 1983499960)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1938391808) (.leaf 1894590586)) (.branch 40 (.leaf 1852045959) (.leaf 1810710017))) (.branch 43 (.branch 42 (.leaf 1770537142) (.leaf 1731483881)) (.branch 44 (.leaf 1693508822) (.leaf 1656572491))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1620637238) (.branch 47 (.leaf 1585667147) (.leaf 1551627934))) (.branch 50 (.branch 49 (.leaf 1518486868) (.leaf 1486212685)) (.branch 51 (.leaf 1454775511) (.leaf 1424146791)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1394299218) (.leaf 1365206672)) (.branch 55 (.leaf 1336844155) (.leaf 1309187737))) (.branch 58 (.branch 57 (.leaf 1282214502) (.leaf 1255902494)) (.branch 59 (.leaf 1230230672) (.leaf 1205178863))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1180727719) (.branch 62 (.leaf 1156858678) (.leaf 1133553923))) (.branch 65 (.branch 64 (.leaf 1110796349) (.leaf 1088569525)) (.branch 66 (.leaf 1066857667) (.leaf 1045645600)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1024918736) (.leaf 1004663043)) (.branch 70 (.leaf 984865018) (.leaf 965511667))) (.branch 73 (.branch 72 (.leaf 946590474) (.leaf 928089389)) (.branch 74 (.leaf 909996797) (.leaf 892301505))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 874992720) (.branch 77 (.leaf 858060033) (.leaf 841493400))) (.branch 80 (.branch 79 (.leaf 825283126) (.leaf 809419853)) (.branch 81 (.leaf 793894541) (.leaf 778698458)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 763823163) (.leaf 749260497)) (.branch 85 (.leaf 735002570) (.leaf 721041750))) (.branch 88 (.branch 87 (.leaf 707370651) (.leaf 693982124)) (.branch 89 (.leaf 680869247) (.leaf 668025316)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 655443837) (.branch 92 (.leaf 643118515) (.leaf 631043249))) (.branch 95 (.branch 94 (.leaf 619212122) (.leaf 607619395)) (.branch 96 (.leaf 596259503) (.leaf 585127041)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 574216765) (.leaf 563523582)) (.branch 100 (.leaf 553042546) (.leaf 542768853))) (.branch 103 (.branch 102 (.leaf 532697832) (.leaf 522824947)) (.branch 104 (.leaf 513145784) (.leaf 503656053))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 494351581) (.leaf 485228308)) (.branch 108 (.leaf 476282282) (.leaf 467509659))) (.branch 111 (.branch 110 (.leaf 458906693) (.leaf 450469739)) (.branch 112 (.leaf 442195247) (.leaf 434079758)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 426119901) (.leaf 418312392)) (.branch 116 (.leaf 410654028) (.leaf 403141690))) (.branch 119 (.branch 118 (.leaf 395772333) (.leaf 388542988)) (.branch 120 (.leaf 381450761) (.leaf 374492826)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 500).prefactor = (919599295651671/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 500).cutoff/(generalMeanRows 500).c)).2 =
    (103892083656339/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 500).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 500).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 500).q*(generalMeanRows 500).c/2-2 = (227/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable159.value]
    have hcontinuation : (generalMeanRows 500).q*(generalMeanRows 500).cutoff/2-2 = (3278/1557:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable188.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 500).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 500

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 500).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 500).criticalRate j.val*(generalMeanRows 500).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 500).c*(generalMeanRows 500).criticalPoint j.val)).2-
      (generalMeanRows 500).J/2-(generalMeanRows 500).error (generalMeanGrid j.val)+
      (generalMeanRows 500).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 500).c)).2-
      (generalMeanRows 500).J/2-(generalMeanRows 500).error 4 := by
  have he : (generalMeanRows 500).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 500) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 500)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0500

/-! Kernel-checked entropy margins for general spectral rectangle 501. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0501
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5203807617) (.branch 2 (.leaf 5035005212) (.leaf 4873683237))) (.branch 5 (.branch 4 (.leaf 4719412399) (.leaf 4571793868)) (.branch 6 (.leaf 4430456626) (.leaf 4295055088)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4165266974) (.leaf 4040791409)) (.branch 10 (.leaf 3921347199) (.leaf 3806671285))) (.branch 13 (.branch 12 (.leaf 3696517338) (.leaf 3590654491)) (.branch 14 (.leaf 3488866182) (.leaf 3390949104))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3296712244) (.branch 17 (.leaf 3205976006) (.leaf 3118571410))) (.branch 20 (.branch 19 (.leaf 3034339357) (.leaf 2953129949)) (.branch 21 (.leaf 2874801871) (.leaf 2799221815)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2726263956) (.leaf 2655809461)) (.branch 25 (.leaf 2587746040) (.leaf 2521967528))) (.branch 28 (.branch 27 (.leaf 2458373499) (.leaf 2396868905)) (.branch 29 (.leaf 2337363748) (.leaf 2279772764)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2224015142) (.branch 32 (.leaf 2170014251) (.leaf 2117697394))) (.branch 35 (.branch 34 (.leaf 2066995571) (.leaf 2017843267)) (.branch 36 (.leaf 1970178245) (.leaf 1923941361)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1879076379) (.leaf 1835529817)) (.branch 40 (.leaf 1793250779) (.leaf 1752190821))) (.branch 43 (.branch 42 (.leaf 1712303806) (.leaf 1673545782)) (.branch 44 (.leaf 1635874859) (.leaf 1599251099))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1563636408) (.branch 47 (.leaf 1528994437) (.leaf 1495290491))) (.branch 50 (.branch 49 (.leaf 1462491438) (.leaf 1430565631)) (.branch 51 (.leaf 1399482823) (.leaf 1369214102)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1339731817) (.leaf 1311009514)) (.branch 55 (.leaf 1283021876) (.leaf 1255744662))) (.branch 58 (.branch 57 (.leaf 1229154659) (.leaf 1203229623)) (.branch 59 (.leaf 1177948236) (.leaf 1153290058))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1129235484) (.branch 62 (.leaf 1105765702) (.leaf 1082862658))) (.branch 65 (.branch 64 (.leaf 1060509013) (.leaf 1038688118)) (.branch 66 (.leaf 1017383970) (.leaf 996581191)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 976264992) (.leaf 956421150)) (.branch 70 (.leaf 937035979) (.leaf 918096304))) (.branch 73 (.branch 72 (.leaf 899589442) (.leaf 881503175)) (.branch 74 (.leaf 863825731) (.leaf 846545765))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 829652336) (.branch 77 (.leaf 813134895) (.leaf 796983261))) (.branch 80 (.branch 79 (.leaf 781187610) (.leaf 765738459)) (.branch 81 (.leaf 750626646) (.leaf 735843324)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 721379942) (.leaf 707228234)) (.branch 85 (.leaf 693380209) (.leaf 679828135))) (.branch 88 (.branch 87 (.leaf 666564534) (.leaf 653582166)) (.branch 89 (.leaf 640874024) (.leaf 628433321)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 616253484) (.branch 92 (.leaf 604328143) (.leaf 592651126))) (.branch 95 (.branch 94 (.leaf 581216446) (.leaf 570018300)) (.branch 96 (.leaf 559051059) (.leaf 548309260)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 537787602) (.leaf 527480937)) (.branch 100 (.leaf 517384270) (.leaf 507492747))) (.branch 103 (.branch 102 (.leaf 497801652) (.leaf 488306404)) (.branch 104 (.leaf 479002549) (.leaf 469885758))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 460951822) (.leaf 452196644)) (.branch 108 (.leaf 443616243) (.leaf 435206741))) (.branch 111 (.branch 110 (.leaf 426964366) (.leaf 418885447)) (.branch 112 (.leaf 410966407) (.leaf 403203764)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 395594127) (.leaf 388134192)) (.branch 116 (.leaf 380820739) (.leaf 373650630))) (.branch 119 (.branch 118 (.leaf 366620806) (.leaf 359728286)) (.branch 120 (.leaf 352970161) (.leaf 346343595)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 501).prefactor = (1157468839524963/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 501).cutoff/(generalMeanRows 501).c)).2 =
    (81551158977713/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 501).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 501).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 501).q*(generalMeanRows 501).c/2-2 = (1169/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable162.value]
    have hcontinuation : (generalMeanRows 501).q*(generalMeanRows 501).cutoff/2-2 = (3278/1557:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable188.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 501).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 501

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 501).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 501).criticalRate j.val*(generalMeanRows 501).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 501).c*(generalMeanRows 501).criticalPoint j.val)).2-
      (generalMeanRows 501).J/2-(generalMeanRows 501).error (generalMeanGrid j.val)+
      (generalMeanRows 501).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 501).c)).2-
      (generalMeanRows 501).J/2-(generalMeanRows 501).error 4 := by
  have he : (generalMeanRows 501).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 501) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 501)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0501

/-! Kernel-checked entropy margins for general spectral rectangle 502. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0502
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5154124145) (.branch 2 (.leaf 4984479935) (.leaf 4822350546))) (.branch 5 (.branch 4 (.leaf 4667307156) (.leaf 4518951267)) (.branch 6 (.leaf 4376912057) (.leaf 4240844020)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4110424850) (.leaf 3985353545)) (.branch 10 (.leaf 3865348699) (.leaf 3750146961))) (.branch 13 (.branch 12 (.leaf 3639501642) (.leaf 3533181450)) (.branch 14 (.leaf 3430969344) (.leaf 3332661491))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3238066305) (.branch 17 (.leaf 3147003585) (.leaf 3059303712))) (.branch 20 (.branch 19 (.leaf 2974806918) (.leaf 2893362616)) (.branch 21 (.leaf 2814828783) (.leaf 2739071386)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2665963864) (.leaf 2595386638)) (.branch 25 (.leaf 2527226668) (.leaf 2461377030))) (.branch 28 (.branch 27 (.leaf 2397736541) (.leaf 2336209398)) (.branch 29 (.leaf 2276704845) (.leaf 2219136868)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2163423909) (.branch 32 (.leaf 2109488599) (.leaf 2057257506))) (.branch 35 (.branch 34 (.leaf 2006660911) (.leaf 1957632584)) (.branch 36 (.leaf 1910109585) (.leaf 1864032079)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1819343152) (.leaf 1775988653)) (.branch 40 (.leaf 1733917034) (.leaf 1693079209))) (.branch 43 (.branch 42 (.leaf 1653428414) (.leaf 1614920083)) (.branch 44 (.leaf 1577511728) (.leaf 1541162825))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1505834709) (.branch 47 (.leaf 1471490474) (.leaf 1438094884))) (.branch 50 (.branch 49 (.leaf 1405614278) (.leaf 1374016494)) (.branch 51 (.leaf 1343270787) (.leaf 1313347759)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1284219286) (.leaf 1255858457)) (.branch 55 (.leaf 1228239510) (.leaf 1201337776))) (.branch 58 (.branch 57 (.leaf 1175129620) (.leaf 1149592395)) (.branch 59 (.leaf 1124704392) (.leaf 1100444791))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1076793619) (.branch 62 (.leaf 1053731711) (.leaf 1031240668))) (.branch 65 (.branch 64 (.leaf 1009302822) (.leaf 987901202)) (.branch 66 (.leaf 967019497) (.leaf 946642030)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 926753726) (.leaf 907340084)) (.branch 70 (.leaf 888387150) (.leaf 869881494))) (.branch 73 (.branch 72 (.leaf 851810183) (.leaf 834160762)) (.branch 74 (.leaf 816921231) (.leaf 800080021))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 783625983) (.branch 77 (.leaf 767548362) (.leaf 751836783))) (.branch 80 (.branch 79 (.leaf 736481235) (.leaf 721472053)) (.branch 81 (.leaf 706799904) (.leaf 692455777)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 678430961) (.leaf 664717039)) (.branch 85 (.leaf 651305875) (.leaf 638189600))) (.branch 88 (.branch 87 (.leaf 625360602) (.leaf 612811515)) (.branch 89 (.leaf 600535212) (.leaf 588524792)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 576773571) (.branch 92 (.leaf 565275075) (.leaf 554023033))) (.branch 95 (.branch 94 (.leaf 543011364) (.leaf 532234176)) (.branch 96 (.leaf 521685753) (.leaf 511360553)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 501253198) (.leaf 491358470)) (.branch 100 (.leaf 481671304) (.leaf 472186781))) (.branch 103 (.branch 102 (.leaf 462900126) (.leaf 453806701)) (.branch 104 (.leaf 444901997) (.leaf 436181637))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 427641363) (.leaf 419277036)) (.branch 108 (.leaf 411084632) (.leaf 403060237))) (.branch 111 (.branch 110 (.leaf 395200043) (.leaf 387500346)) (.branch 112 (.leaf 379957539) (.leaf 372568114)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 365328654) (.leaf 358235831)) (.branch 116 (.leaf 351286406) (.leaf 344477221))) (.branch 119 (.branch 118 (.leaf 337805202) (.leaf 331267352)) (.branch 120 (.leaf 324860750) (.leaf 318582551)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 502).prefactor = (926681687721603/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 502).cutoff/(generalMeanRows 502).c)).2 =
    (49280014170937/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 502).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 502).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 502).q*(generalMeanRows 502).c/2-2 = (1203/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable135.value]
    have hcontinuation : (generalMeanRows 502).q*(generalMeanRows 502).cutoff/2-2 = (1630/783:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable187.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 502).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 502

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 502).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 502).criticalRate j.val*(generalMeanRows 502).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 502).c*(generalMeanRows 502).criticalPoint j.val)).2-
      (generalMeanRows 502).J/2-(generalMeanRows 502).error (generalMeanGrid j.val)+
      (generalMeanRows 502).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 502).c)).2-
      (generalMeanRows 502).J/2-(generalMeanRows 502).error 4 := by
  have he : (generalMeanRows 502).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 502) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 502)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0502

/-! Kernel-checked entropy margins for general spectral rectangle 503. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0503
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5018987948) (.branch 2 (.leaf 4848977454) (.leaf 4686552680))) (.branch 5 (.branch 4 (.leaf 4531281489) (.leaf 4382762244)) (.branch 6 (.leaf 4240621149) (.leaf 4104509876)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3974103434) (.leaf 3849098267)) (.branch 10 (.leaf 3729210535) (.leaf 3614174566))) (.branch 13 (.branch 12 (.leaf 3503741451) (.leaf 3397677782)) (.branch 14 (.leaf 3295764489) (.leaf 3197795796))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3103578258) (.branch 17 (.leaf 3012929888) (.leaf 2925679357))) (.branch 20 (.branch 19 (.leaf 2841665252) (.leaf 2760735408)) (.branch 21 (.leaf 2682746282) (.leaf 2607562385)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2535055751) (.leaf 2465105450)) (.branch 25 (.leaf 2397597140) (.leaf 2332422646))) (.branch 28 (.branch 27 (.leaf 2269479580) (.leaf 2208670974)) (.branch 29 (.leaf 2149904953) (.leaf 2093094424)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2038156787) (.branch 32 (.leaf 1985013670) (.leaf 1933590674))) (.branch 35 (.branch 34 (.leaf 1883817145) (.leaf 1835625954)) (.branch 36 (.leaf 1788953293) (.leaf 1743738487)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1699923818) (.leaf 1657454353)) (.branch 40 (.leaf 1616277792) (.leaf 1576344325))) (.branch 43 (.branch 42 (.leaf 1537606489) (.leaf 1500019043)) (.branch 44 (.leaf 1463538849) (.leaf 1428124754))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1393737489) (.branch 47 (.leaf 1360339567) (.leaf 1327895187))) (.branch 50 (.branch 49 (.leaf 1296370147) (.leaf 1265731765)) (.branch 51 (.leaf 1235948791) (.leaf 1206991342)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1178830830) (.leaf 1151439892)) (.branch 55 (.leaf 1124792335) (.leaf 1098863073))) (.branch 58 (.branch 57 (.leaf 1073628071) (.leaf 1049064298)) (.branch 59 (.leaf 1025149672) (.leaf 1001863018))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 979184022) (.branch 62 (.leaf 957093190) (.leaf 935571806))) (.branch 65 (.branch 64 (.leaf 914601900) (.leaf 894166210)) (.branch 66 (.leaf 874248147) (.leaf 854831766)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 835901737) (.leaf 817443313)) (.branch 70 (.leaf 799442306) (.leaf 781885061))) (.branch 73 (.branch 72 (.leaf 764758430) (.leaf 748049754)) (.branch 74 (.leaf 731746836) (.leaf 715837923))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 700311684) (.branch 77 (.leaf 685157197) (.leaf 670363926))) (.branch 80 (.branch 79 (.leaf 655921704) (.leaf 641820722)) (.branch 81 (.leaf 628051510) (.leaf 614604922)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 601472125) (.leaf 588644586)) (.branch 85 (.leaf 576114055) (.leaf 563872561))) (.branch 88 (.branch 87 (.leaf 551912391) (.leaf 540226090)) (.branch 89 (.leaf 528806441) (.leaf 517646462)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 506739394) (.branch 92 (.leaf 496078693) (.leaf 485658020))) (.branch 95 (.branch 94 (.leaf 475471235) (.leaf 465512389)) (.branch 96 (.leaf 455775716) (.leaf 446255624)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 436946694) (.leaf 427843668)) (.branch 100 (.leaf 418941446) (.leaf 410235078))) (.branch 103 (.branch 102 (.leaf 401719762) (.leaf 393390835)) (.branch 104 (.leaf 385243769) (.leaf 377274167))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 369477759) (.leaf 361850394)) (.branch 108 (.leaf 354388040) (.leaf 347086779))) (.branch 111 (.branch 110 (.leaf 339942798) (.leaf 332952395)) (.branch 112 (.leaf 326111966) (.leaf 319418006)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 312867106) (.leaf 306455948)) (.branch 116 (.leaf 300181304) (.leaf 294040032))) (.branch 119 (.branch 118 (.leaf 288029073) (.leaf 282145446)) (.branch 120 (.leaf 276386252) (.leaf 270748665)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 503).prefactor = (4666067271367059/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 503).cutoff/(generalMeanRows 503).c)).2 =
    (378914142889271/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 503).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 503).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 503).q*(generalMeanRows 503).c/2-2 = (1271/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable168.value]
    have hcontinuation : (generalMeanRows 503).q*(generalMeanRows 503).cutoff/2-2 = (1630/783:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable187.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 503).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 503

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 503).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 503).criticalRate j.val*(generalMeanRows 503).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 503).c*(generalMeanRows 503).criticalPoint j.val)).2-
      (generalMeanRows 503).J/2-(generalMeanRows 503).error (generalMeanGrid j.val)+
      (generalMeanRows 503).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 503).c)).2-
      (generalMeanRows 503).J/2-(generalMeanRows 503).error 4 := by
  have he : (generalMeanRows 503).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 503) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 503)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0503

/-! Kernel-checked entropy margins for general spectral rectangle 504. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0504
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5299774480) (.branch 2 (.leaf 5132730364) (.leaf 4972990537))) (.branch 5 (.branch 4 (.leaf 4820138073) (.leaf 4673785576)) (.branch 6 (.leaf 4533572601) (.leaf 4399163354)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4270244627) (.leaf 4146523955)) (.branch 10 (.leaf 4027727947) (.leaf 3913600788))) (.branch 13 (.branch 12 (.leaf 3803902882) (.leaf 3698409617)) (.branch 14 (.leaf 3596910251) (.leaf 3499206892))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3405113569) (.branch 17 (.leaf 3314455385) (.leaf 3227067737))) (.branch 20 (.branch 19 (.leaf 3142795608) (.leaf 3061492908)) (.branch 21 (.leaf 2983021877) (.leaf 2907252526)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2834062130) (.leaf 2763334754)) (.branch 25 (.leaf 2694960817) (.leaf 2628836686))) (.branch 28 (.branch 27 (.leaf 2564864308) (.leaf 2502950853)) (.branch 29 (.leaf 2443008401) (.leaf 2384953637)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2328707573) (.branch 32 (.leaf 2274195290) (.leaf 2221345694))) (.branch 35 (.branch 34 (.leaf 2170091293) (.leaf 2120367984)) (.branch 36 (.leaf 2072114860) (.leaf 2025274020)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1979790405) (.leaf 1935611630)) (.branch 40 (.leaf 1892687840) (.leaf 1850971562))) (.branch 43 (.branch 42 (.leaf 1810417581) (.leaf 1770982807)) (.branch 44 (.leaf 1732626165) (.leaf 1695308485))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1658992395) (.branch 47 (.leaf 1623642231) (.leaf 1589223940))) (.branch 50 (.branch 49 (.leaf 1555704999) (.leaf 1523054333)) (.branch 51 (.leaf 1491242239) (.leaf 1460240316)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1430021398) (.leaf 1400559487)) (.branch 55 (.leaf 1371829700) (.leaf 1343808207))) (.branch 58 (.branch 57 (.leaf 1316472181) (.leaf 1289799747)) (.branch 59 (.leaf 1263769932) (.leaf 1238362628))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1213558540) (.branch 62 (.leaf 1189339153) (.leaf 1165686693))) (.branch 65 (.branch 64 (.leaf 1142584089) (.leaf 1120014940)) (.branch 66 (.leaf 1097963487) (.leaf 1076414576)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1055353636) (.leaf 1034766646)) (.branch 70 (.leaf 1014640115) (.leaf 994961052))) (.branch 73 (.branch 72 (.leaf 975716950) (.leaf 956895755)) (.branch 74 (.leaf 938485855) (.leaf 920476051))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 902855548) (.branch 77 (.leaf 885613929) (.leaf 868741142))) (.branch 80 (.branch 79 (.leaf 852227483) (.leaf 836063584)) (.branch 81 (.leaf 820240394) (.leaf 804749167)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 789581450) (.leaf 774729071)) (.branch 85 (.leaf 760184124) (.leaf 745938963))) (.branch 88 (.branch 87 (.leaf 731986185) (.leaf 718318627)) (.branch 89 (.leaf 704929349) (.leaf 691811632)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 678958964) (.branch 92 (.leaf 666365033) (.leaf 654023721))) (.branch 95 (.branch 94 (.leaf 641929093) (.leaf 630075395)) (.branch 96 (.leaf 618457041) (.leaf 607068611)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 595904842) (.leaf 584960624)) (.branch 100 (.leaf 574230994) (.leaf 563711129))) (.branch 103 (.branch 102 (.leaf 553396342) (.leaf 543282077)) (.branch 104 (.leaf 533363905) (.leaf 523637517))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 514098724) (.leaf 504743448)) (.branch 108 (.leaf 495567720) (.leaf 486567678))) (.branch 111 (.branch 110 (.leaf 477739561) (.leaf 469079706)) (.branch 112 (.leaf 460584546) (.leaf 452250605)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 444074495) (.leaf 436052917)) (.branch 116 (.leaf 428182651) (.leaf 420460561))) (.branch 119 (.branch 118 (.leaf 412883586) (.leaf 405448741)) (.branch 120 (.leaf 398153116) (.leaf 390993869)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 504).prefactor = (4539729682131809/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 504).cutoff/(generalMeanRows 504).c)).2 =
    (413036250200249/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 504).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 504).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 504).q*(generalMeanRows 504).c/2-2 = (1397/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable189.value]
    have hcontinuation : (generalMeanRows 504).q*(generalMeanRows 504).cutoff/2-2 = (503/242:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable190.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 504).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 504

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 504).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 504).criticalRate j.val*(generalMeanRows 504).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 504).c*(generalMeanRows 504).criticalPoint j.val)).2-
      (generalMeanRows 504).J/2-(generalMeanRows 504).error (generalMeanGrid j.val)+
      (generalMeanRows 504).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 504).c)).2-
      (generalMeanRows 504).J/2-(generalMeanRows 504).error 4 := by
  have he : (generalMeanRows 504).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 504) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 504)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0504

/-! Kernel-checked entropy margins for general spectral rectangle 505. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0505
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5057858722) (.branch 2 (.leaf 4886640773) (.leaf 4723033364))) (.branch 5 (.branch 4 (.leaf 4566604908) (.leaf 4416954199)) (.branch 6 (.leaf 4273707765) (.leaf 4136517504)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4005058562) (.leaf 3879027439)) (.branch 10 (.leaf 3758140275) (.leaf 3642131315))) (.branch 13 (.branch 12 (.leaf 3530751507) (.leaf 3423767244)) (.branch 14 (.leaf 3320959213) (.leaf 3222121349))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3127059885) (.branch 17 (.leaf 3035592476) (.leaf 2947547407))) (.branch 20 (.branch 19 (.leaf 2862762856) (.leaf 2781086225)) (.branch 21 (.leaf 2702373522) (.leaf 2626488794)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2553303596) (.leaf 2482696513)) (.branch 25 (.leaf 2414552709) (.leaf 2348763508))) (.branch 28 (.branch 27 (.leaf 2285226019) (.leaf 2223842767)) (.branch 29 (.leaf 2164521373) (.leaf 2107174237)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2051718257) (.branch 32 (.leaf 1998074560) (.leaf 1946168252))) (.branch 35 (.branch 34 (.leaf 1895928187) (.leaf 1847286751)) (.branch 36 (.leaf 1800179659) (.leaf 1754545764)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1710326883) (.leaf 1667467627)) (.branch 40 (.leaf 1625915250) (.leaf 1585619502))) (.branch 43 (.branch 42 (.leaf 1546532491) (.leaf 1508608556)) (.branch 44 (.leaf 1471804145) (.leaf 1436077707))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1401389580) (.branch 47 (.leaf 1367701892) (.leaf 1334978471))) (.branch 50 (.branch 49 (.leaf 1303184754) (.leaf 1272287702)) (.branch 51 (.leaf 1242255723) (.leaf 1213058600)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1184667418) (.leaf 1157054501)) (.branch 55 (.leaf 1130193349) (.leaf 1104058577))) (.branch 58 (.branch 57 (.leaf 1078625864) (.leaf 1053871898)) (.branch 59 (.leaf 1029774327) (.leaf 1006311713))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 983463488) (.branch 62 (.leaf 961209911) (.leaf 939532031))) (.branch 65 (.branch 64 (.leaf 918411645) (.leaf 897831270)) (.branch 66 (.leaf 877774100) (.leaf 858223985)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 839165391) (.leaf 820583377)) (.branch 70 (.leaf 802463570) (.leaf 784792132))) (.branch 73 (.branch 72 (.leaf 767555741) (.leaf 750741570)) (.branch 74 (.leaf 734337259) (.leaf 718330897))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 702711004) (.branch 77 (.leaf 687466511) (.leaf 672586741))) (.branch 80 (.branch 79 (.leaf 658061393) (.leaf 643880527)) (.branch 81 (.leaf 630034546) (.leaf 616514185)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 603310494) (.leaf 590414827)) (.branch 85 (.leaf 577818827) (.leaf 565514416))) (.branch 88 (.branch 87 (.leaf 553493785) (.leaf 541749380)) (.branch 89 (.leaf 530273893) (.leaf 519060251)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 508101611) (.branch 92 (.leaf 497391346) (.leaf 486923037))) (.branch 95 (.branch 94 (.leaf 476690469) (.leaf 466687618)) (.branch 96 (.leaf 456908648) (.leaf 447347900)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 437999890) (.leaf 428859296)) (.branch 100 (.leaf 419920960) (.leaf 411179872))) (.branch 103 (.branch 102 (.leaf 402631176) (.leaf 394270155)) (.branch 104 (.leaf 386092230) (.leaf 378092955))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 370268012) (.leaf 362613205)) (.branch 108 (.leaf 355124460) (.leaf 347797813))) (.branch 111 (.branch 110 (.leaf 340629416) (.leaf 333615525)) (.branch 112 (.leaf 326752499) (.leaf 320036799)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 313464981) (.leaf 307033695)) (.branch 116 (.leaf 300739681) (.leaf 294579766))) (.branch 119 (.branch 118 (.leaf 288550862) (.leaf 282649962)) (.branch 120 (.leaf 276874140) (.leaf 271220543)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 505).prefactor = (4670126918512371/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 505).cutoff/(generalMeanRows 505).c)).2 =
    (373183468180287/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 505).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 505).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 505).q*(generalMeanRows 505).c/2-2 = (1271/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable168.value]
    have hcontinuation : (generalMeanRows 505).q*(generalMeanRows 505).cutoff/2-2 = (3242/1575:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable191.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 505).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 505

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 505).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 505).criticalRate j.val*(generalMeanRows 505).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 505).c*(generalMeanRows 505).criticalPoint j.val)).2-
      (generalMeanRows 505).J/2-(generalMeanRows 505).error (generalMeanGrid j.val)+
      (generalMeanRows 505).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 505).c)).2-
      (generalMeanRows 505).J/2-(generalMeanRows 505).error 4 := by
  have he : (generalMeanRows 505).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 505) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 505)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0505

/-! Kernel-checked entropy margins for general spectral rectangle 506. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0506
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5299412729) (.branch 2 (.leaf 5132365082) (.leaf 4972648956))) (.branch 5 (.branch 4 (.leaf 4819843936) (.leaf 4673559465)) (.branch 6 (.leaf 4533432232) (.leaf 4399123849)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4270318766) (.leaf 4146722400)) (.branch 10 (.leaf 4028059453) (.leaf 3914072391))) (.branch 13 (.branch 12 (.leaf 3804520071) (.leaf 3699176496)) (.branch 14 (.leaf 3597829683) (.leaf 3500280630))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3406342379) (.branch 17 (.leaf 3315839153) (.leaf 3228605575))) (.branch 20 (.branch 19 (.leaf 3144485940) (.leaf 3063333559)) (.branch 21 (.leaf 2985010146) (.leaf 2909385256)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2836335773) (.leaf 2765745426)) (.branch 25 (.leaf 2697504351) (.leaf 2631508679))) (.branch 28 (.branch 27 (.leaf 2567660163) (.leaf 2505865820)) (.branch 29 (.leaf 2446037609) (.leaf 2388092126)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2331950323) (.branch 32 (.leaf 2277537247) (.leaf 2224781790))) (.branch 35 (.branch 34 (.leaf 2173616470) (.leaf 2123977207)) (.branch 36 (.leaf 2075803137) (.leaf 2029036414)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1983622047) (.leaf 1939507730)) (.branch 40 (.leaf 1896643695) (.leaf 1854982567))) (.branch 43 (.branch 42 (.leaf 1814479230) (.leaf 1775090706)) (.branch 44 (.leaf 1736776033) (.leaf 1699496156))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1663213825) (.branch 47 (.leaf 1627893499) (.leaf 1593501248))) (.branch 50 (.branch 49 (.leaf 1560004677) (.leaf 1527372834)) (.branch 51 (.leaf 1495576145) (.leaf 1464586334)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1434376360) (.leaf 1404920351)) (.branch 55 (.leaf 1376193545) (.leaf 1348172234))) (.branch 58 (.branch 57 (.leaf 1320833712) (.leaf 1294156219)) (.branch 59 (.leaf 1268118902) (.leaf 1242701762))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1217885617) (.branch 62 (.leaf 1193652060) (.leaf 1169983422))) (.branch 65 (.branch 64 (.leaf 1146862736) (.leaf 1124273701)) (.branch 66 (.leaf 1102200654) (.leaf 1080628538)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1059542871) (.leaf 1038929724)) (.branch 70 (.leaf 1018775689) (.leaf 999067862))) (.branch 73 (.branch 72 (.leaf 979793813) (.leaf 960941568)) (.branch 74 (.leaf 942499589) (.leaf 924456751))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 906802326) (.branch 77 (.leaf 889525966) (.leaf 872617682))) (.branch 80 (.branch 79 (.leaf 856067835) (.leaf 839867113)) (.branch 81 (.leaf 824006523) (.leaf 808477375)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 793271268) (.leaf 778380079)) (.branch 85 (.leaf 763795952) (.leaf 749511284))) (.branch 88 (.branch 87 (.leaf 735518719) (.leaf 721811134)) (.branch 89 (.leaf 708381630) (.leaf 695223525)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 682330343) (.branch 92 (.leaf 669695808) (.leaf 657313833))) (.branch 95 (.branch 94 (.leaf 645178516) (.leaf 633284131)) (.branch 96 (.leaf 621625120) (.leaf 610196090)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 598991804) (.leaf 588007174)) (.branch 100 (.leaf 577237259) (.leaf 566677259))) (.branch 103 (.branch 102 (.leaf 556322505) (.leaf 546168462)) (.branch 104 (.leaf 536210717) (.leaf 526444978))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 516867070) (.leaf 507472931)) (.branch 108 (.leaf 498258605) (.leaf 489220243))) (.branch 111 (.branch 110 (.leaf 480354094) (.leaf 471656508)) (.branch 112 (.leaf 463123927) (.leaf 454752883)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 446540000) (.leaf 438481983)) (.branch 116 (.leaf 430575621) (.leaf 422817784))) (.branch 119 (.branch 118 (.leaf 415205417) (.leaf 407735542)) (.branch 120 (.leaf 400405250) (.leaf 393211707)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 506).prefactor = (913598260804973/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 506).cutoff/(generalMeanRows 506).c)).2 =
    (52341783914361/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 506).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 506).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 506).q*(generalMeanRows 506).c/2-2 = (1397/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable189.value]
    have hcontinuation : (generalMeanRows 506).q*(generalMeanRows 506).cutoff/2-2 = (578/275:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable129.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 506).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 506

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 506).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 506).criticalRate j.val*(generalMeanRows 506).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 506).c*(generalMeanRows 506).criticalPoint j.val)).2-
      (generalMeanRows 506).J/2-(generalMeanRows 506).error (generalMeanGrid j.val)+
      (generalMeanRows 506).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 506).c)).2-
      (generalMeanRows 506).J/2-(generalMeanRows 506).error 4 := by
  have he : (generalMeanRows 506).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 506) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 506)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0506

/-! Kernel-checked entropy margins for general spectral rectangle 507. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0507
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5337064508) (.branch 2 (.leaf 5168845045) (.leaf 5007981264))) (.branch 5 (.branch 4 (.leaf 4854053306) (.leaf 4706671050)) (.branch 6 (.leaf 4565471516) (.leaf 4430116544)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4300290726) (.leaf 4175699536)) (.branch 10 (.leaf 4056067660) (.leaf 3941137486))) (.branch 13 (.branch 12 (.leaf 3830667728) (.leaf 3724432196)) (.branch 14 (.leaf 3622218665) (.leaf 3523827850))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3429072472) (.branch 17 (.leaf 3337776403) (.leaf 3249773882))) (.branch 20 (.branch 19 (.leaf 3164908801) (.leaf 3083034043)) (.branch 21 (.leaf 3004010878) (.leaf 2927708402)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2854003027) (.leaf 2782778002)) (.branch 25 (.leaf 2713922975) (.leaf 2647333586))) (.branch 28 (.branch 27 (.leaf 2582911088) (.leaf 2520562001)) (.branch 29 (.leaf 2460197784) (.leaf 2401734538)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2345092718) (.branch 32 (.leaf 2290196878) (.leaf 2236975424))) (.branch 35 (.branch 34 (.leaf 2185360389) (.leaf 2135287220)) (.branch 36 (.leaf 2086694579) (.leaf 2039524160)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1993720514) (.leaf 1949230891)) (.branch 40 (.leaf 1906005082) (.leaf 1863995283))) (.branch 43 (.branch 42 (.leaf 1823155957) (.leaf 1783443714)) (.branch 44 (.leaf 1744817189) (.leaf 1707236936))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1670665321) (.branch 47 (.leaf 1635066427) (.leaf 1600405964))) (.branch 50 (.branch 49 (.leaf 1566651179) (.leaf 1533770777)) (.branch 51 (.leaf 1501734849) (.leaf 1470514792)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1440083248) (.leaf 1410414039)) (.branch 55 (.leaf 1381482105) (.leaf 1353263449))) (.branch 58 (.branch 57 (.leaf 1325735082) (.leaf 1298874976)) (.branch 59 (.leaf 1272662012) (.leaf 1247075938))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1222097324) (.branch 62 (.leaf 1197707526) (.leaf 1173888644))) (.branch 65 (.branch 64 (.leaf 1150623486) (.leaf 1127895538)) (.branch 66 (.leaf 1105688927) (.leaf 1083988395)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1062779266) (.leaf 1042047423)) (.branch 70 (.leaf 1021779279) (.leaf 1001961751))) (.branch 73 (.branch 72 (.leaf 982582244) (.leaf 963628621)) (.branch 74 (.leaf 945089185) (.leaf 926952663))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 909208179) (.branch 77 (.leaf 891845245) (.leaf 874853738))) (.branch 80 (.branch 79 (.leaf 858223887) (.leaf 841946256)) (.branch 81 (.leaf 826011732) (.leaf 810411506)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 795137067) (.leaf 780180184)) (.branch 85 (.leaf 765532897) (.leaf 751187504))) (.branch 88 (.branch 87 (.leaf 737136553) (.leaf 723372827)) (.branch 89 (.leaf 709889341) (.leaf 696679325)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 683736224) (.branch 92 (.leaf 671053680) (.leaf 658625532))) (.branch 95 (.branch 94 (.leaf 646445805) (.leaf 634508703)) (.branch 96 (.leaf 622808600) (.leaf 611340039)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 600097720) (.leaf 589076497)) (.branch 100 (.leaf 578271372) (.leaf 567677487))) (.branch 103 (.branch 102 (.leaf 557290123) (.leaf 547104693)) (.branch 104 (.leaf 537116735) (.leaf 527321912))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 517716002) (.leaf 508294901)) (.branch 108 (.leaf 499054611) (.leaf 489991243))) (.branch 111 (.branch 110 (.leaf 481101010) (.leaf 472380223)) (.branch 112 (.leaf 463825290) (.leaf 455432709)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 447199072) (.leaf 439121052)) (.branch 116 (.leaf 431195410) (.leaf 423418986))) (.branch 119 (.branch 118 (.leaf 415788698) (.leaf 408301541)) (.branch 120 (.leaf 400954583) (.leaf 393744962)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 507).prefactor = (2285835959295439/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 507).cutoff/(generalMeanRows 507).c)).2 =
    (413036250200249/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 507).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 507).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 507).q*(generalMeanRows 507).c/2-2 = (1397/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable189.value]
    have hcontinuation : (generalMeanRows 507).q*(generalMeanRows 507).cutoff/2-2 = (503/242:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable190.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 507).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 507

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 507).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 507).criticalRate j.val*(generalMeanRows 507).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 507).c*(generalMeanRows 507).criticalPoint j.val)).2-
      (generalMeanRows 507).J/2-(generalMeanRows 507).error (generalMeanGrid j.val)+
      (generalMeanRows 507).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 507).c)).2-
      (generalMeanRows 507).J/2-(generalMeanRows 507).error 4 := by
  have he : (generalMeanRows 507).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 507) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 507)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0507

/-! Kernel-checked entropy margins for general spectral rectangle 508. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0508
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5195942645) (.branch 2 (.leaf 5027161494) (.leaf 4865808352))) (.branch 5 (.branch 4 (.leaf 4711460220) (.leaf 4563724003)) (.branch 6 (.leaf 4422233897) (.leaf 4286649063)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4156651539) (.leaf 4031944369)) (.branch 10 (.leaf 3912249918) (.leaf 3797308356))) (.branch 13 (.branch 12 (.leaf 3686876278) (.leaf 3580725464)) (.branch 14 (.leaf 3478641742) (.leaf 3380423964))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3285883056) (.branch 17 (.leaf 3194841171) (.leaf 3107130893))) (.branch 20 (.branch 19 (.leaf 3022594521) (.leaf 2941083406)) (.branch 21 (.leaf 2862457340) (.leaf 2786583998)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2713338420) (.leaf 2642602531)) (.branch 25 (.leaf 2574264701) (.leaf 2508219337))) (.branch 28 (.branch 27 (.leaf 2444366503) (.leaf 2382611567)) (.branch 29 (.leaf 2322864879) (.leaf 2265041462)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2209060736) (.branch 32 (.leaf 2154846248) (.leaf 2102325436))) (.branch 35 (.branch 34 (.leaf 2051429391) (.leaf 2002092652)) (.branch 36 (.leaf 1954253002) (.leaf 1907851285)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1862831229) (.leaf 1819139287)) (.branch 40 (.leaf 1776724478) (.leaf 1735538254))) (.branch 43 (.branch 42 (.leaf 1695534355) (.leaf 1656668692)) (.branch 44 (.leaf 1618899225) (.leaf 1582185852))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1546490308) (.branch 47 (.leaf 1511776062) (.leaf 1478008230))) (.branch 50 (.branch 49 (.leaf 1445153486) (.leaf 1413179982)) (.branch 51 (.leaf 1382057269) (.leaf 1351756227)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1322248996) (.leaf 1293508911)) (.branch 55 (.leaf 1265510443) (.leaf 1238229141))) (.branch 58 (.branch 57 (.leaf 1211641578) (.leaf 1185725301)) (.branch 59 (.leaf 1160458783) (.leaf 1135821374))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1111793265) (.branch 62 (.leaf 1088355441) (.leaf 1065489646))) (.branch 65 (.branch 64 (.leaf 1043178344) (.leaf 1021404690)) (.branch 66 (.leaf 1000152491) (.leaf 979406180)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 959150784) (.leaf 939371899)) (.branch 70 (.leaf 920055661) (.leaf 901188723))) (.branch 73 (.branch 72 (.leaf 882758233) (.leaf 864751806)) (.branch 74 (.leaf 847157511) (.leaf 829963843))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 813159710) (.branch 77 (.leaf 796734412) (.leaf 780677625))) (.branch 80 (.branch 79 (.leaf 764979382) (.leaf 749630062)) (.branch 81 (.leaf 734620372) (.leaf 719941334)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 705584271) (.leaf 691540796)) (.branch 85 (.leaf 677802799) (.leaf 664362435))) (.branch 88 (.branch 87 (.leaf 651212114) (.leaf 638344489)) (.branch 89 (.leaf 625752449) (.leaf 613429107)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 601367792) (.branch 92 (.leaf 589562043) (.leaf 578005593))) (.branch 95 (.branch 94 (.leaf 566692372) (.leaf 555616490)) (.branch 96 (.leaf 544772238) (.leaf 534154073)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 523756620) (.leaf 513574658)) (.branch 100 (.leaf 503603122) (.leaf 493837089))) (.branch 103 (.branch 102 (.leaf 484271780) (.leaf 474902551)) (.branch 104 (.leaf 465724888) (.leaf 456734405))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 447926836) (.leaf 439298034)) (.branch 108 (.leaf 430843963) (.leaf 422560700))) (.branch 111 (.branch 110 (.leaf 414444425) (.leaf 406491421)) (.branch 112 (.leaf 398698069) (.leaf 391060847)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 383576324) (.leaf 376241157)) (.branch 116 (.leaf 369052092) (.leaf 362005957))) (.branch 119 (.branch 118 (.leaf 355099660) (.leaf 348330189)) (.branch 120 (.leaf 341694605) (.leaf 335190046)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 508).prefactor = (1150959726384957/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 508).cutoff/(generalMeanRows 508).c)).2 =
    (49698990971597/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 508).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 508).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 508).q*(generalMeanRows 508).c/2-2 = (1481/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable171.value]
    have hcontinuation : (generalMeanRows 508).q*(generalMeanRows 508).cutoff/2-2 = (503/242:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable190.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 508).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 508

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 508).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 508).criticalRate j.val*(generalMeanRows 508).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 508).c*(generalMeanRows 508).criticalPoint j.val)).2-
      (generalMeanRows 508).J/2-(generalMeanRows 508).error (generalMeanGrid j.val)+
      (generalMeanRows 508).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 508).c)).2-
      (generalMeanRows 508).J/2-(generalMeanRows 508).error 4 := by
  have he : (generalMeanRows 508).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 508) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 508)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0508

/-! Kernel-checked entropy margins for general spectral rectangle 509. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0509
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5274423938) (.branch 2 (.leaf 5105910637) (.leaf 4944854963))) (.branch 5 (.branch 4 (.leaf 4790827410) (.leaf 4643429029)) (.branch 6 (.leaf 4502288754) (.leaf 4367061024)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4237423650) (.leaf 4113075901)) (.branch 10 (.leaf 3993736780) (.leaf 3879143470))) (.branch 13 (.branch 12 (.leaf 3769049929) (.leaf 3663225608)) (.branch 14 (.leaf 3561454300) (.leaf 3463533077))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3369271333) (.branch 17 (.leaf 3278489899) (.leaf 3191020242))) (.branch 20 (.branch 19 (.leaf 3106703721) (.leaf 3025390914)) (.branch 21 (.leaf 2946940990) (.leaf 2871221136)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2798106026) (.leaf 2727477332)) (.branch 25 (.leaf 2659223272) (.leaf 2593238190))) (.branch 28 (.branch 27 (.leaf 2529422170) (.leaf 2467680674)) (.branch 29 (.leaf 2407924210) (.leaf 2350068020)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2294031791) (.branch 32 (.leaf 2239739390) (.leaf 2187118609))) (.branch 35 (.branch 34 (.leaf 2136100933) (.leaf 2086621325)) (.branch 36 (.leaf 2038618019) (.leaf 1992032333)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1946808489) (.leaf 1902893450)) (.branch 40 (.leaf 1860236761) (.leaf 1818790407))) (.branch 43 (.branch 42 (.leaf 1778508672) (.leaf 1739348018)) (.branch 44 (.leaf 1701266957) (.leaf 1664225945))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1628187273) (.branch 47 (.leaf 1593114968) (.leaf 1558974701))) (.branch 50 (.branch 49 (.leaf 1525733697) (.leaf 1493360654)) (.branch 51 (.leaf 1461825666) (.leaf 1431100149)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1401156771) (.leaf 1371969389)) (.branch 55 (.leaf 1343512988) (.leaf 1315763622))) (.branch 58 (.branch 57 (.leaf 1288698359) (.leaf 1262295233)) (.branch 59 (.leaf 1236533193) (.leaf 1211392056))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1186852469) (.branch 62 (.leaf 1162895863) (.leaf 1139504417))) (.branch 65 (.branch 64 (.leaf 1116661022) (.leaf 1094349245)) (.branch 66 (.leaf 1072553297) (.leaf 1051258005)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1030448776) (.leaf 1010111579)) (.branch 70 (.leaf 990232910) (.leaf 970799773))) (.branch 73 (.branch 72 (.leaf 951799654) (.leaf 933220500)) (.branch 74 (.leaf 915050698) (.leaf 897279053))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 879894773) (.branch 77 (.leaf 862887447) (.leaf 846247031))) (.branch 80 (.branch 79 (.leaf 829963830) (.leaf 814028483)) (.branch 81 (.leaf 798431951) (.leaf 783165498)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 768220683) (.leaf 753589346)) (.branch 85 (.leaf 739263594) (.leaf 725235793))) (.branch 88 (.branch 87 (.leaf 711498553) (.leaf 698044724)) (.branch 89 (.leaf 684867380) (.leaf 671959814)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 659315529) (.branch 92 (.leaf 646928225) (.leaf 634791797))) (.branch 95 (.branch 94 (.leaf 622900325) (.leaf 611248066)) (.branch 96 (.leaf 599829448) (.leaf 588639063)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 577671660) (.leaf 566922144)) (.branch 100 (.leaf 556385561) (.leaf 546057101))) (.branch 103 (.branch 102 (.leaf 535932089) (.leaf 526005981)) (.branch 104 (.leaf 516274359) (.leaf 506732925))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 497377501) (.leaf 488204018)) (.branch 108 (.leaf 479208521) (.leaf 470387155))) (.branch 111 (.branch 110 (.leaf 461736171) (.leaf 453251916)) (.branch 112 (.leaf 444930831) (.leaf 436769451)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 428764398) (.leaf 420912380)) (.branch 116 (.leaf 413210188) (.leaf 405654694))) (.branch 119 (.branch 118 (.leaf 398242847) (.leaf 390971670)) (.branch 120 (.leaf 383838261) (.leaf 376839786)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 509).prefactor = (289255578779083/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 509).cutoff/(generalMeanRows 509).c)).2 =
    (209231346325861/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 509).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 509).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 509).q*(generalMeanRows 509).c/2-2 = (227/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable159.value]
    have hcontinuation : (generalMeanRows 509).q*(generalMeanRows 509).cutoff/2-2 = (6574/3105:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable192.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 509).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 509

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 509).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 509).criticalRate j.val*(generalMeanRows 509).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 509).c*(generalMeanRows 509).criticalPoint j.val)).2-
      (generalMeanRows 509).J/2-(generalMeanRows 509).error (generalMeanGrid j.val)+
      (generalMeanRows 509).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 509).c)).2-
      (generalMeanRows 509).J/2-(generalMeanRows 509).error 4 := by
  have he : (generalMeanRows 509).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 509) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 509)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0509

/-! Kernel-checked entropy margins for general spectral rectangle 510. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0510
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5202567914) (.branch 2 (.leaf 5033791571) (.leaf 4872508499))) (.branch 5 (.branch 4 (.leaf 4718287655) (.leaf 4570728632)) (.branch 6 (.leaf 4429458982) (.leaf 4294131830)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4164423736) (.leaf 4040032775)) (.branch 10 (.leaf 3920676813) (.leaf 3806091943))) (.branch 13 (.branch 12 (.leaf 3696031080) (.leaf 3590262681)) (.branch 14 (.leaf 3488569578) (.leaf 3390747928))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3296606241) (.branch 17 (.leaf 3205964502) (.leaf 3118653360))) (.branch 20 (.branch 19 (.leaf 3034513391) (.leaf 2953394417)) (.branch 21 (.leaf 2875154878) (.leaf 2799661257)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2726787551) (.leaf 2656414778)) (.branch 25 (.leaf 2588430524) (.leaf 2522728523))) (.branch 28 (.branch 27 (.leaf 2459208271) (.leaf 2397774658)) (.branch 29 (.leaf 2338337644) (.leaf 2280811936)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2225116708) (.branch 32 (.leaf 2171175328) (.leaf 2118915106))) (.branch 35 (.branch 34 (.leaf 2068267061) (.leaf 2019165705)) (.branch 36 (.leaf 1971548835) (.leaf 1925357346)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1880535052) (.leaf 1837028518)) (.branch 40 (.leaf 1794786907) (.leaf 1753761833))) (.branch 43 (.branch 42 (.leaf 1713907220) (.leaf 1675179182)) (.branch 44 (.leaf 1637535895) (.leaf 1600937489))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1565345938) (.branch 47 (.leaf 1530724966) (.leaf 1497039947))) (.branch 50 (.branch 49 (.leaf 1464257820) (.leaf 1432347007)) (.branch 51 (.leaf 1401277334) (.leaf 1371019958)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1341547296) (.leaf 1312832964)) (.branch 55 (.leaf 1284851712) (.leaf 1257579367))) (.branch 58 (.branch 57 (.leaf 1230992778) (.leaf 1205069769)) (.branch 59 (.leaf 1179789081) (.leaf 1155130338))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1131073993) (.branch 62 (.leaf 1107601295) (.leaf 1084694243))) (.branch 65 (.branch 64 (.leaf 1062335557) (.leaf 1040508639)) (.branch 66 (.leaf 1019197540) (.leaf 998386931)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 978062074) (.leaf 958208792)) (.branch 70 (.leaf 938813444) (.leaf 919862901))) (.branch 73 (.branch 72 (.leaf 901344522) (.leaf 883246130)) (.branch 74 (.leaf 865555993) (.leaf 848262803))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 831355659) (.branch 77 (.leaf 814824044) (.leaf 798657813))) (.branch 80 (.branch 79 (.leaf 782847174) (.leaf 767382674)) (.branch 81 (.leaf 752255184) (.leaf 737455883)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 722976249) (.leaf 708808041)) (.branch 85 (.leaf 694943294) (.leaf 681374301))) (.branch 88 (.branch 87 (.leaf 668093605) (.leaf 655093990)) (.branch 89 (.leaf 642368467) (.leaf 629910272)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 617712849) (.branch 92 (.leaf 605769847) (.leaf 594075109))) (.branch 95 (.branch 94 (.leaf 582622667) (.leaf 571406733)) (.branch 96 (.leaf 560421690) (.leaf 549662091)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 539122647) (.leaf 528798224)) (.branch 100 (.leaf 518683836) (.leaf 508774642))) (.branch 103 (.branch 102 (.leaf 499065936) (.leaf 489553147)) (.branch 104 (.leaf 480231830) (.leaf 471097663))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 462146447) (.leaf 453374092)) (.branch 108 (.leaf 444776623) (.leaf 436350170))) (.branch 111 (.branch 110 (.leaf 428090967) (.leaf 419995347)) (.branch 112 (.leaf 412059740) (.leaf 404280669)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 396654746) (.leaf 389178672)) (.branch 116 (.leaf 381849230) (.leaf 374663286))) (.branch 119 (.branch 118 (.leaf 367617785) (.leaf 360709747)) (.branch 120 (.leaf 353936268) (.leaf 347294512)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 510).prefactor = (928795016590407/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 510).cutoff/(generalMeanRows 510).c)).2 =
    (41065015291493/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 510).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 510).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 510).q*(generalMeanRows 510).c/2-2 = (1169/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable162.value]
    have hcontinuation : (generalMeanRows 510).q*(generalMeanRows 510).cutoff/2-2 = (6574/3105:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable192.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 510).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 510

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 510).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 510).criticalRate j.val*(generalMeanRows 510).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 510).c*(generalMeanRows 510).criticalPoint j.val)).2-
      (generalMeanRows 510).J/2-(generalMeanRows 510).error (generalMeanGrid j.val)+
      (generalMeanRows 510).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 510).c)).2-
      (generalMeanRows 510).J/2-(generalMeanRows 510).error 4 := by
  have he : (generalMeanRows 510).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 510) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 510)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0510

/-! Kernel-checked entropy margins for general spectral rectangle 511. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0511
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5221816005) (.branch 2 (.leaf 5052429439) (.leaf 4890549191))) (.branch 5 (.branch 4 (.leaf 4735744480) (.leaf 4587615098)) (.branch 6 (.leaf 4445788742) (.leaf 4309918631)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4179681370) (.leaf 4054775043)) (.branch 10 (.leaf 3934917482) (.leaf 3819844719))) (.branch 13 (.branch 12 (.leaf 3709309571) (.leaf 3603080373)) (.branch 14 (.leaf 3500939814) (.leaf 3402683882))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3308120904) (.branch 17 (.leaf 3217070662) (.leaf 3129363593))) (.branch 20 (.branch 19 (.leaf 3044840045) (.leaf 2963349603)) (.branch 21 (.leaf 2884750461) (.leaf 2808908851)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2735698512) (.leaf 2665000202)) (.branch 25 (.leaf 2596701239) (.leaf 2530695093))) (.branch 28 (.branch 27 (.leaf 2466880989) (.leaf 2405163552)) (.branch 29 (.leaf 2345452470) (.leaf 2287662186)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2231711608) (.branch 32 (.leaf 2177523841) (.leaf 2125025935))) (.branch 35 (.branch 34 (.leaf 2074148652) (.leaf 2024826251)) (.branch 36 (.leaf 1976996279) (.leaf 1930599386)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1885579144) (.leaf 1841881884)) (.branch 40 (.leaf 1799456535) (.leaf 1758254483))) (.branch 43 (.branch 42 (.leaf 1718229435) (.leaf 1679337284)) (.branch 44 (.leaf 1641535997) (.leaf 1604785496))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1569047555) (.branch 47 (.leaf 1534285702) (.leaf 1500465119))) (.branch 50 (.branch 49 (.leaf 1467552562) (.leaf 1435516271)) (.branch 51 (.leaf 1404325898) (.leaf 1373952429)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1344368117) (.leaf 1315546417)) (.branch 55 (.leaf 1287461924) (.leaf 1260090314))) (.branch 58 (.branch 57 (.leaf 1233408293) (.leaf 1207393541)) (.branch 59 (.leaf 1182024665) (.leaf 1157281154))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1133143336) (.branch 62 (.leaf 1109592335) (.leaf 1086610031))) (.branch 65 (.branch 64 (.leaf 1064179029) (.leaf 1042282620)) (.branch 66 (.leaf 1020904747) (.leaf 1000029977)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 979643472) (.leaf 959730958)) (.branch 70 (.leaf 940278702) (.leaf 921273485))) (.branch 73 (.branch 72 (.leaf 902702577) (.leaf 884553721)) (.branch 74 (.leaf 866815102) (.leaf 849475336))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 832523446) (.branch 77 (.leaf 815948844) (.leaf 799741315))) (.branch 80 (.branch 79 (.leaf 783891002) (.leaf 768388387)) (.branch 81 (.leaf 753224278) (.leaf 738389796)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 723876362) (.leaf 709675681)) (.branch 85 (.leaf 695779733) (.leaf 682180760))) (.branch 88 (.branch 87 (.leaf 668871259) (.leaf 655843964)) (.branch 89 (.leaf 643091844) (.leaf 630608088)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 618386102) (.branch 92 (.leaf 606419492) (.leaf 594702065))) (.branch 95 (.branch 94 (.leaf 583227814) (.leaf 571990916)) (.branch 96 (.leaf 560985721) (.leaf 550206749)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 539648679) (.leaf 529306347)) (.branch 100 (.leaf 519174739) (.leaf 509248985))) (.branch 103 (.branch 102 (.leaf 499524353) (.leaf 489996246)) (.branch 104 (.leaf 480660194) (.leaf 471511853))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 462547000) (.leaf 453761524)) (.branch 108 (.leaf 445151429) (.leaf 436712825))) (.branch 111 (.branch 110 (.leaf 428441926) (.leaf 420335049)) (.branch 112 (.leaf 412388604) (.leaf 404599098)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 396963127) (.leaf 389477376)) (.branch 116 (.leaf 382138614) (.leaf 374943692))) (.branch 119 (.branch 118 (.leaf 367889540) (.leaf 360973168)) (.branch 120 (.leaf 354191655) (.leaf 347542158)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 511).prefactor = (1161474396529789/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 511).cutoff/(generalMeanRows 511).c)).2 =
    (81551158977713/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 511).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 511).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 511).q*(generalMeanRows 511).c/2-2 = (1169/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable162.value]
    have hcontinuation : (generalMeanRows 511).q*(generalMeanRows 511).cutoff/2-2 = (3278/1557:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable188.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 511).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 511

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 511).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 511).criticalRate j.val*(generalMeanRows 511).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 511).c*(generalMeanRows 511).criticalPoint j.val)).2-
      (generalMeanRows 511).J/2-(generalMeanRows 511).error (generalMeanGrid j.val)+
      (generalMeanRows 511).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 511).c)).2-
      (generalMeanRows 511).J/2-(generalMeanRows 511).error 4 := by
  have he : (generalMeanRows 511).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 511) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 511)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0511

/-! Kernel-checked entropy margins for general spectral rectangle 512. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0512
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5151490671) (.branch 2 (.leaf 4981874692) (.leaf 4819800667))) (.branch 5 (.branch 4 (.leaf 4664836228) (.leaf 4516579662)) (.branch 6 (.leaf 4374657240) (.leaf 4238720825)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4108445734) (.leaf 3983528820)) (.branch 10 (.leaf 3863686745) (.leaf 3748654418))) (.branch 13 (.branch 12 (.leaf 3638183588) (.leaf 3532041565)) (.branch 14 (.leaf 3430010056) (.leaf 3331884107))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3237471142) (.branch 17 (.leaf 3146590076) (.leaf 3059070512))) (.branch 20 (.branch 19 (.leaf 2974751995) (.leaf 2893483339)) (.branch 21 (.leaf 2815121996) (.leaf 2739533483)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2666590849) (.leaf 2596174186)) (.branch 25 (.leaf 2528170173) (.leaf 2462471661))) (.branch 28 (.branch 27 (.leaf 2398977279) (.leaf 2337591074)) (.branch 29 (.leaf 2278222179) (.leaf 2220784501)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2165196427) (.branch 32 (.leaf 2111380563) (.leaf 2059263473))) (.branch 35 (.branch 34 (.leaf 2008775452) (.leaf 1959850306)) (.branch 36 (.leaf 1912425145) (.leaf 1866440197)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1821838625) (.leaf 1778566364)) (.branch 40 (.leaf 1736571963) (.leaf 1695806439))) (.branch 43 (.branch 42 (.leaf 1656223140) (.leaf 1617777616)) (.branch 44 (.leaf 1580427500) (.leaf 1544132393))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1508853756) (.branch 47 (.leaf 1474554816) (.leaf 1441200466))) (.branch 50 (.branch 49 (.leaf 1408757179) (.leaf 1377192926)) (.branch 51 (.leaf 1346477093) (.leaf 1316580416)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1287474902) (.leaf 1259133771)) (.branch 55 (.leaf 1231531388) (.leaf 1204643212))) (.branch 58 (.branch 57 (.leaf 1178445734) (.leaf 1152916430)) (.branch 59 (.leaf 1128033710) (.leaf 1103776873))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1080126063) (.branch 62 (.leaf 1057062225) (.leaf 1034567072))) (.branch 65 (.branch 64 (.leaf 1012623043) (.leaf 991213270)) (.branch 66 (.leaf 970321546) (.leaf 949932290)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 930030524) (.leaf 910601838)) (.branch 70 (.leaf 891632369) (.leaf 873108773))) (.branch 73 (.branch 72 (.leaf 855018201) (.leaf 837348278)) (.branch 74 (.leaf 820087082) (.leaf 803223120))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 786745315) (.branch 77 (.leaf 770642982) (.leaf 754905813))) (.branch 80 (.branch 79 (.leaf 739523860) (.leaf 724487520)) (.branch 81 (.leaf 709787522) (.leaf 695414909)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 681361026) (.leaf 667617508)) (.branch 85 (.leaf 654176268) (.leaf 641029485))) (.branch 88 (.branch 87 (.leaf 628169593) (.leaf 615589271)) (.branch 89 (.leaf 603281431) (.leaf 591239213)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 579455971) (.branch 92 (.leaf 567925266) (.leaf 556640861))) (.branch 95 (.branch 94 (.leaf 545596710) (.leaf 534786948)) (.branch 96 (.leaf 524205892) (.leaf 513848025)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 503707996) (.leaf 493780613)) (.branch 100 (.leaf 484060833) (.leaf 474543760))) (.branch 103 (.branch 102 (.leaf 465224640) (.leaf 456098854)) (.branch 104 (.leaf 447161914) (.leaf 438409457))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 429837242) (.leaf 421441148)) (.branch 108 (.leaf 413217163) (.leaf 405161387))) (.branch 111 (.branch 110 (.leaf 397270025) (.leaf 389539383)) (.branch 112 (.leaf 381965868) (.leaf 374545979)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 367276309) (.leaf 360153540)) (.branch 116 (.leaf 353174439) (.leaf 346335857))) (.branch 119 (.branch 118 (.leaf 339634725) (.leaf 333068053)) (.branch 120 (.leaf 326632926) (.leaf 320326502)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 512).prefactor = (2330987630471141/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 512).cutoff/(generalMeanRows 512).c)).2 =
    (400003818084247/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 512).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 512).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 512).q*(generalMeanRows 512).c/2-2 = (1203/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable135.value]
    have hcontinuation : (generalMeanRows 512).q*(generalMeanRows 512).cutoff/2-2 = (3278/1557:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable188.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 512).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 512

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 512).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 512).criticalRate j.val*(generalMeanRows 512).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 512).c*(generalMeanRows 512).criticalPoint j.val)).2-
      (generalMeanRows 512).J/2-(generalMeanRows 512).error (generalMeanGrid j.val)+
      (generalMeanRows 512).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 512).c)).2-
      (generalMeanRows 512).J/2-(generalMeanRows 512).error 4 := by
  have he : (generalMeanRows 512).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 512) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 512)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0512

/-! Kernel-checked entropy margins for general spectral rectangle 513. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0513
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5132143220) (.branch 2 (.leaf 4963142102) (.leaf 4801669645))) (.branch 5 (.branch 4 (.leaf 4647293234) (.leaf 4499610974)) (.branch 6 (.leaf 4358249002) (.leaf 4222859101)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4093116551) (.leaf 3968718209)) (.branch 10 (.leaf 3849380779) (.leaf 3734839243))) (.branch 13 (.branch 12 (.leaf 3624845456) (.leaf 3519166855)) (.branch 14 (.leaf 3417585301) (.leaf 3319896014))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3225906608) (.branch 17 (.leaf 3135436207) (.leaf 3048314632))) (.branch 20 (.branch 19 (.leaf 2964381664) (.leaf 2883486356)) (.branch 21 (.leaf 2805486410) (.leaf 2730247600)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2657643238) (.leaf 2587553679)) (.branch 25 (.leaf 2519865874) (.leaf 2454472942))) (.branch 28 (.branch 27 (.leaf 2391273783) (.leaf 2330172718)) (.branch 29 (.leaf 2271079150) (.leaf 2213907254)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2158575688) (.branch 32 (.leaf 2105007319) (.leaf 2053128977))) (.branch 35 (.branch 34 (.leaf 2002871214) (.leaf 1954168093)) (.branch 36 (.leaf 1906956974) (.leaf 1861178333)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1816775576) (.leaf 1773694875)) (.branch 40 (.leaf 1731885013) (.leaf 1691297235))) (.branch 43 (.branch 42 (.leaf 1651885113) (.leaf 1613604414)) (.branch 44 (.leaf 1576412983) (.leaf 1540270630))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1505139018) (.branch 47 (.leaf 1470981570) (.leaf 1437763371))) (.branch 50 (.branch 49 (.leaf 1405451081) (.leaf 1374012850)) (.branch 51 (.leaf 1343418244) (.leaf 1313638165)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1284644790) (.leaf 1256411496)) (.branch 55 (.leaf 1228912808) (.leaf 1202124332))) (.branch 58 (.branch 57 (.leaf 1176022708) (.leaf 1150585552)) (.branch 59 (.leaf 1125791412) (.leaf 1101619720))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1078050746) (.branch 62 (.leaf 1055065563) (.leaf 1032646000))) (.branch 65 (.branch 64 (.leaf 1010774613) (.leaf 989434646)) (.branch 66 (.leaf 968609999) (.leaf 948285197)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 928445361) (.leaf 909076179)) (.branch 70 (.leaf 890163880) (.leaf 871695212))) (.branch 73 (.branch 72 (.leaf 853657412) (.leaf 836038189)) (.branch 74 (.leaf 818825702) (.leaf 802008536))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 785575688) (.branch 77 (.leaf 769516544) (.leaf 753820868))) (.branch 80 (.branch 79 (.leaf 738478778) (.leaf 723480736)) (.branch 81 (.leaf 708817532) (.leaf 694480268)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 680460347) (.leaf 666749459)) (.branch 85 (.leaf 653339571) (.leaf 640222912))) (.branch 88 (.branch 87 (.leaf 627391965) (.leaf 614839457)) (.branch 89 (.leaf 602558344) (.leaf 590541810)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 578783250) (.branch 92 (.leaf 567276267) (.leaf 556014662))) (.branch 95 (.branch 94 (.leaf 544992424) (.leaf 534203727)) (.branch 96 (.leaf 523642920) (.leaf 513304519)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 503183206) (.leaf 493273817)) (.branch 100 (.leaf 483571339) (.leaf 474070904))) (.branch 103 (.branch 102 (.leaf 464767786) (.leaf 455657389)) (.branch 104 (.leaf 446735251) (.leaf 437997034))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 429438518) (.leaf 421055604)) (.branch 108 (.leaf 412844302) (.leaf 404800730))) (.branch 111 (.branch 110 (.leaf 396921114) (.leaf 389201779)) (.branch 112 (.leaf 381639148) (.leaf 374229737)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 366970157) (.leaf 359857103)) (.branch 116 (.leaf 352887359) (.leaf 346057790))) (.branch 119 (.branch 118 (.leaf 339365341) (.leaf 332807034)) (.branch 120 (.leaf 326379968) (.leaf 320081313)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 513).prefactor = (2329957716601057/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 513).cutoff/(generalMeanRows 513).c)).2 =
    (40289817611061/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 513).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 513).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 513).q*(generalMeanRows 513).c/2-2 = (1203/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable135.value]
    have hcontinuation : (generalMeanRows 513).q*(generalMeanRows 513).cutoff/2-2 = (6574/3105:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable192.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 513).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 513

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 513).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 513).criticalRate j.val*(generalMeanRows 513).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 513).c*(generalMeanRows 513).criticalPoint j.val)).2-
      (generalMeanRows 513).J/2-(generalMeanRows 513).error (generalMeanGrid j.val)+
      (generalMeanRows 513).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 513).c)).2-
      (generalMeanRows 513).J/2-(generalMeanRows 513).error 4 := by
  have he : (generalMeanRows 513).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 513) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 513)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0513

/-! Kernel-checked entropy margins for general spectral rectangle 514. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0514
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5149759198) (.branch 2 (.leaf 4980177986) (.leaf 4818151278))) (.branch 5 (.branch 4 (.leaf 4663244974) (.leaf 4515055797)) (.branch 6 (.leaf 4373208604) (.leaf 4237353979)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4107166090) (.leaf 3982340754)) (.branch 10 (.leaf 3862593700) (.leaf 3747659003))) (.branch 13 (.branch 12 (.leaf 3637287664) (.leaf 3531246324)) (.branch 14 (.leaf 3429316093) (.leaf 3331291489))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3236979467) (.branch 17 (.leaf 3146198528) (.leaf 3058777911))) (.branch 20 (.branch 19 (.leaf 2974556844) (.leaf 2893383864)) (.branch 21 (.leaf 2815116185) (.leaf 2739619120)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2666765544) (.leaf 2596435405)) (.branch 25 (.leaf 2528515263) (.leaf 2462897870))) (.branch 28 (.branch 27 (.leaf 2399481782) (.leaf 2338170989)) (.branch 29 (.leaf 2278874583) (.leaf 2221506446)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2165984955) (.branch 32 (.leaf 2112232714) (.leaf 2060176300))) (.branch 35 (.branch 34 (.leaf 2009746029) (.leaf 1960875735)) (.branch 36 (.leaf 1913502565) (.leaf 1867566790)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1823011621) (.leaf 1779783047)) (.branch 40 (.leaf 1737829673) (.leaf 1697102579))) (.branch 43 (.branch 42 (.leaf 1657555175) (.leaf 1619143078)) (.branch 44 (.leaf 1581823989) (.leaf 1545557578))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1510305377) (.branch 47 (.leaf 1476030685) (.leaf 1442698465))) (.branch 50 (.branch 49 (.leaf 1410275263) (.leaf 1378729121)) (.branch 51 (.leaf 1348029500) (.leaf 1318147202)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1289054307) (.leaf 1260724103)) (.branch 55 (.leaf 1233131026) (.leaf 1206250599))) (.branch 58 (.branch 57 (.leaf 1180059382) (.leaf 1154534914)) (.branch 59 (.leaf 1129655669) (.leaf 1105401007))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1081751134) (.branch 62 (.leaf 1058687054) (.leaf 1036190536))) (.branch 65 (.branch 64 (.leaf 1014244076) (.leaf 992830860)) (.branch 66 (.leaf 971934733) (.leaf 951540166)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 931632231) (.leaf 912196564)) (.branch 70 (.leaf 893219350) (.leaf 874687288))) (.branch 73 (.branch 72 (.leaf 856587574) (.leaf 838907874)) (.branch 74 (.leaf 821636304) (.leaf 804761414))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 788272160) (.branch 77 (.leaf 772157894) (.leaf 756408343))) (.branch 80 (.branch 79 (.leaf 741013592) (.leaf 725964069)) (.branch 81 (.leaf 711250534) (.leaf 696864057)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 682796013) (.leaf 669038063)) (.branch 85 (.leaf 655582146) (.leaf 642420464))) (.branch 88 (.branch 87 (.leaf 629545476) (.leaf 616949881)) (.branch 89 (.leaf 604626613) (.leaf 592568832)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 580769912) (.branch 92 (.leaf 569223432) (.leaf 557923171))) (.branch 95 (.branch 94 (.leaf 546863100) (.leaf 536037371)) (.branch 96 (.leaf 525440313) (.leaf 515066426)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 504910372) (.leaf 494966969)) (.branch 100 (.leaf 485231187) (.leaf 475698143))) (.branch 103 (.branch 102 (.leaf 466363092) (.leaf 457221424)) (.branch 104 (.leaf 448268661) (.leaf 439500450))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 430912557) (.leaf 422500869)) (.branch 108 (.leaf 414261381) (.leaf 406190201))) (.branch 111 (.branch 110 (.leaf 398283538) (.leaf 390537706)) (.branch 112 (.leaf 382949116) (.leaf 375514273)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 368229774) (.leaf 361092305)) (.branch 116 (.leaf 354098638) (.leaf 347245626))) (.branch 119 (.branch 118 (.leaf 340530206) (.leaf 333949388)) (.branch 120 (.leaf 327500261) (.leaf 321179986)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 514).prefactor = (935182099676203/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 514).cutoff/(generalMeanRows 514).c)).2 =
    (40289817611061/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 514).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 514).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 514).q*(generalMeanRows 514).c/2-2 = (1203/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable135.value]
    have hcontinuation : (generalMeanRows 514).q*(generalMeanRows 514).cutoff/2-2 = (6574/3105:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable192.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 514).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 514

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 514).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 514).criticalRate j.val*(generalMeanRows 514).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 514).c*(generalMeanRows 514).criticalPoint j.val)).2-
      (generalMeanRows 514).J/2-(generalMeanRows 514).error (generalMeanGrid j.val)+
      (generalMeanRows 514).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 514).c)).2-
      (generalMeanRows 514).J/2-(generalMeanRows 514).error 4 := by
  have he : (generalMeanRows 514).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 514) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 514)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0514

/-! Kernel-checked entropy margins for general spectral rectangle 515. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0515
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5082563238) (.branch 2 (.leaf 4912754688) (.leaf 4750523442))) (.branch 5 (.branch 4 (.leaf 4595435510) (.leaf 4447087645)) (.branch 6 (.leaf 4305104661) (.leaf 4169137036)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4038858774) (.leaf 3913965473)) (.branch 10 (.leaf 3794172601) (.leaf 3679213926))) (.branch 13 (.branch 12 (.leaf 3568840109) (.leaf 3462817416)) (.branch 14 (.leaf 3360926555) (.leaf 3262961619))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3168729112) (.branch 17 (.leaf 3078047070) (.leaf 2990744250))) (.branch 20 (.branch 19 (.leaf 2906659387) (.leaf 2825640514)) (.branch 21 (.leaf 2747544331) (.leaf 2672235633)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2599586773) (.leaf 2529477174)) (.branch 25 (.leaf 2461792870) (.leaf 2396426089))) (.branch 28 (.branch 27 (.leaf 2333274859) (.leaf 2272242651)) (.branch 29 (.leaf 2213238041) (.leaf 2156174395)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2100969584) (.branch 32 (.leaf 2047545711) (.leaf 1995828857))) (.branch 35 (.branch 34 (.leaf 1945748851) (.leaf 1897239048)) (.branch 36 (.leaf 1850236124) (.leaf 1804679886)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1760513093) (.leaf 1717681288)) (.branch 40 (.leaf 1676132642) (.leaf 1635817809))) (.branch 43 (.branch 42 (.leaf 1596689783) (.leaf 1558703776)) (.branch 44 (.leaf 1521817092) (.leaf 1485989014))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1451180701) (.branch 47 (.leaf 1417355083) (.leaf 1384476769))) (.branch 50 (.branch 49 (.leaf 1352511957) (.leaf 1321428353)) (.branch 51 (.leaf 1291195090) (.leaf 1261782655)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1233162821) (.leaf 1205308576)) (.branch 55 (.leaf 1178194068) (.leaf 1151794540))) (.branch 58 (.branch 57 (.leaf 1126086282) (.leaf 1101046571)) (.branch 59 (.leaf 1076653629) (.leaf 1052886572))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1029725367) (.branch 62 (.leaf 1007150793) (.leaf 985144400))) (.branch 65 (.branch 64 (.leaf 963688469) (.leaf 942765985)) (.branch 66 (.leaf 922360595) (.leaf 902456583)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 883038835) (.leaf 864092816)) (.branch 70 (.leaf 845604542) (.leaf 827560550))) (.branch 73 (.branch 72 (.leaf 809947881) (.leaf 792754053)) (.branch 74 (.leaf 775967041) (.leaf 759575257))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 743567527) (.branch 77 (.leaf 727933079) (.leaf 712661519))) (.branch 80 (.branch 79 (.leaf 697742820) (.leaf 683167301)) (.branch 81 (.leaf 668925617) (.leaf 655008742)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 641407954) (.leaf 628114827)) (.branch 85 (.leaf 615121214) (.leaf 602419238))) (.branch 88 (.branch 87 (.leaf 590001279) (.leaf 577859967)) (.branch 89 (.leaf 565988166) (.leaf 554378972)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 543025697) (.branch 92 (.leaf 531921865) (.leaf 521061200))) (.branch 95 (.branch 94 (.leaf 510437623) (.leaf 500045239)) (.branch 96 (.leaf 489878334) (.leaf 479931365)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 470198956) (.leaf 460675892)) (.branch 100 (.leaf 451357109) (.leaf 442237694))) (.branch 103 (.branch 102 (.leaf 433312874) (.leaf 424578017)) (.branch 104 (.leaf 416028619) (.leaf 407660309))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 399468835) (.leaf 391450065)) (.branch 108 (.leaf 383599984) (.leaf 375914684))) (.branch 111 (.branch 110 (.leaf 368390368) (.leaf 361023338)) (.branch 112 (.leaf 353810001) (.leaf 346746855)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 339830495) (.leaf 333057605)) (.branch 116 (.leaf 326424956) (.leaf 319929403))) (.branch 119 (.branch 118 (.leaf 313567884) (.leaf 307337415)) (.branch 120 (.leaf 301235088) (.leaf 295258070)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 515).prefactor = (935621714889883/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 515).cutoff/(generalMeanRows 515).c)).2 =
    (98077868115273/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 515).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 515).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 515).q*(generalMeanRows 515).c/2-2 = (1237/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable167.value]
    have hcontinuation : (generalMeanRows 515).q*(generalMeanRows 515).cutoff/2-2 = (3278/1557:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable188.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 515).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 515

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 515).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 515).criticalRate j.val*(generalMeanRows 515).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 515).c*(generalMeanRows 515).criticalPoint j.val)).2-
      (generalMeanRows 515).J/2-(generalMeanRows 515).error (generalMeanGrid j.val)+
      (generalMeanRows 515).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 515).c)).2-
      (generalMeanRows 515).J/2-(generalMeanRows 515).error 4 := by
  have he : (generalMeanRows 515).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 515) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 515)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0515

/-! Kernel-checked entropy margins for general spectral rectangle 516. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0516
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5015004128) (.branch 2 (.leaf 4845038472) (.leaf 4682685154))) (.branch 5 (.branch 4 (.leaf 4527508526) (.leaf 4379103777)) (.branch 6 (.leaf 4237094234) (.leaf 4101128968)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3970880639) (.leaf 3846043572)) (.branch 10 (.leaf 3726332018) (.leaf 3611478586))) (.branch 13 (.branch 12 (.leaf 3501232829) (.leaf 3395359953)) (.branch 14 (.leaf 3293639655) (.leaf 3195865055))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3101841731) (.branch 17 (.leaf 3011386826) (.leaf 2924328242))) (.branch 20 (.branch 19 (.leaf 2840503894) (.leaf 2759761025)) (.branch 21 (.leaf 2681955579) (.leaf 2606951622)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2534620807) (.leaf 2464841882)) (.branch 25 (.leaf 2397500232) (.leaf 2332487461))) (.branch 28 (.branch 27 (.leaf 2269700996) (.leaf 2209043728)) (.branch 29 (.leaf 2150423675) (.leaf 2093753666)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2038951052) (.branch 32 (.leaf 1985937438) (.leaf 1934638423))) (.branch 35 (.branch 34 (.leaf 1884983372) (.leaf 1836905192)) (.branch 36 (.leaf 1790340128) (.leaf 1745227571)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1701509879) (.leaf 1659132208)) (.branch 40 (.leaf 1618042357) (.leaf 1578190618))) (.branch 43 (.branch 42 (.leaf 1539529642) (.leaf 1502014305)) (.branch 44 (.leaf 1465601590) (.leaf 1430250469))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1395921803) (.branch 47 (.leaf 1362578234) (.leaf 1330184092))) (.branch 50 (.branch 49 (.leaf 1298705310) (.leaf 1268109336)) (.branch 51 (.leaf 1238365056) (.leaf 1209442718)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1181313864) (.leaf 1153951265)) (.branch 55 (.leaf 1127328853) (.leaf 1101421670))) (.branch 58 (.branch 57 (.leaf 1076205807) (.leaf 1051658355)) (.branch 59 (.leaf 1027757354) (.leaf 1004481745))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 981811330) (.branch 62 (.leaf 959726727) (.leaf 938209332))) (.branch 65 (.branch 64 (.leaf 917241280) (.leaf 896805414)) (.branch 66 (.leaf 876885245) (.leaf 857464929)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 838529228) (.leaf 820063489)) (.branch 70 (.leaf 802053613) (.leaf 784486032))) (.branch 73 (.branch 72 (.leaf 767347681) (.leaf 750625982)) (.branch 74 (.leaf 734308816) (.leaf 718384503))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 702841788) (.branch 77 (.leaf 687669815) (.leaf 672858116))) (.branch 80 (.branch 79 (.leaf 658396590) (.leaf 644275489)) (.branch 81 (.leaf 630485400) (.leaf 617017236)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 603862220) (.leaf 591011867)) (.branch 85 (.leaf 578457981) (.leaf 566192636))) (.branch 88 (.branch 87 (.leaf 554208167) (.leaf 542497160)) (.branch 89 (.leaf 531052442) (.leaf 519867069)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 508934322) (.branch 92 (.leaf 498247690) (.leaf 487800872))) (.branch 95 (.branch 94 (.leaf 477587758) (.leaf 467602430)) (.branch 96 (.leaf 457839152) (.leaf 448292362)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 438956664) (.leaf 429826827)) (.branch 100 (.leaf 420897774) (.leaf 412164579))) (.branch 103 (.branch 102 (.leaf 403622459) (.leaf 395266772)) (.branch 104 (.leaf 387093009) (.leaf 379096791))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 371273864) (.leaf 363620093)) (.branch 108 (.leaf 356131461) (.leaf 348804062))) (.branch 111 (.branch 110 (.leaf 341634099) (.leaf 334617879)) (.branch 112 (.leaf 327751810) (.leaf 321032398)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 314456244) (.leaf 308020038)) (.branch 116 (.leaf 301720561) (.leaf 295554678))) (.branch 119 (.branch 118 (.leaf 289519336) (.leaf 283611563)) (.branch 120 (.leaf 277828464) (.leaf 272167219)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 516).prefactor = (4694297719184763/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 516).cutoff/(generalMeanRows 516).c)).2 =
    (384677847606021/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 516).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 516).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 516).q*(generalMeanRows 516).c/2-2 = (1271/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable168.value]
    have hcontinuation : (generalMeanRows 516).q*(generalMeanRows 516).cutoff/2-2 = (3278/1557:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable188.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 516).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 516

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 516).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 516).criticalRate j.val*(generalMeanRows 516).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 516).c*(generalMeanRows 516).criticalPoint j.val)).2-
      (generalMeanRows 516).J/2-(generalMeanRows 516).error (generalMeanGrid j.val)+
      (generalMeanRows 516).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 516).c)).2-
      (generalMeanRows 516).J/2-(generalMeanRows 516).error 4 := by
  have he : (generalMeanRows 516).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 516) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 516)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0516

/-! Kernel-checked entropy margins for general spectral rectangle 517. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0517
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5084359119) (.branch 2 (.leaf 4914525450) (.leaf 4752255985))) (.branch 5 (.branch 4 (.leaf 4597118484) (.leaf 4448711284)) (.branch 6 (.leaf 4306660631) (.leaf 4170618299)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4040259460) (.leaf 3915280767)) (.branch 10 (.leaf 3795398636) (.leaf 3680347689))) (.branch 13 (.branch 12 (.leaf 3569879350) (.leaf 3463760571)) (.branch 14 (.leaf 3361772673) (.leaf 3263710292))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3169380418) (.branch 17 (.leaf 3078601515) (.leaf 2991202717))) (.branch 20 (.branch 19 (.leaf 2907023092) (.leaf 2825910961)) (.branch 21 (.leaf 2747723278) (.leaf 2672325054)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2599588827) (.leaf 2529394176)) (.branch 25 (.leaf 2461627267) (.leaf 2396180434))) (.branch 28 (.branch 27 (.leaf 2332951792) (.leaf 2271844879)) (.branch 29 (.leaf 2212768319) (.leaf 2155635515)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2100364357) (.branch 32 (.leaf 2046876955) (.leaf 1995099390))) (.branch 35 (.branch 34 (.leaf 1944961475) (.leaf 1896396544)) (.branch 36 (.leaf 1849341244) (.leaf 1803735347)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1759521569) (.leaf 1716645405)) (.branch 40 (.leaf 1675054977) (.leaf 1634700882))) (.branch 43 (.branch 42 (.leaf 1595536056) (.leaf 1557515649)) (.branch 44 (.leaf 1520596903) (.leaf 1484739036))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1449903141) (.branch 47 (.leaf 1416052079) (.leaf 1383150393))) (.branch 50 (.branch 49 (.leaf 1351164213) (.leaf 1320061175)) (.branch 51 (.leaf 1289810346) (.leaf 1260382145)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1231748275) (.leaf 1203881660)) (.branch 55 (.leaf 1176756382) (.leaf 1150347619))) (.branch 58 (.branch 57 (.leaf 1124631596) (.leaf 1099585530)) (.branch 59 (.leaf 1075187580) (.leaf 1051416801))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1028253104) (.branch 62 (.leaf 1005677210) (.leaf 983670611))) (.branch 65 (.branch 64 (.leaf 962215537) (.leaf 941294917)) (.branch 66 (.leaf 920892349) (.leaf 900992066)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 881578907) (.leaf 862638289)) (.branch 70 (.leaf 844156183) (.leaf 826119083))) (.branch 73 (.branch 72 (.leaf 808513987) (.leaf 791328373)) (.branch 74 (.leaf 774550177) (.leaf 758167770))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 742169946) (.branch 77 (.leaf 726545894) (.leaf 711285189))) (.branch 80 (.branch 79 (.leaf 696377771) (.leaf 681813927)) (.branch 81 (.leaf 667584283) (.leaf 653679783)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 640091680) (.leaf 626811519)) (.branch 85 (.leaf 613831130) (.leaf 601142610))) (.branch 88 (.branch 87 (.leaf 588738318) (.leaf 576610861)) (.branch 89 (.leaf 564753083) (.leaf 553158058)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 541819082) (.branch 92 (.leaf 530729659) (.leaf 519883496))) (.branch 95 (.branch 94 (.leaf 509274498) (.leaf 498896754)) (.branch 96 (.leaf 488744536) (.leaf 478812286)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 469094616) (.leaf 459586298)) (.branch 100 (.leaf 450282256) (.leaf 441177566))) (.branch 103 (.branch 102 (.leaf 432267445) (.leaf 423547249)) (.branch 104 (.leaf 415012467) (.leaf 406658717))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 398481741) (.leaf 390477399)) (.branch 108 (.leaf 382641666) (.leaf 374970631))) (.branch 111 (.branch 110 (.leaf 367460488) (.leaf 360107535)) (.branch 112 (.leaf 352908171) (.leaf 345858891)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 338956284) (.leaf 332197031)) (.branch 116 (.leaf 325577897) (.leaf 319095736))) (.branch 119 (.branch 118 (.leaf 312747481) (.leaf 306530144)) (.branch 120 (.leaf 300440816) (.leaf 294476661)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 517).prefactor = (466402565767897/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 517).cutoff/(generalMeanRows 517).c)).2 =
    (77885093514391/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 517).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 517).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 517).q*(generalMeanRows 517).c/2-2 = (1237/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable167.value]
    have hcontinuation : (generalMeanRows 517).q*(generalMeanRows 517).cutoff/2-2 = (6538/3123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable193.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 517).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 517

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 517).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 517).criticalRate j.val*(generalMeanRows 517).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 517).c*(generalMeanRows 517).criticalPoint j.val)).2-
      (generalMeanRows 517).J/2-(generalMeanRows 517).error (generalMeanGrid j.val)+
      (generalMeanRows 517).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 517).c)).2-
      (generalMeanRows 517).J/2-(generalMeanRows 517).error 4 := by
  have he : (generalMeanRows 517).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 517) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 517)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0517

/-! Kernel-checked entropy margins for general spectral rectangle 518. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0518
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5102099214) (.branch 2 (.leaf 4931672970) (.leaf 4768837323))) (.branch 5 (.branch 4 (.leaf 4613158524) (.leaf 4464233508)) (.branch 6 (.leaf 4321687219) (.leaf 4185170215)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4054356534) (.leaf 3928941772)) (.branch 10 (.leaf 3808641353) (.leaf 3693188976))) (.branch 13 (.branch 12 (.leaf 3582335197) (.leaf 3475846154)) (.branch 14 (.leaf 3373502405) (.leaf 3275097869))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3180438864) (.branch 17 (.leaf 3089343219) (.leaf 3001639474))) (.branch 20 (.branch 19 (.leaf 2917166134) (.leaf 2835770991)) (.branch 21 (.leaf 2757310499) (.leaf 2681649199)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2608659184) (.leaf 2538219614)) (.branch 25 (.leaf 2470216256) (.leaf 2404541068))) (.branch 28 (.branch 27 (.leaf 2341091812) (.leaf 2279771688)) (.branch 29 (.leaf 2220489002) (.leaf 2163156852)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2107692845) (.branch 32 (.leaf 2054018818) (.leaf 2002060592))) (.branch 35 (.branch 34 (.leaf 1951747738) (.leaf 1903013357)) (.branch 36 (.leaf 1855793875) (.leaf 1810028851)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1765660805) (.leaf 1722635040)) (.branch 40 (.leaf 1680899497) (.leaf 1640404599))) (.branch 43 (.branch 42 (.leaf 1601103121) (.leaf 1562950056)) (.branch 44 (.leaf 1525902494) (.leaf 1489919515))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1454962071) (.branch 47 (.leaf 1420992898) (.leaf 1387976413))) (.branch 50 (.branch 49 (.leaf 1355878628) (.leaf 1324667068)) (.branch 51 (.leaf 1294310689) (.leaf 1264779808)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1236046030) (.leaf 1208082185)) (.branch 55 (.leaf 1180862262) (.leaf 1154361355))) (.branch 58 (.branch 57 (.leaf 1128555606) (.leaf 1103422150)) (.branch 59 (.leaf 1078939071) (.leaf 1055085353))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1031840834) (.branch 62 (.leaf 1009186169) (.leaf 987102786))) (.branch 65 (.branch 64 (.leaf 965572852) (.leaf 944579237)) (.branch 66 (.leaf 924105481) (.leaf 904135763)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 884654868) (.leaf 865648164)) (.branch 70 (.leaf 847101571) (.leaf 829001537))) (.branch 73 (.branch 72 (.leaf 811335014) (.leaf 794089437)) (.branch 74 (.leaf 777252699) (.leaf 760813132))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 744759488) (.branch 77 (.leaf 729080922) (.leaf 713766971))) (.branch 80 (.branch 79 (.leaf 698807538) (.leaf 684192878)) (.branch 81 (.leaf 669913585) (.leaf 655960570)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 642325056) (.leaf 628998559)) (.branch 85 (.leaf 615972879) (.leaf 603240087))) (.branch 88 (.branch 87 (.leaf 590792515) (.leaf 578622743)) (.branch 89 (.leaf 566723591) (.leaf 555088110)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 543709570) (.branch 92 (.leaf 532581454) (.leaf 521697448))) (.branch 95 (.branch 94 (.leaf 511051433) (.leaf 500637480)) (.branch 96 (.leaf 490449839) (.leaf 480482934)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 470731358) (.leaf 461189864)) (.branch 100 (.leaf 451853359) (.leaf 442716901))) (.branch 103 (.branch 102 (.leaf 433775691) (.leaf 425025069)) (.branch 104 (.leaf 416460508) (.leaf 408077611))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 399872104) (.leaf 391839833)) (.branch 108 (.leaf 383976761) (.leaf 376278960))) (.branch 111 (.branch 110 (.leaf 368742613) (.leaf 361364004)) (.branch 112 (.leaf 354139520) (.leaf 347065644)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 340138954) (.leaf 333356116)) (.branch 116 (.leaf 326713888) (.leaf 320209109))) (.branch 119 (.branch 118 (.leaf 313838704) (.leaf 307599674)) (.branch 120 (.leaf 301489099) (.leaf 295504134)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 518).prefactor = (2340149573026179/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 518).cutoff/(generalMeanRows 518).c)).2 =
    (77885093514391/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 518).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 518).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 518).q*(generalMeanRows 518).c/2-2 = (1237/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable167.value]
    have hcontinuation : (generalMeanRows 518).q*(generalMeanRows 518).cutoff/2-2 = (6538/3123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable193.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 518).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 518

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 518).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 518).criticalRate j.val*(generalMeanRows 518).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 518).c*(generalMeanRows 518).criticalPoint j.val)).2-
      (generalMeanRows 518).J/2-(generalMeanRows 518).error (generalMeanGrid j.val)+
      (generalMeanRows 518).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 518).c)).2-
      (generalMeanRows 518).J/2-(generalMeanRows 518).error 4 := by
  have he : (generalMeanRows 518).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 518) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 518)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0518

/-! Kernel-checked entropy margins for general spectral rectangle 519. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0519
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5036645194) (.branch 2 (.leaf 4866036588) (.leaf 4703040389))) (.branch 5 (.branch 4 (.leaf 4547222940) (.leaf 4398181191)) (.branch 6 (.leaf 4255540031) (.leaf 4118949906)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3988084683) (.leaf 3862639737)) (.branch 10 (.leaf 3742330229) (.leaf 3626889553))) (.branch 13 (.branch 12 (.leaf 3516067925) (.leaf 3409631115)) (.branch 14 (.leaf 3307359282) (.leaf 3209045925))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3114496922) (.branch 17 (.leaf 3023529643) (.leaf 2935972157))) (.branch 20 (.branch 19 (.leaf 2851662483) (.leaf 2770447920)) (.branch 21 (.leaf 2692184422) (.leaf 2616736022)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2543974302) (.leaf 2473777910)) (.branch 25 (.leaf 2406032099) (.leaf 2340628317))) (.branch 28 (.branch 27 (.leaf 2277463811) (.leaf 2216441274)) (.branch 29 (.leaf 2157468509) (.leaf 2100458116)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2045327204) (.branch 32 (.leaf 1991997124) (.leaf 1940393218))) (.branch 35 (.branch 34 (.leaf 1890444581) (.leaf 1842083849)) (.branch 36 (.leaf 1795246989) (.leaf 1749873114)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1705904301) (.leaf 1663285424)) (.branch 40 (.leaf 1621964001) (.leaf 1581890045))) (.branch 43 (.branch 42 (.leaf 1543015925) (.leaf 1505296243)) (.branch 44 (.leaf 1468687708) (.leaf 1433149024))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1398640782) (.branch 47 (.leaf 1365125362) (.leaf 1332566840))) (.branch 50 (.branch 49 (.leaf 1300930893) (.leaf 1270184721)) (.branch 51 (.leaf 1240296968) (.leaf 1211237645)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1182978061) (.leaf 1155490760)) (.branch 55 (.leaf 1128749455) (.leaf 1102728971))) (.branch 58 (.branch 57 (.leaf 1077405190) (.leaf 1052754999)) (.branch 59 (.leaf 1028756240) (.leaf 1005387662))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 982628879) (.branch 62 (.leaf 960460328) (.leaf 938863230))) (.branch 65 (.branch 64 (.leaf 917819551) (.leaf 897311966)) (.branch 66 (.leaf 877323829) (.leaf 857839140)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 838842514) (.leaf 820319151)) (.branch 70 (.leaf 802254815) (.leaf 784635802))) (.branch 73 (.branch 72 (.leaf 767448919) (.leaf 750681460)) (.branch 74 (.leaf 734321187) (.leaf 718356304))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 702775443) (.branch 77 (.leaf 687567641) (.leaf 672722326))) (.branch 80 (.branch 79 (.leaf 658229295) (.leaf 644078704)) (.branch 81 (.leaf 630261051) (.leaf 616767156)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 603588158) (.leaf 590715490)) (.branch 85 (.leaf 578140876) (.leaf 565856314))) (.branch 88 (.branch 87 (.leaf 553854068) (.leaf 542126653)) (.branch 89 (.leaf 530666829) (.leaf 519467588)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 508522148) (.branch 92 (.leaf 497823942) (.leaf 487366608))) (.branch 95 (.branch 94 (.leaf 477143985) (.leaf 467150103)) (.branch 96 (.leaf 457379175) (.leaf 447825591)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 438483911) (.leaf 429348860)) (.branch 100 (.leaf 420415319) (.leaf 411678322))) (.branch 103 (.branch 102 (.leaf 403133048) (.leaf 394774819)) (.branch 104 (.leaf 386599091) (.leaf 378601451))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 370777614) (.leaf 363123416)) (.branch 108 (.leaf 355634809) (.leaf 348307861))) (.branch 111 (.branch 110 (.leaf 341138747) (.leaf 334123751)) (.branch 112 (.leaf 327259257) (.leaf 320541747)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 313967800) (.leaf 307534087)) (.branch 116 (.leaf 301237369) (.leaf 295074491))) (.branch 119 (.branch 118 (.leaf 289042384) (.leaf 283138059)) (.branch 120 (.leaf 277358603) (.leaf 271701183)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 519).prefactor = (2341241455345961/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 519).cutoff/(generalMeanRows 519).c)).2 =
    (378914142889271/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 519).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 519).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 519).q*(generalMeanRows 519).c/2-2 = (1271/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable168.value]
    have hcontinuation : (generalMeanRows 519).q*(generalMeanRows 519).cutoff/2-2 = (1630/783:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable187.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 519).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 519

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 519).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 519).criticalRate j.val*(generalMeanRows 519).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 519).c*(generalMeanRows 519).criticalPoint j.val)).2-
      (generalMeanRows 519).J/2-(generalMeanRows 519).error (generalMeanGrid j.val)+
      (generalMeanRows 519).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 519).c)).2-
      (generalMeanRows 519).J/2-(generalMeanRows 519).error 4 := by
  have he : (generalMeanRows 519).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 519) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 519)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0519

/-! Kernel-checked entropy margins for general spectral rectangle 520. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0520
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4970847115) (.branch 2 (.leaf 4800106406) (.leaf 4637013179))) (.branch 5 (.branch 4 (.leaf 4481132063) (.leaf 4332058389)) (.branch 6 (.leaf 4189415513) (.leaf 4052852425)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3922041609) (.leaf 3796677127)) (.branch 10 (.leaf 3676472887) (.leaf 3561161089))) (.branch 13 (.branch 12 (.leaf 3450490813) (.leaf 3344226739)) (.branch 14 (.leaf 3242147991) (.leaf 3144047072))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3049728909) (.branch 17 (.leaf 2959009962) (.leaf 2871717426))) (.branch 20 (.branch 19 (.leaf 2787688484) (.leaf 2706769632)) (.branch 21 (.leaf 2628816053) (.leaf 2553691039)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2481265464) (.leaf 2411417289)) (.branch 25 (.leaf 2344031115) (.leaf 2278997754))) (.branch 28 (.branch 27 (.leaf 2216213850) (.leaf 2155581511)) (.branch 29 (.leaf 2097007977) (.leaf 2040405308)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1985690094) (.branch 32 (.leaf 1932783185) (.leaf 1881609439))) (.branch 35 (.branch 34 (.leaf 1832097490) (.leaf 1784179525)) (.branch 36 (.leaf 1737791084) (.leaf 1692870864)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1649360543) (.leaf 1607204614)) (.branch 40 (.leaf 1566350224) (.leaf 1526747031))) (.branch 43 (.branch 42 (.leaf 1488347064) (.leaf 1451104593)) (.branch 44 (.leaf 1414976012) (.leaf 1379919720))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1345896016) (.branch 47 (.leaf 1312866998) (.leaf 1280796469))) (.branch 50 (.branch 49 (.leaf 1249649848) (.leaf 1219394085)) (.branch 51 (.leaf 1189997581) (.leaf 1161430118)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1133662782) (.leaf 1106667904)) (.branch 55 (.leaf 1080418993) (.leaf 1054890678))) (.branch 58 (.branch 57 (.leaf 1030058653) (.leaf 1005899624)) (.branch 59 (.leaf 982391259) (.leaf 959512144))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 937241732) (.branch 62 (.leaf 915560311) (.leaf 894448953))) (.branch 65 (.branch 64 (.leaf 873889488) (.leaf 853864457)) (.branch 66 (.leaf 834357088) (.leaf 815351260)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 796831472) (.leaf 778782816)) (.branch 70 (.leaf 761190949) (.leaf 744042068))) (.branch 73 (.branch 72 (.leaf 727322885) (.leaf 711020606)) (.branch 74 (.leaf 695122905) (.leaf 679617907))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 664494167) (.branch 77 (.leaf 649740648) (.leaf 635346710))) (.branch 80 (.branch 79 (.leaf 621302087) (.leaf 607596873)) (.branch 81 (.leaf 594221507) (.leaf 581166758)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 568423713) (.leaf 555983758)) (.branch 85 (.leaf 543838574) (.leaf 531980117))) (.branch 88 (.branch 87 (.leaf 520400613) (.leaf 509092542)) (.branch 89 (.leaf 498048632) (.leaf 487261845)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 476725371) (.branch 92 (.leaf 466432619) (.leaf 456377206))) (.branch 95 (.branch 94 (.leaf 446552949) (.leaf 436953859)) (.branch 96 (.leaf 427574136) (.leaf 418408155)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 409450464) (.leaf 400695778)) (.branch 100 (.leaf 392138971) (.leaf 383775070))) (.branch 103 (.branch 102 (.leaf 375599250) (.leaf 367606829)) (.branch 104 (.leaf 359793262) (.leaf 352154137))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 344685170) (.leaf 337382199)) (.branch 108 (.leaf 330241182) (.leaf 323258191))) (.branch 111 (.branch 110 (.leaf 316429409) (.leaf 309751127)) (.branch 112 (.leaf 303219737) (.leaf 296831734)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 290583707) (.leaf 284472339)) (.branch 116 (.leaf 278494403) (.leaf 272646760))) (.branch 119 (.branch 118 (.leaf 266926354) (.leaf 261330212)) (.branch 120 (.leaf 255855439) (.leaf 250499217)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 520).prefactor = (2349478150847379/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 520).cutoff/(generalMeanRows 520).c)).2 =
    (92834587270203/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 520).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 520).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 520).q*(generalMeanRows 520).c/2-2 = (261/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable137.value]
    have hcontinuation : (generalMeanRows 520).q*(generalMeanRows 520).cutoff/2-2 = (1630/783:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable187.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 520).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 520

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 520).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 520).criticalRate j.val*(generalMeanRows 520).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 520).c*(generalMeanRows 520).criticalPoint j.val)).2-
      (generalMeanRows 520).J/2-(generalMeanRows 520).error (generalMeanGrid j.val)+
      (generalMeanRows 520).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 520).c)).2-
      (generalMeanRows 520).J/2-(generalMeanRows 520).error 4 := by
  have he : (generalMeanRows 520).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 520) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 520)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0520

/-! Kernel-checked entropy margins for general spectral rectangle 521. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0521
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5034636521) (.branch 2 (.leaf 4864048426) (.leaf 4701086214))) (.branch 5 (.branch 4 (.leaf 4545314464) (.leaf 4396328533)) (.branch 6 (.leaf 4253751863) (.leaf 4117233591)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3986446404) (.leaf 3861084610)) (.branch 10 (.leaf 3740862410) (.leaf 3625512330))) (.branch 13 (.branch 12 (.leaf 3514783810) (.leaf 3408441923)) (.branch 14 (.leaf 3306266204) (.leaf 3208049597))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3113597481) (.branch 17 (.leaf 3022726791) (.leaf 2935265203))) (.branch 20 (.branch 19 (.leaf 2851050396) (.leaf 2769929369)) (.branch 21 (.leaf 2691757814) (.leaf 2616399537)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2543725929) (.leaf 2473615469)) (.branch 25 (.leaf 2405953272) (.leaf 2340630669))) (.branch 28 (.branch 27 (.leaf 2277544817) (.leaf 2216598332)) (.branch 29 (.leaf 2157698959) (.leaf 2100759257)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2045696311) (.branch 32 (.leaf 1992431455) (.leaf 1940890028))) (.branch 35 (.branch 34 (.leaf 1891001134) (.leaf 1842697423)) (.branch 36 (.leaf 1795914889) (.leaf 1750592673)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1706672890) (.leaf 1664100457)) (.branch 40 (.leaf 1622822940) (.leaf 1582790401))) (.branch 43 (.branch 42 (.leaf 1543955267) (.leaf 1506272195)) (.branch 44 (.leaf 1469697954) (.leaf 1434191309))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1399712916) (.branch 47 (.leaf 1366225220) (.leaf 1333692358))) (.branch 50 (.branch 49 (.leaf 1302080077) (.leaf 1271355641)) (.branch 51 (.leaf 1241487759) (.leaf 1212446509)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1184203266) (.leaf 1156730637)) (.branch 55 (.leaf 1130002399) (.leaf 1103993442))) (.branch 58 (.branch 57 (.leaf 1078679709) (.leaf 1054038148)) (.branch 59 (.leaf 1030046660) (.leaf 1006684056))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 983930005) (.branch 62 (.leaf 961765001) (.leaf 940170320))) (.branch 65 (.branch 64 (.leaf 919127980) (.leaf 898620710)) (.branch 66 (.leaf 878631914) (.leaf 859145641)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 840146552) (.leaf 821619897)) (.branch 70 (.leaf 803551481) (.leaf 785927644))) (.branch 73 (.branch 72 (.leaf 768735237) (.leaf 751961593)) (.branch 74 (.leaf 735594513) (.leaf 719622238))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 704033438) (.branch 77 (.leaf 688817183) (.leaf 673962935))) (.branch 80 (.branch 79 (.leaf 659460525) (.leaf 645300139)) (.branch 81 (.leaf 631472303) (.leaf 617967869)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 604778000) (.leaf 591894158)) (.branch 85 (.leaf 579308090) (.leaf 567011821))) (.branch 88 (.branch 87 (.leaf 554997634) (.leaf 543258069)) (.branch 89 (.leaf 531785905) (.leaf 520574156)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 509616058) (.branch 92 (.leaf 498905062) (.leaf 488434825))) (.branch 95 (.branch 94 (.leaf 478199201) (.leaf 468192235)) (.branch 96 (.leaf 458408156) (.leaf 448841368)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 439486444) (.leaf 430338122)) (.branch 100 (.leaf 421391295) (.leaf 412641009))) (.branch 103 (.branch 102 (.leaf 404082453) (.leaf 395710959)) (.branch 104 (.leaf 387521992) (.leaf 379511151))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 371674156) (.leaf 364006852)) (.branch 108 (.leaf 356505199) (.leaf 349165271))) (.branch 111 (.branch 110 (.leaf 341983252) (.leaf 334955430)) (.branch 112 (.leaf 328078194) (.leaf 321348033)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 314761531) (.leaf 308315363)) (.branch 116 (.leaf 302006293) (.leaf 295831173))) (.branch 119 (.branch 118 (.leaf 289786934) (.leaf 283870592)) (.branch 120 (.leaf 278079239) (.leaf 272410041)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 521).prefactor = (2348314707539523/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 521).cutoff/(generalMeanRows 521).c)).2 =
    (95447960679221/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 521).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 521).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 521).q*(generalMeanRows 521).c/2-2 = (1271/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable168.value]
    have hcontinuation : (generalMeanRows 521).q*(generalMeanRows 521).cutoff/2-2 = (6538/3123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable193.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 521).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 521

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 521).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 521).criticalRate j.val*(generalMeanRows 521).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 521).c*(generalMeanRows 521).criticalPoint j.val)).2-
      (generalMeanRows 521).J/2-(generalMeanRows 521).error (generalMeanGrid j.val)+
      (generalMeanRows 521).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 521).c)).2-
      (generalMeanRows 521).J/2-(generalMeanRows 521).error 4 := by
  have he : (generalMeanRows 521).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 521) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 521)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0521

/-! Kernel-checked entropy margins for general spectral rectangle 522. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0522
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4968510397) (.branch 2 (.leaf 4797794584) (.leaf 4634739593))) (.branch 5 (.branch 4 (.leaf 4478908300) (.leaf 4329894452)) (.branch 6 (.leaf 4187319964) (.leaf 4050832527)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3920103452) (.leaf 3794825738)) (.branch 10 (.leaf 3674712340) (.leaf 3559494597))) (.branch 13 (.branch 12 (.leaf 3448920816) (.leaf 3342754987)) (.branch 14 (.leaf 3240775612) (.leaf 3142774643))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3048556513) (.branch 17 (.leaf 2957937249) (.leaf 2870743657))) (.branch 20 (.branch 19 (.leaf 2786812583) (.leaf 2705990225)) (.branch 21 (.leaf 2628131506) (.leaf 2553099496)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2480764874) (.leaf 2411005440)) (.branch 25 (.leaf 2343705654) (.leaf 2278756218))) (.branch 28 (.branch 27 (.leaf 2216053681) (.leaf 2155500078)) (.branch 29 (.leaf 2097002594) (.leaf 2040473249)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1985828605) (.branch 32 (.leaf 1932989501) (.leaf 1881880792))) (.branch 35 (.branch 34 (.leaf 1832431120) (.leaf 1784572688)) (.branch 36 (.leaf 1738241061) (.leaf 1693374968)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1649916125) (.leaf 1607809067)) (.branch 40 (.leaf 1567000990) (.leaf 1527441602))) (.branch 43 (.branch 42 (.leaf 1489082987) (.leaf 1451879475)) (.branch 44 (.leaf 1415787518) (.leaf 1380765576))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1346774013) (.branch 47 (.leaf 1313774992) (.leaf 1281732380))) (.branch 50 (.branch 49 (.leaf 1250611662) (.leaf 1220379853)) (.branch 51 (.leaf 1191005423) (.leaf 1162458216)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1134709387) (.leaf 1107731330)) (.branch 55 (.leaf 1081497617) (.leaf 1055982942))) (.branch 58 (.branch 57 (.leaf 1031163060) (.leaf 1007014739)) (.branch 59 (.leaf 983515707) (.leaf 960644608))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 938380954) (.branch 62 (.leaf 916705087) (.leaf 895598137))) (.branch 65 (.branch 64 (.leaf 875041984) (.leaf 855019224)) (.branch 66 (.leaf 835513134) (.leaf 816507643)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 797987296) (.leaf 779937233)) (.branch 70 (.leaf 762343155) (.leaf 745191302))) (.branch 73 (.branch 72 (.leaf 728468429) (.leaf 712161781)) (.branch 74 (.leaf 696259073) (.leaf 680748466))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 665618550) (.branch 77 (.leaf 650858327) (.leaf 636457187))) (.branch 80 (.branch 79 (.leaf 622404897) (.leaf 608691584)) (.branch 81 (.leaf 595307715) (.leaf 582244088)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 569491817) (.leaf 557042316)) (.branch 85 (.leaf 544887290) (.leaf 533018719))) (.branch 88 (.branch 87 (.leaf 521428852) (.leaf 510110192)) (.branch 89 (.leaf 499055486) (.leaf 488257719)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 477710098) (.branch 92 (.leaf 467406051) (.leaf 457339212))) (.branch 95 (.branch 94 (.leaf 447503415) (.leaf 437892688)) (.branch 96 (.leaf 428501242) (.leaf 419323470)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 410353933) (.leaf 401587358)) (.branch 100 (.leaf 393018631) (.leaf 384642790))) (.branch 103 (.branch 102 (.leaf 376455021) (.leaf 368450654)) (.branch 104 (.leaf 360625152) (.leaf 352974113))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 345493260) (.leaf 338178441)) (.branch 108 (.leaf 331025620) (.leaf 324030877))) (.branch 111 (.branch 110 (.leaf 317190402) (.leaf 310500491)) (.branch 112 (.leaf 303957543) (.leaf 297558058)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 291298630) (.leaf 285175946)) (.branch 116 (.leaf 279186785) (.leaf 273328011))) (.branch 119 (.branch 118 (.leaf 267596571) (.leaf 261989497)) (.branch 120 (.leaf 256503896) (.leaf 251136953)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 522).prefactor = (4713016662875283/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 522).cutoff/(generalMeanRows 522).c)).2 =
    (187108024454213/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 522).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 522).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 522).q*(generalMeanRows 522).c/2-2 = (261/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable137.value]
    have hcontinuation : (generalMeanRows 522).q*(generalMeanRows 522).cutoff/2-2 = (6538/3123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable193.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 522).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 522

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 522).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 522).criticalRate j.val*(generalMeanRows 522).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 522).c*(generalMeanRows 522).criticalPoint j.val)).2-
      (generalMeanRows 522).J/2-(generalMeanRows 522).error (generalMeanGrid j.val)+
      (generalMeanRows 522).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 522).c)).2-
      (generalMeanRows 522).J/2-(generalMeanRows 522).error 4 := by
  have he : (generalMeanRows 522).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 522) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 522)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0522

/-! Kernel-checked entropy margins for general spectral rectangle 523. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0523
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4988334997) (.branch 2 (.leaf 4816993607) (.leaf 4653326603))) (.branch 5 (.branch 4 (.leaf 4496897084) (.leaf 4347298955)) (.branch 6 (.leaf 4204154249) (.leaf 4067110720)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3935839700) (.leaf 3810034174)) (.branch 10 (.leaf 3689407045) (.leaf 3573689570))) (.branch 13 (.branch 12 (.leaf 3462629946) (.leaf 3355992026)) (.branch 14 (.leaf 3253554156) (.leaf 3155108109))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3060458126) (.branch 17 (.leaf 2969420022) (.leaf 2881820383))) (.branch 20 (.branch 19 (.leaf 2797495820) (.leaf 2716292288)) (.branch 21 (.leaf 2638064461) (.leaf 2562675151)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2489994776) (.leaf 2419900870)) (.branch 25 (.leaf 2352277624) (.leaf 2287015471))) (.branch 28 (.branch 27 (.leaf 2224010687) (.leaf 2163165038)) (.branch 29 (.leaf 2104385438) (.leaf 2047583635)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1992675928) (.branch 32 (.leaf 1939582888) (.leaf 1888229108))) (.branch 35 (.branch 34 (.leaf 1838542972) (.leaf 1790456428)) (.branch 36 (.leaf 1743904788) (.leaf 1698826534)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1655163140) (.leaf 1612858903)) (.branch 40 (.leaf 1571860784) (.leaf 1532118263))) (.branch 43 (.branch 42 (.leaf 1493583201) (.leaf 1456209708)) (.branch 44 (.leaf 1419954024) (.leaf 1384774400))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1350630998) (.branch 47 (.leaf 1317485781) (.leaf 1285302425))) (.branch 50 (.branch 49 (.leaf 1254046228) (.leaf 1223684022)) (.branch 51 (.leaf 1194184098) (.leaf 1165516132)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1137651108) (.leaf 1110561260)) (.branch 55 (.leaf 1084220003) (.leaf 1058601877))) (.branch 58 (.branch 57 (.leaf 1033682491) (.leaf 1009438468)) (.branch 59 (.leaf 985847399) (.leaf 962887793))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 940539032) (.branch 62 (.leaf 918781333) (.leaf 897595704))) (.branch 65 (.branch 64 (.leaf 876963908) (.leaf 856868428)) (.branch 66 (.leaf 837292431) (.leaf 818219739)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 799634796) (.leaf 781522643)) (.branch 70 (.leaf 763868886) (.leaf 746659674))) (.branch 73 (.branch 72 (.leaf 729881672) (.leaf 713522040)) (.branch 74 (.leaf 697568409) (.leaf 682008864))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 666831916) (.branch 77 (.leaf 652026493) (.leaf 637581916))) (.branch 80 (.branch 79 (.leaf 623487883) (.leaf 609734452)) (.branch 81 (.leaf 596312031) (.leaf 583211355)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 570423478) (.leaf 557939758)) (.branch 85 (.leaf 545751846) (.leaf 533851670))) (.branch 88 (.branch 87 (.leaf 522231428) (.leaf 510883575)) (.branch 89 (.leaf 499800811) (.leaf 488976075)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 478402534) (.branch 92 (.leaf 468073571) (.leaf 457982781))) (.branch 95 (.branch 94 (.leaf 448123961) (.leaf 438491102)) (.branch 96 (.leaf 429078380) (.leaf 419880152)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 410890947) (.leaf 402105462)) (.branch 100 (.leaf 393518551) (.leaf 385125225))) (.branch 103 (.branch 102 (.leaf 376920641) (.leaf 368900102)) (.branch 104 (.leaf 361059047) (.leaf 353393047))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 345897803) (.leaf 338569140)) (.branch 108 (.leaf 331403000) (.leaf 324395442))) (.branch 111 (.branch 110 (.leaf 317542636) (.leaf 310840859)) (.branch 112 (.leaf 304286491) (.leaf 297876015)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 291606006) (.leaf 285473138)) (.branch 116 (.leaf 279474171) (.leaf 273605955))) (.branch 119 (.branch 118 (.leaf 267865425) (.leaf 262249595)) (.branch 120 (.leaf 256755561) (.leaf 251380495)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 523).prefactor = (2357743823775553/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 523).cutoff/(generalMeanRows 523).c)).2 =
    (92834587270203/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 523).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 523).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 523).q*(generalMeanRows 523).c/2-2 = (261/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable137.value]
    have hcontinuation : (generalMeanRows 523).q*(generalMeanRows 523).cutoff/2-2 = (1630/783:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable187.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 523).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 523

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 523).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 523).criticalRate j.val*(generalMeanRows 523).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 523).c*(generalMeanRows 523).criticalPoint j.val)).2-
      (generalMeanRows 523).J/2-(generalMeanRows 523).error (generalMeanGrid j.val)+
      (generalMeanRows 523).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 523).c)).2-
      (generalMeanRows 523).J/2-(generalMeanRows 523).error 4 := by
  have he : (generalMeanRows 523).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 523) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 523)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0523

/-! Kernel-checked entropy margins for general spectral rectangle 524. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0524
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4923611073) (.branch 2 (.leaf 4752169960) (.leaf 4588438057))) (.branch 5 (.branch 4 (.leaf 4431976713) (.leaf 4282378182)) (.branch 6 (.leaf 4139262928) (.leaf 4002277222)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3871090987) (.leaf 3745395867)) (.branch 10 (.leaf 3624903491) (.leaf 3509343901))) (.branch 13 (.branch 12 (.leaf 3398464136) (.leaf 3292026945)) (.branch 14 (.leaf 3189809618) (.leaf 3091602921))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2997210130) (.branch 17 (.leaf 2906446136) (.leaf 2819136643))) (.branch 20 (.branch 19 (.leaf 2735117415) (.leaf 2654233596)) (.branch 21 (.leaf 2576339081) (.leaf 2501295936)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2428973863) (.leaf 2359249709)) (.branch 25 (.leaf 2292007006) (.leaf 2227135551))) (.branch 28 (.branch 27 (.leaf 2164531013) (.leaf 2104094572)) (.branch 29 (.leaf 2045732578) (.leaf 1989356243)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1934881343) (.branch 32 (.leaf 1882227952) (.leaf 1831320182))) (.branch 35 (.branch 34 (.leaf 1782085956) (.leaf 1734456778)) (.branch 36 (.leaf 1688367535) (.leaf 1643756299)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1600564149) (.leaf 1558735003)) (.branch 40 (.leaf 1518215459) (.leaf 1478954648))) (.branch 43 (.branch 42 (.leaf 1440904093) (.leaf 1404017582)) (.branch 44 (.leaf 1368251044) (.leaf 1333562433))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1299911624) (.branch 47 (.leaf 1267260306) (.leaf 1235571892))) (.branch 50 (.branch 49 (.leaf 1204811425) (.leaf 1174945496)) (.branch 51 (.leaf 1145942164) (.leaf 1117770878)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1090402412) (.leaf 1063808794)) (.branch 55 (.leaf 1037963241) (.leaf 1012840108))) (.branch 58 (.branch 57 (.leaf 988414821) (.leaf 964663835)) (.branch 59 (.leaf 941564573) (.leaf 919095388))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 897235513) (.branch 62 (.leaf 875965021) (.leaf 855264784))) (.branch 65 (.branch 64 (.leaf 835116433) (.leaf 815502329)) (.branch 66 (.leaf 796405520) (.leaf 777809716)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 759699255) (.leaf 742059074)) (.branch 70 (.leaf 724874686) (.leaf 708132147))) (.branch 73 (.branch 72 (.leaf 691818036) (.leaf 675919432)) (.branch 74 (.leaf 660423889) (.leaf 645319418))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 630594463) (.branch 77 (.leaf 616237887) (.leaf 602238951))) (.branch 80 (.branch 79 (.leaf 588587295) (.leaf 575272927)) (.branch 81 (.leaf 562286202) (.leaf 549617812)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 537258766) (.leaf 525200385)) (.branch 85 (.leaf 513434281) (.leaf 501952351))) (.branch 88 (.branch 87 (.leaf 490746760) (.leaf 479809936)) (.branch 89 (.leaf 469134554) (.leaf 458713531)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 448540012) (.branch 92 (.leaf 438607364) (.leaf 428909165))) (.branch 95 (.branch 94 (.leaf 419439200) (.leaf 410191447)) (.branch 96 (.leaf 401160074) (.leaf 392339430)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 383724040) (.leaf 375308595)) (.branch 100 (.leaf 367087949) (.leaf 359057112))) (.branch 103 (.branch 102 (.leaf 351211242) (.leaf 343545646)) (.branch 104 (.leaf 336055765) (.leaf 328737178))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 321585593) (.leaf 314596841)) (.branch 108 (.leaf 307766876) (.leaf 301091767))) (.branch 111 (.branch 110 (.leaf 294567695) (.leaf 288190951)) (.branch 112 (.leaf 281957930) (.leaf 275865126)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 269909135) (.leaf 264086643)) (.branch 116 (.leaf 258394431) (.leaf 252829366))) (.branch 119 (.branch 118 (.leaf 247388401) (.leaf 242068572)) (.branch 120 (.leaf 236866995) (.leaf 231780862)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 524).prefactor = (4732077152151277/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 524).cutoff/(generalMeanRows 524).c)).2 =
    (181909758333393/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 524).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 524).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 524).q*(generalMeanRows 524).c/2-2 = (1339/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable194.value]
    have hcontinuation : (generalMeanRows 524).q*(generalMeanRows 524).cutoff/2-2 = (1630/783:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable187.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 524).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 524

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 524).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 524).criticalRate j.val*(generalMeanRows 524).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 524).c*(generalMeanRows 524).criticalPoint j.val)).2-
      (generalMeanRows 524).J/2-(generalMeanRows 524).error (generalMeanGrid j.val)+
      (generalMeanRows 524).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 524).c)).2-
      (generalMeanRows 524).J/2-(generalMeanRows 524).error 4 := by
  have he : (generalMeanRows 524).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 524) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 524)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0524

/-! Kernel-checked entropy margins for general spectral rectangle 525. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0525
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5080498506) (.branch 2 (.leaf 4910728719) (.leaf 4748548660))) (.branch 5 (.branch 4 (.leaf 4593522616) (.leaf 4445245785)) (.branch 6 (.leaf 4303341574) (.leaf 4167459193)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4037271501) (.leaf 3912473067)) (.branch 10 (.leaf 3792778432) (.leaf 3677920537))) (.branch 13 (.branch 12 (.leaf 3567649298) (.leaf 3461730315)) (.branch 14 (.leaf 3359943708) (.leaf 3262083042))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3167954356) (.branch 17 (.leaf 3077375277) (.leaf 2990174199))) (.branch 20 (.branch 19 (.leaf 2906189544) (.leaf 2825269069)) (.branch 21 (.leaf 2747269240) (.leaf 2672054649)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2599497478) (.leaf 2529477006)) (.branch 25 (.leaf 2461879149) (.leaf 2396596041))) (.branch 28 (.branch 27 (.leaf 2333525636) (.leaf 2272571349)) (.branch 29 (.leaf 2213641715) (.leaf 2156650079)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2101514300) (.branch 32 (.leaf 2048156481) (.leaf 1996502718))) (.branch 35 (.branch 34 (.leaf 1946482858) (.leaf 1898030288)) (.branch 36 (.leaf 1851081720) (.leaf 1805577004)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1761458948) (.leaf 1718673150)) (.branch 40 (.leaf 1677167837) (.leaf 1636893724))) (.branch 43 (.branch 42 (.leaf 1597803871) (.leaf 1559853553)) (.branch 44 (.leaf 1523000145) (.leaf 1487202999))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1452423344) (.branch 47 (.leaf 1418624182) (.leaf 1385770193))) (.branch 50 (.branch 49 (.leaf 1353827648) (.leaf 1322764324)) (.branch 51 (.leaf 1292549426) (.leaf 1263153512)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1234548425) (.leaf 1206707222)) (.branch 55 (.leaf 1179604120) (.leaf 1153214429))) (.branch 58 (.branch 57 (.leaf 1127514505) (.leaf 1102481690)) (.branch 59 (.leaf 1078094268) (.leaf 1054331419))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1031173169) (.branch 62 (.leaf 1008600357) (.leaf 986594588))) (.branch 65 (.branch 64 (.leaf 965138203) (.leaf 944214237)) (.branch 66 (.leaf 923806392) (.leaf 903899001)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 884477002) (.leaf 865525907)) (.branch 70 (.leaf 847031777) (.leaf 828981194))) (.branch 73 (.branch 72 (.leaf 811361243) (.leaf 794159483)) (.branch 74 (.leaf 777363930) (.leaf 760963031))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 744945654) (.branch 77 (.leaf 729301059) (.leaf 714018889))) (.branch 80 (.branch 79 (.leaf 699089147) (.leaf 684502186)) (.branch 81 (.leaf 670248691) (.leaf 656319663)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 642706411) (.leaf 629400533)) (.branch 85 (.leaf 616393908) (.leaf 603678684))) (.branch 88 (.branch 87 (.leaf 591247263) (.leaf 579092298)) (.branch 89 (.leaf 567206675) (.leaf 555583509)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 544216131) (.branch 92 (.leaf 533098083) (.leaf 522223107))) (.branch 95 (.branch 94 (.leaf 511585141) (.leaf 501178304)) (.branch 96 (.leaf 490996898) (.leaf 481035394)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 471288429) (.leaf 461750801)) (.branch 100 (.leaf 452417457) (.leaf 443283496))) (.branch 103 (.branch 102 (.leaf 434344156) (.leaf 425594813)) (.branch 104 (.leaf 417030976) (.leaf 408648278))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 400442479) (.leaf 392409454)) (.branch 108 (.leaf 384545194) (.leaf 376845800))) (.branch 111 (.branch 110 (.leaf 369307479) (.leaf 361926541)) (.branch 112 (.leaf 354699396) (.leaf 347622549)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 340692600) (.leaf 333906236)) (.branch 116 (.leaf 327260233) (.leaf 320751449))) (.branch 119 (.branch 118 (.leaf 314376826) (.leaf 308133382)) (.branch 120 (.leaf 302018213) (.leaf 296028489)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 525).prefactor = (1172990116574153/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 525).cutoff/(generalMeanRows 525).c)).2 =
    (197602915243727/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 525).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 525).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 525).q*(generalMeanRows 525).c/2-2 = (1237/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable167.value]
    have hcontinuation : (generalMeanRows 525).q*(generalMeanRows 525).cutoff/2-2 = (6574/3105:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable192.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 525).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 525

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 525).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 525).criticalRate j.val*(generalMeanRows 525).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 525).c*(generalMeanRows 525).criticalPoint j.val)).2-
      (generalMeanRows 525).J/2-(generalMeanRows 525).error (generalMeanGrid j.val)+
      (generalMeanRows 525).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 525).c)).2-
      (generalMeanRows 525).J/2-(generalMeanRows 525).error 4 := by
  have he : (generalMeanRows 525).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 525) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 525)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0525

/-! Kernel-checked entropy margins for general spectral rectangle 526. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0526
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5012613771) (.branch 2 (.leaf 4842690997) (.leaf 4680392854))) (.branch 5 (.branch 4 (.leaf 4525281984) (.leaf 4376952027)) (.branch 6 (.leaf 4235024913) (.leaf 4099148450)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3968994164) (.leaf 3844255355)) (.branch 10 (.leaf 3724645353) (.leaf 3609895945))) (.branch 13 (.branch 12 (.leaf 3499755944) (.leaf 3393989896)) (.branch 14 (.leaf 3292376912) (.leaf 3194709591))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3100793046) (.branch 17 (.leaf 3010444016) (.leaf 2923490044))) (.branch 20 (.branch 19 (.leaf 2839768732) (.leaf 2759127052)) (.branch 21 (.leaf 2681420715) (.leaf 2606513586)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2534277149) (.leaf 2464590010)) (.branch 25 (.leaf 2397337439) (.leaf 2332410945))) (.branch 28 (.branch 27 (.leaf 2269707884) (.leaf 2209131091)) (.branch 29 (.leaf 2150588545) (.leaf 2093993054)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2039261959) (.branch 32 (.leaf 1986316866) (.leaf 1935083388))) (.branch 35 (.branch 34 (.leaf 1885490910) (.leaf 1837472371)) (.branch 36 (.leaf 1790964053) (.leaf 1745905390)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1702238790) (.leaf 1659909463)) (.branch 40 (.leaf 1618865265) (.leaf 1579056552))) (.branch 43 (.branch 42 (.leaf 1540436036) (.leaf 1502958661)) (.branch 44 (.leaf 1466581477) (.leaf 1431263529))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1396965746) (.branch 47 (.leaf 1363650842) (.leaf 1331283220))) (.branch 50 (.branch 49 (.leaf 1299828883) (.leaf 1269255353)) (.branch 51 (.leaf 1239531586) (.leaf 1210627901)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1182515912) (.leaf 1155168457)) (.branch 55 (.leaf 1128559538) (.leaf 1102664264))) (.branch 58 (.branch 57 (.leaf 1077458792) (.leaf 1052920276)) (.branch 59 (.leaf 1029026822) (.leaf 1005757431))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 983091966) (.branch 62 (.leaf 961011104) (.leaf 939496298))) (.branch 65 (.branch 64 (.leaf 918529740) (.leaf 898094325)) (.branch 66 (.leaf 878173619) (.leaf 858751827)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 839813762) (.leaf 821344817)) (.branch 70 (.leaf 803330940) (.leaf 785758607))) (.branch 73 (.branch 72 (.leaf 768614798) (.leaf 751886974)) (.branch 74 (.leaf 735563057) (.leaf 719631407))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 704080804) (.branch 77 (.leaf 688900430) (.leaf 674079849))) (.branch 80 (.branch 79 (.leaf 659608993) (.leaf 645478146)) (.branch 81 (.leaf 631677927) (.leaf 618199276)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 605033444) (.leaf 592171974)) (.branch 85 (.leaf 579606694) (.leaf 567329702))) (.branch 88 (.branch 87 (.leaf 555333358) (.leaf 543610269)) (.branch 89 (.leaf 532153283) (.leaf 520955477)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 510010150) (.branch 92 (.leaf 499310811) (.leaf 488851174))) (.branch 95 (.branch 94 (.leaf 478625148) (.leaf 468626829)) (.branch 96 (.leaf 458850496) (.leaf 449290601)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 439941763) (.leaf 430798762)) (.branch 100 (.leaf 421856534) (.leaf 413110163))) (.branch 103 (.branch 102 (.leaf 404554878) (.leaf 396186046)) (.branch 104 (.leaf 387999168) (.leaf 379989874))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 372153917) (.leaf 364487172)) (.branch 108 (.leaf 356985629) (.leaf 349645387))) (.branch 111 (.branch 110 (.leaf 342462657) (.leaf 335433752)) (.branch 112 (.leaf 328555086) (.leaf 321823169)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 315234606) (.leaf 308786094)) (.branch 116 (.leaf 302474417) (.leaf 296296443))) (.branch 119 (.branch 118 (.leaf 290249123) (.leaf 284329489)) (.branch 120 (.leaf 278534647) (.leaf 272861782)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 526).prefactor = (4708065525401441/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 526).cutoff/(generalMeanRows 526).c)).2 =
    (77514441126477/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 526).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 526).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 526).q*(generalMeanRows 526).c/2-2 = (1271/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable168.value]
    have hcontinuation : (generalMeanRows 526).q*(generalMeanRows 526).cutoff/2-2 = (6574/3105:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable192.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 526).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 526

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 526).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 526).criticalRate j.val*(generalMeanRows 526).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 526).c*(generalMeanRows 526).criticalPoint j.val)).2-
      (generalMeanRows 526).J/2-(generalMeanRows 526).error (generalMeanGrid j.val)+
      (generalMeanRows 526).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 526).c)).2-
      (generalMeanRows 526).J/2-(generalMeanRows 526).error 4 := by
  have he : (generalMeanRows 526).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 526) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 526)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0526

/-! Kernel-checked entropy margins for general spectral rectangle 527. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0527
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5032359139) (.branch 2 (.leaf 4861805297) (.leaf 4698890136))) (.branch 5 (.branch 4 (.leaf 4543176502) (.leaf 4394258181)) (.branch 6 (.leaf 4251757197) (.leaf 4115321407)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3984622338) (.leaf 3859353258)) (.branch 10 (.leaf 3739227428) (.leaf 3623976532))) (.branch 13 (.branch 12 (.leaf 3513349256) (.leaf 3407109995)) (.branch 14 (.leaf 3305037682) (.leaf 3206924722))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3112576019) (.branch 17 (.leaf 3021808084) (.leaf 2934448224))) (.branch 20 (.branch 19 (.leaf 2850333792) (.leaf 2769311503)) (.branch 21 (.leaf 2691236802) (.leaf 2615973285)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2543392160) (.leaf 2473371757)) (.branch 25 (.leaf 2405797064) (.leaf 2340559308))) (.branch 28 (.branch 27 (.leaf 2277555563) (.leaf 2216688384)) (.branch 29 (.leaf 2157865469) (.leaf 2100999346)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2046007082) (.branch 32 (.leaf 1992810008) (.leaf 1941333467))) (.branch 35 (.branch 34 (.leaf 1891506579) (.leaf 1843262019)) (.branch 36 (.leaf 1796535811) (.leaf 1751267137)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1707398154) (.leaf 1664873830)) (.branch 40 (.leaf 1623641782) (.leaf 1583652132))) (.branch 43 (.branch 42 (.leaf 1544857365) (.leaf 1507212202)) (.branch 44 (.leaf 1470673476) (.leaf 1435200019))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1400752555) (.branch 47 (.leaf 1367293596) (.leaf 1334787351))) (.branch 50 (.branch 49 (.leaf 1303199633) (.leaf 1272497778)) (.branch 51 (.leaf 1242650564) (.leaf 1213628137)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1185401940) (.leaf 1157944649)) (.branch 55 (.leaf 1131230107) (.leaf 1105233269))) (.branch 58 (.branch 57 (.leaf 1079930144) (.leaf 1055297743)) (.branch 59 (.leaf 1031314029) (.leaf 1007957872))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 985209004) (.branch 62 (.leaf 963047974) (.leaf 941456116))) (.branch 65 (.branch 64 (.leaf 920415501) (.leaf 899908914)) (.branch 66 (.leaf 879919810) (.leaf 860432287)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 841431057) (.leaf 822901415)) (.branch 70 (.leaf 804829214) (.leaf 787200838))) (.branch 73 (.branch 72 (.leaf 770003178) (.leaf 753223612)) (.branch 74 (.leaf 736849978) (.leaf 720870557))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 705274054) (.branch 77 (.leaf 690049577) (.leaf 675186621))) (.branch 80 (.branch 79 (.leaf 660675049) (.leaf 646505080)) (.branch 81 (.leaf 632667269) (.leaf 619152497)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 605951956) (.leaf 593057133)) (.branch 85 (.leaf 580459803) (.leaf 568152012))) (.branch 88 (.branch 87 (.leaf 556126069) (.leaf 544374535)) (.branch 89 (.leaf 532890211) (.leaf 521666130)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 510695549) (.branch 92 (.leaf 499971935) (.leaf 489488964))) (.branch 95 (.branch 94 (.leaf 479240506) (.leaf 469220624)) (.branch 96 (.leaf 459423559) (.leaf 449843730)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 440475725) (.leaf 431314293)) (.branch 100 (.leaf 422354340) (.leaf 413590923))) (.branch 103 (.branch 102 (.leaf 405019242) (.leaf 396634639)) (.branch 104 (.leaf 388432590) (.leaf 380408700))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 372558701) (.leaf 364878443)) (.branch 108 (.leaf 357363896) (.leaf 350011140))) (.branch 111 (.branch 110 (.leaf 342816364) (.leaf 335775863)) (.branch 112 (.leaf 328886034) (.leaf 322143369)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 315544457) (.leaf 309085978)) (.branch 116 (.leaf 302764701) (.leaf 296577480))) (.branch 119 (.branch 118 (.leaf 290521252) (.leaf 284593034)) (.branch 120 (.leaf 278789922) (.leaf 273109085)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 527).prefactor = (588817861044857/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 527).cutoff/(generalMeanRows 527).c)).2 =
    (384677847606021/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 527).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 527).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 527).q*(generalMeanRows 527).c/2-2 = (1271/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable168.value]
    have hcontinuation : (generalMeanRows 527).q*(generalMeanRows 527).cutoff/2-2 = (3278/1557:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable188.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 527).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 527

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 527).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 527).criticalRate j.val*(generalMeanRows 527).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 527).c*(generalMeanRows 527).criticalPoint j.val)).2-
      (generalMeanRows 527).J/2-(generalMeanRows 527).error (generalMeanGrid j.val)+
      (generalMeanRows 527).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 527).c)).2-
      (generalMeanRows 527).J/2-(generalMeanRows 527).error 4 := by
  have he : (generalMeanRows 527).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 527) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 527)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0527

/-! Kernel-checked entropy margins for general spectral rectangle 528. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0528
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4965910318) (.branch 2 (.leaf 4795233077) (.leaf 4632229321))) (.branch 5 (.branch 4 (.leaf 4476460202) (.leaf 4327517906)) (.branch 6 (.leaf 4185022940) (.leaf 4048621719)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3917984404) (.leaf 3792802958)) (.branch 10 (.leaf 3672789404) (.leaf 3557674245))) (.branch 13 (.branch 12 (.leaf 3447205037) (.leaf 3341145096)) (.branch 14 (.leaf 3239272328) (.leaf 3141378150))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3047266523) (.branch 17 (.leaf 2956753054) (.leaf 2869664182))) (.branch 20 (.branch 19 (.leaf 2785836430) (.leaf 2705115714)) (.branch 21 (.leaf 2627356715) (.leaf 2552422291)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2480182945) (.leaf 2410516325)) (.branch 25 (.leaf 2343306769) (.leaf 2278444874))) (.branch 28 (.branch 27 (.leaf 2215827111) (.leaf 2155355451)) (.branch 29 (.leaf 2096937036) (.leaf 2040483854)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1985912453) (.branch 32 (.leaf 1933143666) (.leaf 1882102355))) (.branch 35 (.branch 34 (.leaf 1832717179) (.leaf 1784920366)) (.branch 36 (.leaf 1738647512) (.leaf 1693837387)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1650431749) (.leaf 1608375185)) (.branch 40 (.leaf 1567614944) (.leaf 1528100790))) (.branch 43 (.branch 42 (.leaf 1489784871) (.leaf 1452621576)) (.branch 44 (.leaf 1416567424) (.leaf 1381580942))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1347622562) (.branch 47 (.leaf 1314654514) (.leaf 1282640737))) (.branch 50 (.branch 49 (.leaf 1251546783) (.leaf 1221339739)) (.branch 51 (.leaf 1191988141) (.leaf 1163461906)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1135732254) (.leaf 1108771648)) (.branch 55 (.leaf 1082553727) (.leaf 1057053250))) (.branch 58 (.branch 57 (.leaf 1032246038) (.leaf 1008108921)) (.branch 59 (.leaf 984619690) (.leaf 961757049))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 939500571) (.branch 62 (.leaf 917830654) (.leaf 896728485))) (.branch 65 (.branch 64 (.leaf 876176000) (.leaf 856155848)) (.branch 66 (.leaf 836651357) (.leaf 817646507)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 799125892) (.leaf 781074699)) (.branch 70 (.leaf 763478675) (.leaf 746324105))) (.branch 73 (.branch 72 (.leaf 729597785) (.leaf 713287003)) (.branch 74 (.leaf 697379512) (.leaf 681863513))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 666727633) (.branch 77 (.leaf 651960907) (.leaf 637552762))) (.branch 80 (.branch 79 (.leaf 623492998) (.leaf 609771771)) (.branch 81 (.leaf 596379580) (.leaf 583307252)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 570545929) (.leaf 558087050)) (.branch 85 (.leaf 545922347) (.leaf 534043825))) (.branch 88 (.branch 87 (.leaf 522443755) (.leaf 511114662)) (.branch 89 (.leaf 500049316) (.leaf 489240721)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 478682105) (.branch 92 (.leaf 468366911) (.leaf 458288793))) (.branch 95 (.branch 94 (.leaf 448441602) (.leaf 438819381)) (.branch 96 (.leaf 429416358) (.leaf 420226937)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 411245694) (.leaf 402467369)) (.branch 100 (.leaf 393886859) (.leaf 385499217))) (.branch 103 (.branch 102 (.leaf 377299637) (.leaf 369283459)) (.branch 104 (.leaf 361446158) (.leaf 353783338))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 346290734) (.leaf 338964199)) (.branch 108 (.leaf 331799707) (.leaf 324793343))) (.branch 111 (.branch 110 (.leaf 317941306) (.leaf 311239896)) (.branch 112 (.leaf 304685520) (.leaf 298274681)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 292003980) (.leaf 285870108)) (.branch 116 (.leaf 279869847) (.leaf 274000067))) (.branch 119 (.branch 118 (.leaf 268257719) (.leaf 262639836)) (.branch 120 (.leaf 257143530) (.leaf 251765989)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 528).prefactor = (2363422137925423/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 528).cutoff/(generalMeanRows 528).c)).2 =
    (188551026898781/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 528).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 528).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 528).q*(generalMeanRows 528).c/2-2 = (261/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable137.value]
    have hcontinuation : (generalMeanRows 528).q*(generalMeanRows 528).cutoff/2-2 = (3278/1557:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable188.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 528).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 528

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 528).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 528).criticalRate j.val*(generalMeanRows 528).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 528).c*(generalMeanRows 528).criticalPoint j.val)).2-
      (generalMeanRows 528).J/2-(generalMeanRows 528).error (generalMeanGrid j.val)+
      (generalMeanRows 528).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 528).c)).2-
      (generalMeanRows 528).J/2-(generalMeanRows 528).error 4 := by
  have he : (generalMeanRows 528).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 528) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 528)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0528

/-! Kernel-checked entropy margins for general spectral rectangle 529. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0529
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5088041962) (.branch 2 (.leaf 4918006721) (.leaf 4755580138))) (.branch 5 (.branch 4 (.leaf 4600324906) (.leaf 4451834761)) (.branch 6 (.leaf 4309731774) (.leaf 4173663929)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4043302963) (.leaf 3918342417)) (.branch 10 (.leaf 3798495891) (.leaf 3683495460))) (.branch 13 (.branch 12 (.leaf 3573090250) (.leaf 3467045138)) (.branch 14 (.leaf 3365139576) (.leaf 3267166523))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3172931462) (.branch 17 (.leaf 3082251506) (.leaf 2994954586))) (.branch 20 (.branch 19 (.leaf 2910878693) (.leaf 2829871195)) (.branch 21 (.leaf 2751788199) (.leaf 2676493970)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2603860393) (.leaf 2533766473)) (.branch 25 (.leaf 2466097877) (.leaf 2400746511))) (.branch 28 (.branch 27 (.leaf 2337610124) (.leaf 2276591940)) (.branch 29 (.leaf 2217600324) (.leaf 2160548464)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2105354077) (.branch 32 (.leaf 2051939137) (.leaf 2000229623))) (.branch 35 (.branch 34 (.leaf 1950155278) (.leaf 1901649391)) (.branch 36 (.leaf 1854648587) (.leaf 1809092638)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1764924283) (.leaf 1722089054)) (.branch 40 (.leaf 1680535122) (.leaf 1640213151))) (.branch 43 (.branch 42 (.leaf 1601076153) (.leaf 1563079365)) (.branch 44 (.leaf 1526180123) (.leaf 1490337746))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1455513435) (.branch 47 (.leaf 1421670165) (.leaf 1388772593))) (.branch 50 (.branch 49 (.leaf 1356786972) (.leaf 1325681059)) (.branch 51 (.leaf 1295424045) (.leaf 1265986473)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1237340174) (.leaf 1209458197)) (.branch 55 (.leaf 1182314748) (.leaf 1155885131))) (.branch 58 (.branch 57 (.leaf 1130145693) (.leaf 1105073774)) (.branch 59 (.leaf 1080647651) (.leaf 1056846500))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1033650346) (.branch 62 (.leaf 1011040023) (.leaf 988997136))) (.branch 65 (.branch 64 (.leaf 967504022) (.leaf 946543717)) (.branch 66 (.leaf 926099921) (.leaf 906156966)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 886699789) (.leaf 867713903)) (.branch 70 (.leaf 849185367) (.leaf 831100764))) (.branch 73 (.branch 72 (.leaf 813447179) (.leaf 796212170)) (.branch 74 (.leaf 779383752) (.leaf 762950375))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 746900903) (.branch 77 (.leaf 731224599) (.leaf 715911103))) (.branch 80 (.branch 79 (.leaf 700950419) (.leaf 686332900)) (.branch 81 (.leaf 672049229) (.leaf 658090408)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 644447743) (.leaf 631112833)) (.branch 85 (.leaf 618077556) (.leaf 605334056))) (.branch 88 (.branch 87 (.leaf 592874738) (.leaf 580692251)) (.branch 89 (.leaf 568779480) (.leaf 557129537)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 545735754) (.branch 92 (.leaf 534591669) (.leaf 523691024))) (.branch 95 (.branch 94 (.leaf 513027752) (.leaf 502595973)) (.branch 96 (.leaf 492389985) (.leaf 482404257)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 472633423) (.leaf 463072278)) (.branch 100 (.leaf 453715769) (.leaf 444558990))) (.branch 103 (.branch 102 (.leaf 435597176) (.leaf 426825702)) (.branch 104 (.leaf 418240071) (.leaf 409835917))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 401608993) (.leaf 393555173)) (.branch 108 (.leaf 385670444) (.leaf 377950905))) (.branch 111 (.branch 110 (.leaf 370392758) (.leaf 362992311)) (.branch 112 (.leaf 355745969) (.leaf 348650236)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 341701707) (.leaf 334897065)) (.branch 116 (.leaf 328233084) (.leaf 321706617))) (.branch 119 (.branch 118 (.leaf 315314603) (.leaf 309054058)) (.branch 120 (.leaf 302922072) (.leaf 296915813)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 529).prefactor = (2353412629648601/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 529).cutoff/(generalMeanRows 529).c)).2 =
    (198328078532551/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 529).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 529).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 529).q*(generalMeanRows 529).c/2-2 = (1237/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable167.value]
    have hcontinuation : (generalMeanRows 529).q*(generalMeanRows 529).cutoff/2-2 = (13166/6201:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable195.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 529).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 529

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 529).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 529).criticalRate j.val*(generalMeanRows 529).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 529).c*(generalMeanRows 529).criticalPoint j.val)).2-
      (generalMeanRows 529).J/2-(generalMeanRows 529).error (generalMeanGrid j.val)+
      (generalMeanRows 529).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 529).c)).2-
      (generalMeanRows 529).J/2-(generalMeanRows 529).error 4 := by
  have he : (generalMeanRows 529).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 529) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 529)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0529

/-! Kernel-checked entropy margins for general spectral rectangle 530. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0530
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5096731420) (.branch 2 (.leaf 4926405790) (.leaf 4763701812))) (.branch 5 (.branch 4 (.leaf 4608181432) (.leaf 4459437692)) (.branch 6 (.leaf 4317092019) (.leaf 4180791795)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4050208195) (.leaf 3925034240)) (.branch 10 (.leaf 3804983037) (.leaf 3689786206))) (.branch 13 (.branch 12 (.leaf 3579192444) (.leaf 3472966226)) (.branch 14 (.leaf 3370886628) (.leaf 3272746255))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3178350257) (.branch 17 (.leaf 3087515436) (.leaf 3000069428))) (.branch 20 (.branch 19 (.leaf 2915849949) (.leaf 2834704104)) (.branch 21 (.leaf 2756487757) (.leaf 2681064940)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2608307317) (.leaf 2538093689)) (.branch 25 (.leaf 2470309528) (.leaf 2404846554))) (.branch 28 (.branch 27 (.leaf 2341602340) (.leaf 2280479948)) (.branch 29 (.leaf 2221387586) (.leaf 2164238291)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2108949642) (.branch 32 (.leaf 2055443479) (.leaf 2003645655))) (.branch 35 (.branch 34 (.leaf 1953485792) (.leaf 1904897065)) (.branch 36 (.leaf 1857815992) (.leaf 1812182242)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1767938455) (.leaf 1725030071)) (.branch 40 (.leaf 1683405173) (.leaf 1643014339))) (.branch 43 (.branch 42 (.leaf 1603810503) (.leaf 1565748823)) (.branch 44 (.leaf 1528786563) (.leaf 1492882974))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1457999190) (.branch 47 (.leaf 1424098121) (.leaf 1391144367))) (.branch 50 (.branch 49 (.leaf 1359104119) (.leaf 1327945083)) (.branch 51 (.leaf 1297636395) (.leaf 1268148550)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1239453328) (.leaf 1211523734)) (.branch 55 (.leaf 1184333928) (.leaf 1157859174))) (.branch 58 (.branch 57 (.leaf 1132075778) (.leaf 1106961040)) (.branch 59 (.leaf 1082493202) (.leaf 1058651403))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1035415634) (.branch 62 (.leaf 1012766697) (.leaf 990686165))) (.branch 65 (.branch 64 (.leaf 969156344) (.leaf 948160243)) (.branch 66 (.leaf 927681532) (.leaf 907704519)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 888214113) (.leaf 869195802)) (.branch 70 (.leaf 850635622) (.leaf 832520135))) (.branch 73 (.branch 72 (.leaf 814836400) (.leaf 797571957)) (.branch 74 (.leaf 780714799) (.leaf 764253356))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 748176475) (.branch 77 (.leaf 732473398) (.leaf 717133750))) (.branch 80 (.branch 79 (.leaf 702147516) (.leaf 687505033)) (.branch 81 (.leaf 673196968) (.leaf 659214308)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 645548344) (.leaf 632190660)) (.branch 85 (.leaf 619133121) (.leaf 606367858))) (.branch 88 (.branch 87 (.leaf 593887262) (.leaf 581683969)) (.branch 89 (.leaf 569750852) (.leaf 558081014)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 546667772) (.branch 92 (.leaf 535504655) (.leaf 524585394))) (.branch 95 (.branch 94 (.leaf 513903911) (.leaf 503454317)) (.branch 96 (.leaf 493230898) (.leaf 483228116)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 473440596) (.leaf 463863122)) (.branch 100 (.leaf 454490634) (.leaf 445318216))) (.branch 103 (.branch 102 (.leaf 436341098) (.leaf 427554643)) (.branch 104 (.leaf 418954350) (.leaf 410535842))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 402294869) (.leaf 394227294)) (.branch 108 (.leaf 386329100) (.leaf 378596377))) (.branch 111 (.branch 110 (.leaf 371025322) (.leaf 363612236)) (.branch 112 (.leaf 356353519) (.leaf 349245668)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 342285272) (.leaf 335469009)) (.branch 116 (.leaf 328793646) (.leaf 322256034))) (.branch 119 (.branch 118 (.leaf 315853104) (.leaf 309581867)) (.branch 120 (.leaf 303439409) (.leaf 297422891)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 530).prefactor = (1178715917043941/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 530).cutoff/(generalMeanRows 530).c)).2 =
    (198328078532551/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 530).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 530).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 530).q*(generalMeanRows 530).c/2-2 = (1237/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable167.value]
    have hcontinuation : (generalMeanRows 530).q*(generalMeanRows 530).cutoff/2-2 = (13166/6201:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable195.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 530).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 530

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 530).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 530).criticalRate j.val*(generalMeanRows 530).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 530).c*(generalMeanRows 530).criticalPoint j.val)).2-
      (generalMeanRows 530).J/2-(generalMeanRows 530).error (generalMeanGrid j.val)+
      (generalMeanRows 530).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 530).c)).2-
      (generalMeanRows 530).J/2-(generalMeanRows 530).error 4 := by
  have he : (generalMeanRows 530).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 530) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 530)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0530

/-! Kernel-checked entropy margins for general spectral rectangle 531. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0531
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5021209249) (.branch 2 (.leaf 4850995096) (.leaf 4688418649))) (.branch 5 (.branch 4 (.leaf 4533041800) (.leaf 4384457491)) (.branch 6 (.leaf 4242287005) (.leaf 4106177546)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3975800075) (.leaf 3850847367)) (.branch 10 (.leaf 3731032262) (.leaf 3616086085))) (.branch 13 (.branch 12 (.leaf 3505757219) (.leaf 3399809807)) (.branch 14 (.leaf 3298022580) (.leaf 3200187782))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3106110192) (.branch 17 (.leaf 3015606234) (.leaf 2928503156))) (.branch 20 (.branch 19 (.leaf 2844638281) (.leaf 2763858319)) (.branch 21 (.leaf 2686018734) (.leaf 2610983156)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2538622850) (.leaf 2468816214)) (.branch 25 (.leaf 2401448320) (.leaf 2336410493))) (.branch 28 (.branch 27 (.leaf 2273599910) (.leaf 2212919242)) (.branch 29 (.leaf 2154276309) (.leaf 2097583770)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2042758824) (.branch 32 (.leaf 1989722942) (.leaf 1938401610))) (.branch 35 (.branch 34 (.leaf 1888724093) (.leaf 1840623213)) (.branch 36 (.leaf 1794035144) (.leaf 1748899216)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1705157737) (.leaf 1662755825)) (.branch 40 (.leaf 1621641246) (.leaf 1581764270))) (.branch 43 (.branch 42 (.leaf 1543077529) (.leaf 1505535889)) (.branch 44 (.leaf 1469096327) (.leaf 1433717817))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1399361221) (.branch 47 (.leaf 1365989189) (.leaf 1333566064))) (.branch 50 (.branch 49 (.leaf 1302057790) (.leaf 1271431834)) (.branch 51 (.leaf 1241657097) (.leaf 1212703849)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1184543655) (.leaf 1157149305)) (.branch 55 (.leaf 1130494758) (.leaf 1104555079))) (.branch 58 (.branch 57 (.leaf 1079306385) (.leaf 1054725792)) (.branch 59 (.leaf 1030791365) (.leaf 1007482073))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 984777743) (.branch 62 (.leaf 962659017) (.leaf 941107318))) (.branch 65 (.branch 64 (.leaf 920104807) (.leaf 899634350)) (.branch 66 (.leaf 879679485) (.leaf 860224389)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 841253849) (.leaf 822753234)) (.branch 70 (.leaf 804708467) (.leaf 787106002))) (.branch 73 (.branch 72 (.leaf 769932795) (.leaf 753176287)) (.branch 74 (.leaf 736824379) (.leaf 720865409))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 705288141) (.branch 77 (.leaf 690081735) (.leaf 675235740))) (.branch 80 (.branch 79 (.leaf 660740071) (.leaf 646584992)) (.branch 81 (.leaf 632761109) (.leaf 619259346)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 606070937) (.leaf 593187413)) (.branch 85 (.leaf 580600586) (.leaf 568302542))) (.branch 88 (.branch 87 (.leaf 556285627) (.leaf 544542435)) (.branch 89 (.leaf 533065803) (.leaf 521848796)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 510884700) (.branch 92 (.leaf 500167014) (.leaf 489689441))) (.branch 95 (.branch 94 (.leaf 479445879) (.leaf 469430416)) (.branch 96 (.leaf 459637319) (.leaf 450061031)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 440696162) (.leaf 431537483)) (.branch 100 (.leaf 422579921) (.leaf 413818552))) (.branch 103 (.branch 102 (.leaf 405248596) (.leaf 396865414)) (.branch 104 (.leaf 388664497) (.leaf 380641469))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 372792075) (.leaf 365112184)) (.branch 108 (.leaf 357597777) (.leaf 350244949))) (.branch 111 (.branch 110 (.leaf 343049902) (.leaf 336008944)) (.branch 112 (.leaf 329118482) (.leaf 322375021)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 315775161) (.leaf 309315591)) (.branch 116 (.leaf 302993091) (.leaf 296804523))) (.branch 119 (.branch 118 (.leaf 290746834) (.leaf 284817048)) (.branch 120 (.leaf 279012270) (.leaf 273329677)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 531).prefactor = (4716138773218049/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 531).cutoff/(generalMeanRows 531).c)).2 =
    (77514441126477/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 531).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 531).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 531).q*(generalMeanRows 531).c/2-2 = (1271/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable168.value]
    have hcontinuation : (generalMeanRows 531).q*(generalMeanRows 531).cutoff/2-2 = (6574/3105:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable192.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 531).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 531

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 531).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 531).criticalRate j.val*(generalMeanRows 531).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 531).c*(generalMeanRows 531).criticalPoint j.val)).2-
      (generalMeanRows 531).J/2-(generalMeanRows 531).error (generalMeanGrid j.val)+
      (generalMeanRows 531).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 531).c)).2-
      (generalMeanRows 531).J/2-(generalMeanRows 531).error 4 := by
  have he : (generalMeanRows 531).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 531) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 531)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0531

/-! Kernel-checked entropy margins for general spectral rectangle 532. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0532
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5029819466) (.branch 2 (.leaf 4859313436) (.leaf 4696458207))) (.branch 5 (.branch 4 (.leaf 4540814922) (.leaf 4391975826)) (.branch 6 (.leaf 4249561550) (.leaf 4113218694)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3982617656) (.leaf 3857450683)) (.branch 10 (.leaf 3737430123) (.leaf 3622286840))) (.branch 13 (.branch 12 (.leaf 3511768785) (.leaf 3405639698)) (.branch 14 (.leaf 3303677929) (.leaf 3205675367))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3111436455) (.branch 17 (.leaf 3020777304) (.leaf 2933524864))) (.branch 20 (.branch 19 (.leaf 2849516180) (.leaf 2768597700)) (.branch 21 (.leaf 2690624637) (.leaf 2615460391)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2542976004) (.leaf 2473049665)) (.branch 25 (.leaf 2405566251) (.leaf 2340416898))) (.branch 28 (.branch 27 (.leaf 2277498610) (.leaf 2216713888)) (.branch 29 (.leaf 2157970397) (.leaf 2101180643)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2046261684) (.branch 32 (.leaf 1993134858) (.leaf 1941725522))) (.branch 35 (.branch 34 (.leaf 1891962820) (.leaf 1843779458)) (.branch 36 (.leaf 1797111501) (.leaf 1751898175)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1708081690) (.leaf 1665607068)) (.branch 40 (.leaf 1624421987) (.leaf 1584476631))) (.branch 43 (.branch 42 (.leaf 1545723551) (.leaf 1508117536)) (.branch 44 (.leaf 1471615488) (.leaf 1436176312))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1401760803) (.branch 47 (.leaf 1368331546) (.leaf 1335852822))) (.branch 50 (.branch 49 (.leaf 1304290520) (.leaf 1273612046)) (.branch 51 (.leaf 1243786253) (.leaf 1214783357)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1186574874) (.leaf 1159133549)) (.branch 55 (.leaf 1132433296) (.leaf 1106449136))) (.branch 58 (.branch 57 (.leaf 1081157147) (.leaf 1056534404)) (.branch 59 (.leaf 1032558935) (.leaf 1009209673))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 986466409) (.branch 62 (.leaf 964309756) (.leaf 942721100))) (.branch 65 (.branch 64 (.leaf 921682575) (.leaf 901177016)) (.branch 66 (.leaf 881187933) (.leaf 861699475)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 842696405) (.leaf 824164066)) (.branch 70 (.leaf 806088357) (.leaf 788455707))) (.branch 73 (.branch 72 (.leaf 771253053) (.leaf 754467811)) (.branch 74 (.leaf 738087863) (.leaf 722101528))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 706497547) (.branch 77 (.leaf 691265067) (.leaf 676393614))) (.branch 80 (.branch 79 (.leaf 661873088) (.leaf 647693737)) (.branch 81 (.leaf 633846148) (.leaf 620321233)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 607110209) (.leaf 594204592)) (.branch 85 (.leaf 581596182) (.leaf 569277050))) (.branch 88 (.branch 87 (.leaf 557239528) (.leaf 545476200)) (.branch 89 (.leaf 533979888) (.leaf 522743646)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 511760750) (.branch 92 (.leaf 501024685) (.leaf 490529146))) (.branch 95 (.branch 94 (.leaf 480268019) (.leaf 470235381)) (.branch 96 (.leaf 460425491) (.leaf 450832782)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 441451854) (.leaf 432277470)) (.branch 100 (.leaf 423304548) (.leaf 414528155))) (.branch 103 (.branch 102 (.leaf 405943504) (.leaf 397545946)) (.branch 104 (.leaf 389330967) (.leaf 381294181))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 373431328) (.leaf 365738267)) (.branch 108 (.leaf 358210975) (.leaf 350845538))) (.branch 111 (.branch 110 (.leaf 343638154) (.leaf 336585122)) (.branch 112 (.leaf 329682844) (.leaf 322927820)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 316316643) (.leaf 309845996)) (.branch 116 (.leaf 303512654) (.leaf 297313475))) (.branch 119 (.branch 118 (.leaf 291245398) (.leaf 285305444)) (.branch 120 (.leaf 279490712) (.leaf 273798374)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 532).prefactor = (472422586479489/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 532).cutoff/(generalMeanRows 532).c)).2 =
    (77514441126477/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 532).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 532).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 532).q*(generalMeanRows 532).c/2-2 = (1271/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable168.value]
    have hcontinuation : (generalMeanRows 532).q*(generalMeanRows 532).cutoff/2-2 = (6574/3105:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable192.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 532).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 532

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 532).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 532).criticalRate j.val*(generalMeanRows 532).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 532).c*(generalMeanRows 532).criticalPoint j.val)).2-
      (generalMeanRows 532).J/2-(generalMeanRows 532).error (generalMeanGrid j.val)+
      (generalMeanRows 532).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 532).c)).2-
      (generalMeanRows 532).J/2-(generalMeanRows 532).error 4 := by
  have he : (generalMeanRows 532).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 532) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 532)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0532

/-! Kernel-checked entropy margins for general spectral rectangle 533. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0533
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5047084219) (.branch 2 (.leaf 4875992930) (.leaf 4712578705))) (.branch 5 (.branch 4 (.leaf 4556401178) (.leaf 4407051194)) (.branch 6 (.leaf 4264148084) (.leaf 4127337234)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3996287910) (.leaf 3870691304)) (.branch 10 (.leaf 3750258776) (.leaf 3634720266))) (.branch 13 (.branch 12 (.leaf 3523822860) (.leaf 3417329487)) (.branch 14 (.leaf 3315017737) (.leaf 3216678782))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3122116398) (.branch 17 (.leaf 3031146061) (.leaf 2943594128))) (.branch 20 (.branch 19 (.leaf 2859297087) (.leaf 2778100855)) (.branch 21 (.leaf 2699860151) (.leaf 2624437905)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2551704717) (.leaf 2481538358)) (.branch 25 (.leaf 2413823308) (.leaf 2348450332))) (.branch 28 (.branch 27 (.leaf 2285316078) (.leaf 2224322714)) (.branch 29 (.leaf 2165377586) (.leaf 2108392903)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2053285436) (.branch 32 (.leaf 1999976253) (.leaf 1948390455))) (.branch 35 (.branch 34 (.leaf 1898456944) (.leaf 1850108193)) (.branch 36 (.leaf 1803280050) (.leaf 1757911530)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1713944646) (.leaf 1671324231)) (.branch 40 (.leaf 1629997783) (.leaf 1589915315))) (.branch 43 (.branch 42 (.leaf 1551029216) (.leaf 1513294119)) (.branch 44 (.leaf 1476666779) (.leaf 1441105958))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1406572318) (.branch 47 (.leaf 1373028316) (.leaf 1340438110))) (.branch 50 (.branch 49 (.leaf 1308767470) (.leaf 1277983694)) (.branch 51 (.leaf 1248055524) (.leaf 1218953076)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1190647768) (.leaf 1163112252)) (.branch 55 (.leaf 1136320350) (.leaf 1110247001))) (.branch 58 (.branch 57 (.leaf 1084868197) (.leaf 1060160937)) (.branch 59 (.leaf 1036103173) (.leaf 1012673765))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 989852435) (.branch 62 (.leaf 967619729) (.leaf 945956971))) (.branch 65 (.branch 64 (.leaf 924846232) (.leaf 904270288)) (.branch 66 (.leaf 884212592) (.leaf 864657241)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 845588944) (.leaf 826992992)) (.branch 70 (.leaf 808855239) (.leaf 791162066))) (.branch 73 (.branch 72 (.leaf 773900363) (.leaf 757057507)) (.branch 74 (.leaf 740621334) (.leaf 724580126))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 708922586) (.branch 77 (.leaf 693637820) (.leaf 678715321))) (.branch 80 (.branch 79 (.leaf 664144954) (.leaf 649916932)) (.branch 81 (.leaf 636021813) (.leaf 622450473)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 609194102) (.leaf 596244188)) (.branch 85 (.leaf 583592499) (.leaf 571231082))) (.branch 88 (.branch 87 (.leaf 559152242) (.leaf 547348536)) (.branch 89 (.leaf 535812763) (.leaf 524537953)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 513517358) (.branch 92 (.leaf 502744442) (.leaf 492212877))) (.branch 95 (.branch 94 (.leaf 481916529) (.leaf 471849454)) (.branch 96 (.leaf 462005892) (.leaf 452380257)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 442967129) (.leaf 433761254)) (.branch 100 (.leaf 424757532) (.leaf 415951015))) (.branch 103 (.branch 102 (.leaf 407336897) (.leaf 398910515)) (.branch 104 (.leaf 390667338) (.leaf 382602966))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 374713123) (.leaf 366993656)) (.branch 108 (.leaf 359440526) (.leaf 352049808))) (.branch 111 (.branch 110 (.leaf 344817685) (.leaf 337740443)) (.branch 112 (.leaf 330814474) (.leaf 324036263)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 317402393) (.leaf 310909536)) (.branch 116 (.leaf 304554455) (.leaf 298333997))) (.branch 119 (.branch 118 (.leaf 292245091) (.leaf 286284749)) (.branch 120 (.leaf 280450058) (.leaf 274738181)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 533).prefactor = (189617666969017/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 533).cutoff/(generalMeanRows 533).c)).2 =
    (77514441126477/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 533).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 533).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 533).q*(generalMeanRows 533).c/2-2 = (1271/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable168.value]
    have hcontinuation : (generalMeanRows 533).q*(generalMeanRows 533).cutoff/2-2 = (6574/3105:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable192.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 533).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 533

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 533).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 533).criticalRate j.val*(generalMeanRows 533).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 533).c*(generalMeanRows 533).criticalPoint j.val)).2-
      (generalMeanRows 533).J/2-(generalMeanRows 533).error (generalMeanGrid j.val)+
      (generalMeanRows 533).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 533).c)).2-
      (generalMeanRows 533).J/2-(generalMeanRows 533).error 4 := by
  have he : (generalMeanRows 533).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 533) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 533)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0533

/-! Kernel-checked entropy margins for general spectral rectangle 534. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0534
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5039784115) (.branch 2 (.leaf 4868958880) (.leaf 4705791633))) (.branch 5 (.branch 4 (.leaf 4549843611) (.leaf 4400707124)) (.branch 6 (.leaf 4258002846) (.leaf 4121377394)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3990501161) (.leaf 3865066373)) (.branch 10 (.leaf 3744785335) (.leaf 3629388858))) (.branch 13 (.branch 12 (.leaf 3518624823) (.leaf 3412256889)) (.branch 14 (.leaf 3310063314) (.leaf 3211835884))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3117378935) (.branch 17 (.leaf 3026508458) (.leaf 2939051283))) (.branch 20 (.branch 19 (.leaf 2854844326) (.leaf 2773733902)) (.branch 21 (.leaf 2695575090) (.leaf 2620231151)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2547572985) (.leaf 2477478642)) (.branch 25 (.leaf 2409832853) (.leaf 2344526612))) (.branch 28 (.branch 27 (.leaf 2281456779) (.leaf 2220525712)) (.branch 29 (.leaf 2161640932) (.leaf 2104714806)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2049664252) (.branch 32 (.leaf 1996410465) (.leaf 1944878669))) (.branch 35 (.branch 34 (.leaf 1894997871) (.leaf 1846700646)) (.branch 36 (.leaf 1799922926) (.leaf 1754603810)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1710685381) (.leaf 1668112538)) (.branch 40 (.leaf 1626832839) (.leaf 1586796349))) (.branch 43 (.branch 42 (.leaf 1547955505) (.leaf 1510264982)) (.branch 44 (.leaf 1473681573) (.leaf 1438164076))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1403673181) (.branch 47 (.leaf 1370171372) (.leaf 1337622833))) (.branch 50 (.branch 49 (.leaf 1305993354) (.leaf 1275250251)) (.branch 51 (.leaf 1245362284) (.leaf 1216299583)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1188033578) (.leaf 1160536933)) (.branch 55 (.leaf 1133783479) (.leaf 1107748163))) (.branch 58 (.branch 57 (.leaf 1082406985) (.leaf 1057736950)) (.branch 59 (.leaf 1033716014) (.leaf 1010323042))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 987537762) (.branch 62 (.leaf 965340719) (.leaf 943713242))) (.branch 65 (.branch 64 (.leaf 922637403) (.leaf 902095981)) (.branch 66 (.leaf 882072431) (.leaf 862550849)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 843515945) (.leaf 824953014)) (.branch 70 (.leaf 806847906) (.leaf 789187005))) (.branch 73 (.branch 72 (.leaf 771957202) (.leaf 755145872)) (.branch 74 (.leaf 738740855) (.leaf 722730430))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 707103301) (.branch 77 (.leaf 691848576) (.leaf 676955747))) (.branch 80 (.branch 79 (.leaf 662414680) (.leaf 648215589)) (.branch 81 (.leaf 634349032) (.leaf 620805886)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 607577343) (.leaf 594654890)) (.branch 85 (.leaf 582030298) (.leaf 569695613))) (.branch 88 (.branch 87 (.leaf 557643143) (.leaf 545865447)) (.branch 89 (.leaf 534355324) (.leaf 523105806)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 512110147) (.branch 92 (.leaf 501361813) (.leaf 490854477))) (.branch 95 (.branch 94 (.leaf 480582008) (.leaf 470538465)) (.branch 96 (.leaf 460718088) (.leaf 451115294)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 441724668) (.leaf 432540955)) (.branch 100 (.leaf 423559060) (.leaf 414774036))) (.branch 103 (.branch 102 (.leaf 406181081) (.leaf 397775534)) (.branch 104 (.leaf 389552868) (.leaf 381508685))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 373638713) (.leaf 365938800)) (.branch 108 (.leaf 358404912) (.leaf 351033127))) (.branch 111 (.branch 110 (.leaf 343819630) (.leaf 336760712)) (.branch 112 (.leaf 329852767) (.leaf 323092285)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 316475849) (.leaf 310000139)) (.branch 116 (.leaf 303661917) (.leaf 297458036))) (.branch 119 (.branch 118 (.leaf 291385428) (.leaf 285441108)) (.branch 120 (.leaf 279622167) (.leaf 273925771)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 534).prefactor = (29534595760537/6250000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 534).cutoff/(generalMeanRows 534).c)).2 =
    (193061989728009/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 534).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 534).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 534).q*(generalMeanRows 534).c/2-2 = (1271/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable168.value]
    have hcontinuation : (generalMeanRows 534).q*(generalMeanRows 534).cutoff/2-2 = (13130/6219:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable196.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 534).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 534

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 534).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 534).criticalRate j.val*(generalMeanRows 534).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 534).c*(generalMeanRows 534).criticalPoint j.val)).2-
      (generalMeanRows 534).J/2-(generalMeanRows 534).error (generalMeanGrid j.val)+
      (generalMeanRows 534).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 534).c)).2-
      (generalMeanRows 534).J/2-(generalMeanRows 534).error 4 := by
  have he : (generalMeanRows 534).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 534) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 534)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0534

/-! Kernel-checked entropy margins for general spectral rectangle 535. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0535
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4964513507) (.branch 2 (.leaf 4793860623) (.leaf 4630887302))) (.branch 5 (.branch 4 (.leaf 4475153845) (.leaf 4326251668)) (.branch 6 (.leaf 4183800583) (.leaf 4047446377)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3916858646) (.leaf 3791728845)) (.branch 10 (.leaf 3671768538) (.leaf 3556707819))) (.branch 13 (.branch 12 (.leaf 3446293876) (.leaf 3340289699)) (.branch 14 (.leaf 3238472898) (.leaf 3140634636))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3046578640) (.branch 17 (.leaf 2956120317) (.leaf 2869085928))) (.branch 20 (.branch 19 (.leaf 2785311841) (.leaf 2704643836)) (.branch 21 (.leaf 2626936479) (.leaf 2552052529)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2479862404) (.leaf 2410243684)) (.branch 25 (.leaf 2343080646) (.leaf 2278263845))) (.branch 28 (.branch 27 (.leaf 2215689712) (.leaf 2155260196)) (.branch 29 (.leaf 2096882415) (.leaf 2040468350)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1985934543) (.branch 32 (.leaf 1933201828) (.leaf 1882195075))) (.branch 35 (.branch 34 (.leaf 1832842952) (.leaf 1785077706)) (.branch 36 (.leaf 1738834949) (.leaf 1694053474)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1650675065) (.leaf 1608644334)) (.branch 40 (.leaf 1567908561) (.leaf 1528417541))) (.branch 43 (.branch 42 (.leaf 1490123452) (.leaf 1452980720)) (.branch 44 (.leaf 1416945896) (.leaf 1381977544))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1348036129) (.branch 47 (.leaf 1315083918) (.leaf 1283084887))) (.branch 50 (.branch 49 (.leaf 1252004624) (.leaf 1221810251)) (.branch 51 (.leaf 1192470341) (.leaf 1163954846)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1136235023) (.leaf 1109283367)) (.branch 55 (.leaf 1083073554) (.leaf 1057580376))) (.branch 58 (.branch 57 (.leaf 1032779686) (.leaf 1008648348)) (.branch 59 (.leaf 985164184) (.leaf 962305929))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 940053186) (.branch 62 (.leaf 918386385) (.leaf 897286740))) (.branch 65 (.branch 64 (.leaf 876736214) (.leaf 856717484)) (.branch 66 (.leaf 837213907) (.leaf 818209485)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 799688840) (.leaf 781637180)) (.branch 70 (.leaf 764040278) (.leaf 746884439))) (.branch 73 (.branch 72 (.leaf 730156483) (.leaf 713843716)) (.branch 74 (.leaf 697933915) (.leaf 682415297))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 667276509) (.branch 77 (.leaf 652506605) (.leaf 638095028))) (.branch 80 (.branch 79 (.leaf 624031594) (.leaf 610306477)) (.branch 81 (.leaf 596910190) (.leaf 583833576)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 571067788) (.leaf 558604282)) (.branch 85 (.leaf 546434800) (.leaf 534551361))) (.branch 88 (.branch 87 (.leaf 522946247) (.leaf 511611995)) (.branch 89 (.leaf 500541386) (.leaf 489727432)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 479163372) (.branch 92 (.leaf 468842661) (.leaf 458758957))) (.branch 95 (.branch 94 (.leaf 448906122) (.leaf 439278207)) (.branch 96 (.leaf 429869447) (.leaf 420674253)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 411687209) (.leaf 402903061)) (.branch 100 (.leaf 394316712) (.leaf 385923219))) (.branch 103 (.branch 102 (.leaf 377717785) (.leaf 369695752)) (.branch 104 (.leaf 361852600) (.leaf 354183941))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 346685510) (.leaf 339353166)) (.branch 108 (.leaf 332182887) (.leaf 325170763))) (.branch 111 (.branch 110 (.leaf 318312992) (.leaf 311605882)) (.branch 112 (.leaf 305045839) (.leaf 298629371)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 292353080) (.leaf 286213662)) (.branch 116 (.leaf 280207899) (.leaf 274332663))) (.branch 119 (.branch 118 (.leaf 268584907) (.leaf 262961666)) (.branch 120 (.leaf 257460054) (.leaf 252077259)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 535).prefactor = (4733671595644497/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 535).cutoff/(generalMeanRows 535).c)).2 =
    (189274092823781/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 535).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 535).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 535).q*(generalMeanRows 535).c/2-2 = (261/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable137.value]
    have hcontinuation : (generalMeanRows 535).q*(generalMeanRows 535).cutoff/2-2 = (13130/6219:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable196.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 535).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 535

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 535).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 535).criticalRate j.val*(generalMeanRows 535).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 535).c*(generalMeanRows 535).criticalPoint j.val)).2-
      (generalMeanRows 535).J/2-(generalMeanRows 535).error (generalMeanGrid j.val)+
      (generalMeanRows 535).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 535).c)).2-
      (generalMeanRows 535).J/2-(generalMeanRows 535).error 4 := by
  have he : (generalMeanRows 535).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 535) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 535)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0535

/-! Kernel-checked entropy margins for general spectral rectangle 536. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0536
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4974495455) (.branch 2 (.leaf 4803523145) (.leaf 4640237585))) (.branch 5 (.branch 4 (.leaf 4484199171) (.leaf 4334999382)) (.branch 6 (.leaf 4192258068) (.leaf 4055621035)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3924757871) (.leaf 3799360010)) (.branch 10 (.leaf 3679138976) (.leaf 3563824804))) (.branch 13 (.branch 12 (.leaf 3453164614) (.leaf 3346921316)) (.branch 14 (.leaf 3244872428) (.leaf 3146809010))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3052534681) (.branch 17 (.leaf 2961864731) (.leaf 2874625299))) (.branch 20 (.branch 19 (.leaf 2790652624) (.leaf 2709792357)) (.branch 21 (.leaf 2631898927) (.leaf 2556834955)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2484470721) (.leaf 2414683661)) (.branch 25 (.leaf 2347357911) (.leaf 2282383882))) (.branch 28 (.branch 27 (.leaf 2219657864) (.leaf 2159081661)) (.branch 29 (.leaf 2100562251) (.leaf 2044011472)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1989345727) (.branch 32 (.leaf 1936485712) (.leaf 1885356161))) (.branch 35 (.branch 34 (.leaf 1835885606) (.leaf 1788006162)) (.branch 36 (.leaf 1741653311) (.leaf 1696765717)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1653285040) (.leaf 1611155767)) (.branch 40 (.leaf 1570325059) (.leaf 1530742593))) (.branch 43 (.branch 42 (.leaf 1492360432) (.leaf 1455132889)) (.branch 44 (.leaf 1419016406) (.leaf 1383969440))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1349952351) (.branch 47 (.leaf 1316927308) (.leaf 1284858184))) (.branch 50 (.branch 49 (.leaf 1253710475) (.leaf 1223451208)) (.branch 51 (.leaf 1194048867) (.leaf 1165473315)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1137695724) (.leaf 1110688508)) (.branch 55 (.leaf 1084425262) (.leaf 1058880699))) (.branch 58 (.branch 57 (.leaf 1034030600) (.leaf 1009851754)) (.branch 59 (.leaf 986321915) (.leaf 963419749))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 941124793) (.branch 62 (.leaf 919417413) (.leaf 898278763))) (.branch 65 (.branch 64 (.leaf 877690746) (.leaf 857635982)) (.branch 66 (.leaf 838097772) (.leaf 819060066)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 800507433) (.leaf 782425032)) (.branch 70 (.leaf 764798588) (.leaf 747614361))) (.branch 73 (.branch 72 (.leaf 730859124) (.leaf 714520144)) (.branch 74 (.leaf 698585152) (.leaf 683042328))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 667880281) (.branch 77 (.leaf 653088027) (.leaf 638654973))) (.branch 80 (.branch 79 (.leaf 624570902) (.leaf 610825953)) (.branch 81 (.leaf 597410609) (.leaf 584315682)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 571532297) (.leaf 559051879)) (.branch 85 (.leaf 546866145) (.leaf 534967087))) (.branch 88 (.branch 87 (.leaf 523346963) (.leaf 511998284)) (.branch 89 (.leaf 500913809) (.leaf 490086527)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 479509657) (.branch 92 (.leaf 469176631) (.leaf 459081090))) (.branch 95 (.branch 94 (.leaf 449216875) (.leaf 439578018)) (.branch 96 (.leaf 430158739) (.leaf 420953431)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 411956661) (.leaf 403163160)) (.branch 100 (.leaf 394567817) (.leaf 386165673))) (.branch 103 (.branch 102 (.leaf 377951918) (.leaf 369921882)) (.branch 104 (.leaf 362071031) (.leaf 354394964))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 346889406) (.leaf 339550205)) (.branch 108 (.leaf 332373327) (.leaf 325354851))) (.branch 111 (.branch 110 (.leaf 318490967) (.leaf 311777972)) (.branch 112 (.leaf 305212265) (.leaf 298790343)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 292508800) (.leaf 286364324)) (.branch 116 (.leaf 280353690) (.leaf 274473762))) (.branch 119 (.branch 118 (.leaf 268721487) (.leaf 263093891)) (.branch 120 (.leaf 257588084) (.leaf 252201245)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 536).prefactor = (4735016112236691/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 536).cutoff/(generalMeanRows 536).c)).2 =
    (188551026898781/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 536).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 536).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 536).q*(generalMeanRows 536).c/2-2 = (261/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable137.value]
    have hcontinuation : (generalMeanRows 536).q*(generalMeanRows 536).cutoff/2-2 = (3278/1557:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable188.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 536).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 536

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 536).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 536).criticalRate j.val*(generalMeanRows 536).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 536).c*(generalMeanRows 536).criticalPoint j.val)).2-
      (generalMeanRows 536).J/2-(generalMeanRows 536).error (generalMeanGrid j.val)+
      (generalMeanRows 536).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 536).c)).2-
      (generalMeanRows 536).J/2-(generalMeanRows 536).error 4 := by
  have he : (generalMeanRows 536).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 536) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 536)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0536

/-! Kernel-checked entropy margins for general spectral rectangle 537. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0537
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4983095434) (.branch 2 (.leaf 4811827545) (.leaf 4648259695))) (.branch 5 (.branch 4 (.leaf 4491951519) (.leaf 4342493791)) (.branch 6 (.leaf 4199505704) (.leaf 4062632451)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3931543049) (.leaf 3805928399)) (.branch 10 (.leaf 3685499524) (.leaf 3569985995))) (.branch 13 (.branch 12 (.leaf 3459134495) (.leaf 3352707522)) (.branch 14 (.leaf 3250482210) (.leaf 3152249258))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3057811947) (.branch 17 (.leaf 2966985245) (.leaf 2879594992))) (.branch 20 (.branch 19 (.leaf 2795477144) (.leaf 2714477085)) (.branch 21 (.leaf 2636448991) (.leaf 2561255248)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2488765909) (.leaf 2418858200)) (.branch 25 (.leaf 2351416057) (.leaf 2286329700))) (.branch 28 (.branch 27 (.leaf 2223495241) (.leaf 2162814312)) (.branch 29 (.leaf 2104193733) (.leaf 2047545188)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1992784936) (.branch 32 (.leaf 1939833536) (.leaf 1888615592))) (.branch 35 (.branch 34 (.leaf 1839059512) (.leaf 1791097293)) (.branch 36 (.leaf 1744664306) (.leaf 1699699110)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1656143263) (.leaf 1613941157)) (.branch 40 (.leaf 1573039859) (.leaf 1533388963))) (.branch 43 (.branch 42 (.leaf 1494940446) (.leaf 1457648544)) (.branch 44 (.leaf 1421469622) (.leaf 1386362066))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1352286168) (.branch 47 (.leaf 1319204031) (.leaf 1287079466))) (.branch 50 (.branch 49 (.leaf 1255877908) (.leaf 1225566328)) (.branch 51 (.leaf 1196113156) (.leaf 1167488202)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1139662589) (.leaf 1112608682)) (.branch 55 (.leaf 1086300032) (.leaf 1060711307))) (.branch 58 (.branch 57 (.leaf 1035818247) (.leaf 1011597601)) (.branch 59 (.leaf 988027083) (.leaf 965085323))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 942751823) (.branch 62 (.leaf 921006915) (.leaf 899831720))) (.branch 65 (.branch 64 (.leaf 879208110) (.leaf 859118676)) (.branch 66 (.leaf 839546688) (.leaf 820476069)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 801891361) (.leaf 783777700)) (.branch 70 (.leaf 766120783) (.leaf 748906847))) (.branch 73 (.branch 72 (.leaf 732122644) (.leaf 715755417)) (.branch 74 (.leaf 699792876) (.leaf 684223182))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 669034922) (.branch 77 (.leaf 654217095) (.leaf 639759089))) (.branch 80 (.branch 79 (.leaf 625650669) (.leaf 611881958)) (.branch 81 (.leaf 598443422) (.leaf 585325856)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 572520370) (.leaf 560018376)) (.branch 85 (.leaf 547811575) (.leaf 535891946))) (.branch 88 (.branch 87 (.leaf 524251733) (.leaf 512883434)) (.branch 89 (.leaf 501779796) (.leaf 490933796)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 480338640) (.branch 92 (.leaf 469987750) (.leaf 459874756))) (.branch 95 (.branch 94 (.leaf 449993487) (.leaf 440337967)) (.branch 96 (.leaf 430902403) (.leaf 421681181)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 412668858) (.leaf 403860154)) (.branch 100 (.leaf 395249951) (.leaf 386833282))) (.branch 103 (.branch 102 (.leaf 378605327) (.leaf 370561408)) (.branch 104 (.leaf 362696985) (.leaf 355007647))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 347489114) (.leaf 340137224)) (.branch 108 (.leaf 332947939) (.leaf 325917329))) (.branch 111 (.branch 110 (.leaf 319041579) (.leaf 312316978)) (.branch 112 (.leaf 305739920) (.leaf 299306896)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 293014494) (.leaf 286859395)) (.branch 116 (.leaf 280838370) (.leaf 274948276))) (.branch 119 (.branch 118 (.leaf 269186056) (.leaf 263548732)) (.branch 120 (.leaf 258033406) (.leaf 252637255)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 537).prefactor = (2371601038105419/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 537).cutoff/(generalMeanRows 537).c)).2 =
    (188551026898781/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 537).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 537).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 537).q*(generalMeanRows 537).c/2-2 = (261/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable137.value]
    have hcontinuation : (generalMeanRows 537).q*(generalMeanRows 537).cutoff/2-2 = (3278/1557:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable188.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 537).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 537

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 537).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 537).criticalRate j.val*(generalMeanRows 537).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 537).c*(generalMeanRows 537).criticalPoint j.val)).2-
      (generalMeanRows 537).J/2-(generalMeanRows 537).error (generalMeanGrid j.val)+
      (generalMeanRows 537).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 537).c)).2-
      (generalMeanRows 537).J/2-(generalMeanRows 537).error 4 := by
  have he : (generalMeanRows 537).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 537) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 537)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0537

/-! Kernel-checked entropy margins for general spectral rectangle 538. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0538
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4917737011) (.branch 2 (.leaf 4746378362) (.leaf 4582754296))) (.branch 5 (.branch 4 (.leaf 4426422720) (.leaf 4276972770)) (.branch 6 (.leaf 4134022092) (.leaf 3997214408)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3866217341) (.leaf 3740720464)) (.branch 10 (.leaf 3620433540) (.leaf 3505084933))) (.branch 13 (.branch 12 (.leaf 3394420180) (.leaf 3288200684)) (.branch 14 (.leaf 3186202532) (.leaf 3088215423))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2994041680) (.branch 17 (.leaf 2903495357) (.leaf 2816401415))) (.branch 20 (.branch 19 (.leaf 2732594969) (.leaf 2651920598)) (.branch 21 (.leaf 2574231704) (.leaf 2499389932)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2427264622) (.leaf 2357732317)) (.branch 25 (.leaf 2290676297) (.leaf 2225986150))) (.branch 28 (.branch 27 (.leaf 2163557382) (.leaf 2103291045)) (.branch 29 (.leaf 2045093397) (.leaf 1988875584)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1934553349) (.branch 32 (.leaf 1882046753) (.leaf 1831279920))) (.branch 35 (.branch 34 (.leaf 1782180802) (.leaf 1734680952)) (.branch 36 (.leaf 1688715316) (.leaf 1644222043)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1601142300) (.leaf 1559420101)) (.branch 40 (.leaf 1519002149) (.leaf 1479837689))) (.branch 43 (.branch 42 (.leaf 1441878364) (.leaf 1405078085)) (.branch 44 (.leaf 1369392910) (.leaf 1334780927))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1301202141) (.branch 47 (.leaf 1268618382) (.leaf 1236993197))) (.branch 50 (.branch 49 (.leaf 1206291769) (.leaf 1176480827)) (.branch 51 (.leaf 1147528567) (.leaf 1119404577)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1092079765) (.leaf 1065526295)) (.branch 55 (.leaf 1039717517) (.leaf 1014627915))) (.branch 58 (.branch 57 (.leaf 990233048) (.leaf 966509492)) (.branch 59 (.leaf 943434799) (.leaf 920987441))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 899146771) (.branch 62 (.leaf 877892976) (.leaf 857207041))) (.branch 65 (.branch 64 (.leaf 837070709) (.leaf 817466446)) (.branch 66 (.leaf 798377405) (.leaf 779787396)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 761680855) (.leaf 744042816)) (.branch 70 (.leaf 726858880) (.leaf 710115194))) (.branch 73 (.branch 72 (.leaf 693798423) (.leaf 677895728)) (.branch 74 (.leaf 662394744) (.leaf 647283557))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 632550687) (.branch 77 (.leaf 618185068) (.leaf 604176029))) (.branch 80 (.branch 79 (.leaf 590513278) (.leaf 577186885)) (.branch 81 (.leaf 564187266) (.leaf 551505171)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 539131668) (.leaf 527058129)) (.branch 85 (.leaf 515276218) (.leaf 503777881))) (.branch 88 (.branch 87 (.leaf 492555332) (.leaf 481601042)) (.branch 89 (.leaf 470907731) (.leaf 460468356)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 450276101) (.branch 92 (.leaf 440324371) (.leaf 430606780))) (.branch 95 (.branch 94 (.leaf 421117145) (.leaf 411849477)) (.branch 96 (.leaf 402797976) (.leaf 393957020)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 385321160) (.leaf 376885115)) (.branch 100 (.leaf 368643762) (.leaf 360592136))) (.branch 103 (.branch 102 (.leaf 352725419) (.leaf 345038934)) (.branch 104 (.leaf 337528147) (.leaf 330188653))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 323016178) (.leaf 316006571)) (.branch 108 (.leaf 309155801) (.leaf 302459951))) (.branch 111 (.branch 110 (.leaf 295915217) (.leaf 289517902)) (.branch 112 (.leaf 283264413) (.leaf 277151257)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 271175038) (.leaf 265332455)) (.branch 116 (.leaf 259620295) (.leaf 254035435))) (.branch 119 (.branch 118 (.leaf 248574836) (.leaf 243235541)) (.branch 120 (.leaf 238014672) (.leaf 232909430)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 538).prefactor = (2379808242331093/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 538).cutoff/(generalMeanRows 538).c)).2 =
    (73916644276707/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 538).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 538).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 538).q*(generalMeanRows 538).c/2-2 = (1339/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable194.value]
    have hcontinuation : (generalMeanRows 538).q*(generalMeanRows 538).cutoff/2-2 = (3278/1557:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable188.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 538).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 538

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 538).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 538).criticalRate j.val*(generalMeanRows 538).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 538).c*(generalMeanRows 538).criticalPoint j.val)).2-
      (generalMeanRows 538).J/2-(generalMeanRows 538).error (generalMeanGrid j.val)+
      (generalMeanRows 538).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 538).c)).2-
      (generalMeanRows 538).J/2-(generalMeanRows 538).error 4 := by
  have he : (generalMeanRows 538).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 538) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 538)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0538

/-! Kernel-checked entropy margins for general spectral rectangle 539. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0539
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4903692746) (.branch 2 (.leaf 4732882058) (.leaf 4569766754))) (.branch 5 (.branch 4 (.leaf 4413907979) (.leaf 4264897838)) (.branch 6 (.leaf 4122356698) (.leaf 3985930775)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3855289984) (.leaf 3730125994)) (.branch 10 (.leaf 3610150497) (.leaf 3495093628))) (.branch 13 (.branch 12 (.leaf 3384702543) (.leaf 3278740137)) (.branch 14 (.leaf 3176983865) (.leaf 3079224678))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2985266052) (.branch 17 (.leaf 2894923096) (.leaf 2808021741))) (.branch 20 (.branch 19 (.leaf 2724397991) (.leaf 2643897238)) (.branch 21 (.leaf 2566373633) (.leaf 2491689503)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2419714817) (.leaf 2350326691)) (.branch 25 (.leaf 2283408930) (.leaf 2218851605))) (.branch 28 (.branch 27 (.leaf 2156550660) (.leaf 2096407549)) (.branch 29 (.leaf 2038328897) (.leaf 1982226186)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1928015464) (.branch 32 (.leaf 1875617071) (.leaf 1824955387))) (.branch 35 (.branch 34 (.leaf 1775958592) (.leaf 1728558452)) (.branch 36 (.leaf 1682690104) (.leaf 1638291870)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1595305076) (.leaf 1553673877)) (.branch 40 (.leaf 1513345109) (.leaf 1474268131))) (.branch 43 (.branch 42 (.leaf 1436394693) (.leaf 1399678802)) (.branch 44 (.leaf 1364076602) (.leaf 1329546257))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1296047846) (.branch 47 (.leaf 1263543257) (.leaf 1231996096))) (.branch 50 (.branch 49 (.leaf 1201371595) (.leaf 1171636529)) (.branch 51 (.leaf 1142759134) (.leaf 1114709033)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1087457168) (.leaf 1060975727)) (.branch 55 (.leaf 1035238090) (.leaf 1010218761))) (.branch 58 (.branch 57 (.leaf 985893317) (.leaf 962238354)) (.branch 59 (.leaf 939231438) (.leaf 916851054))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 895076567) (.branch 62 (.leaf 873888176) (.leaf 853266873))) (.branch 65 (.branch 64 (.leaf 833194409) (.leaf 813653258)) (.branch 66 (.leaf 794626578) (.leaf 776098186)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 758052522) (.leaf 740474623)) (.branch 70 (.leaf 723350096) (.leaf 706665090))) (.branch 73 (.branch 72 (.leaf 690406274) (.leaf 674560811)) (.branch 74 (.leaf 659116340) (.leaf 644060949))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 629383161) (.branch 77 (.leaf 615071912) (.leaf 601116534))) (.branch 80 (.branch 79 (.leaf 587506737) (.leaf 574232593)) (.branch 81 (.leaf 561284524) (.leaf 548653280)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 536329931) (.leaf 524305855)) (.branch 85 (.leaf 512572717) (.leaf 501122468))) (.branch 88 (.branch 87 (.leaf 489947323) (.leaf 479039759)) (.branch 89 (.leaf 468392499) (.leaf 457998502)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 447850959) (.branch 92 (.leaf 437943277) (.leaf 428269076))) (.branch 95 (.branch 94 (.leaf 418822177) (.leaf 409596596)) (.branch 96 (.leaf 400586537) (.leaf 391786383)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 383190691) (.leaf 374794184)) (.branch 100 (.leaf 366591746) (.leaf 358578417))) (.branch 103 (.branch 102 (.leaf 350749382) (.leaf 343099975)) (.branch 104 (.leaf 335625663) (.leaf 328322049))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 321184865) (.leaf 314209966)) (.branch 108 (.leaf 307393326) (.leaf 300731037))) (.branch 111 (.branch 110 (.leaf 294219299) (.leaf 287854422)) (.branch 112 (.leaf 281632820) (.leaf 275551005)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 269605590) (.leaf 263793278)) (.branch 116 (.leaf 258110864) (.leaf 252555232))) (.branch 119 (.branch 118 (.leaf 247123349) (.leaf 241812265)) (.branch 120 (.leaf 236619109) (.leaf 231541086)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 539).prefactor = (1182365272062147/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 539).cutoff/(generalMeanRows 539).c)).2 =
    (366697216494399/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 539).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 539).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 539).q*(generalMeanRows 539).c/2-2 = (1339/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable194.value]
    have hcontinuation : (generalMeanRows 539).q*(generalMeanRows 539).cutoff/2-2 = (6538/3123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable193.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 539).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 539

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 539).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 539).criticalRate j.val*(generalMeanRows 539).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 539).c*(generalMeanRows 539).criticalPoint j.val)).2-
      (generalMeanRows 539).J/2-(generalMeanRows 539).error (generalMeanGrid j.val)+
      (generalMeanRows 539).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 539).c)).2-
      (generalMeanRows 539).J/2-(generalMeanRows 539).error 4 := by
  have he : (generalMeanRows 539).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 539) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 539)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0539

/-! Kernel-checked entropy margins for general spectral rectangle 540. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0540
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4975865566) (.branch 2 (.leaf 4804871024) (.leaf 4641557030))) (.branch 5 (.branch 4 (.leaf 4485484835) (.leaf 4336246692)) (.branch 6 (.leaf 4193463155) (.leaf 4056780659)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3925869365) (.leaf 3800421219)) (.branch 10 (.leaf 3680148206) (.leaf 3564780779))) (.branch 13 (.branch 12 (.leaf 3454066428) (.leaf 3347768393)) (.branch 14 (.leaf 3245664490) (.leaf 3147546041))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3053216900) (.branch 17 (.leaf 2962492562) (.leaf 2875199346))) (.branch 20 (.branch 19 (.leaf 2791173651) (.leaf 2710261266)) (.branch 21 (.leaf 2632316737) (.leaf 2557202789)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2484789788) (.leaf 2414955243)) (.branch 25 (.leaf 2347583350) (.leaf 2282564568))) (.branch 28 (.branch 27 (.leaf 2219795225) (.leaf 2159177155)) (.branch 29 (.leaf 2100617355) (.leaf 2044027678)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1989324533) (.branch 32 (.leaf 1936428615) (.leaf 1885264654))) (.branch 35 (.branch 34 (.leaf 1835761172) (.leaf 1787850270)) (.branch 36 (.leaf 1741467413) (.leaf 1696551242)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1653043396) (.leaf 1610888336)) (.branch 40 (.leaf 1570033192) (.leaf 1530427615))) (.branch 43 (.branch 42 (.leaf 1492023633) (.leaf 1454775529)) (.branch 44 (.leaf 1418639710) (.leaf 1383574599))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1349540523) (.branch 47 (.leaf 1316499612) (.leaf 1284415708))) (.branch 50 (.branch 49 (.leaf 1253254267) (.leaf 1222982284)) (.branch 51 (.leaf 1193568206) (.leaf 1164981861)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1137194386) (.leaf 1110178162)) (.branch 55 (.leaf 1083906747) (.leaf 1058354824))) (.branch 58 (.branch 57 (.leaf 1033498139) (.leaf 1009313451)) (.branch 59 (.leaf 985778479) (.leaf 962871860))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 940573102) (.branch 62 (.leaf 918862540) (.leaf 897721300))) (.branch 65 (.branch 64 (.leaf 877131257) (.leaf 857075005)) (.branch 66 (.leaf 837535817) (.leaf 818497617)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 799944952) (.leaf 781862956)) (.branch 70 (.leaf 764237329) (.leaf 747054310))) (.branch 73 (.branch 72 (.leaf 730300652) (.leaf 713963598)) (.branch 74 (.leaf 698030861) (.leaf 682490602))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 667331409) (.branch 77 (.leaf 652542282) (.leaf 638112611))) (.branch 80 (.branch 79 (.leaf 624032160) (.leaf 610291055)) (.branch 81 (.leaf 596879763) (.leaf 583789080)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 571010116) (.leaf 558534287)) (.branch 85 (.leaf 546353293) (.leaf 534459115))) (.branch 88 (.branch 87 (.leaf 522843999) (.leaf 511500446)) (.branch 89 (.leaf 500421202) (.leaf 489599249)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 479027793) (.branch 92 (.leaf 468700258) (.leaf 458610276))) (.branch 95 (.branch 94 (.leaf 448751680) (.leaf 439118495)) (.branch 96 (.leaf 429704930) (.leaf 420505374)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 411514386) (.leaf 402726690)) (.branch 100 (.leaf 394137170) (.leaf 385740861))) (.branch 103 (.branch 102 (.leaf 377532947) (.leaf 369508752)) (.branch 104 (.leaf 361663739) (.leaf 353993501))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 346493760) (.leaf 339160358)) (.branch 108 (.leaf 331989258) (.leaf 324976536))) (.branch 111 (.branch 110 (.leaf 318118379) (.leaf 311411080)) (.branch 112 (.leaf 304851034) (.leaf 298434737)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 292158781) (.leaf 286019849)) (.branch 116 (.leaf 280014716) (.leaf 274140243))) (.branch 119 (.branch 118 (.leaf 268393375) (.leaf 262771138)) (.branch 120 (.leaf 257270638) (.leaf 251889054)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 540).prefactor = (4728152829719751/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 540).cutoff/(generalMeanRows 540).c)).2 =
    (23478625639083/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 540).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 540).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 540).q*(generalMeanRows 540).c/2-2 = (261/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable137.value]
    have hcontinuation : (generalMeanRows 540).q*(generalMeanRows 540).cutoff/2-2 = (13094/6237:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable197.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 540).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 540

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 540).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 540).criticalRate j.val*(generalMeanRows 540).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 540).c*(generalMeanRows 540).criticalPoint j.val)).2-
      (generalMeanRows 540).J/2-(generalMeanRows 540).error (generalMeanGrid j.val)+
      (generalMeanRows 540).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 540).c)).2-
      (generalMeanRows 540).J/2-(generalMeanRows 540).error 4 := by
  have he : (generalMeanRows 540).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 540) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 540)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0540

/-! Kernel-checked entropy margins for general spectral rectangle 541. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0541
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4984503223) (.branch 2 (.leaf 4813211850) (.leaf 4649614357))) (.branch 5 (.branch 4 (.leaf 4493271234) (.leaf 4343774028)) (.branch 6 (.leaf 4200742631) (.leaf 4063822866)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3932684322) (.leaf 3807018409)) (.branch 10 (.leaf 3686536614) (.leaf 3570968919))) (.branch 13 (.branch 12 (.leaf 3460062377) (.leaf 3353579819)) (.branch 14 (.leaf 3251298673) (.leaf 3153009899))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3058517011) (.branch 17 (.leaf 2967635183) (.leaf 2880190434))) (.branch 20 (.branch 19 (.leaf 2796018878) (.leaf 2714966036)) (.branch 21 (.leaf 2636886203) (.leaf 2561641864)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2489103160) (.leaf 2419147388)) (.branch 25 (.leaf 2351658544) (.leaf 2286526895))) (.branch 28 (.branch 27 (.leaf 2223648591) (.leaf 2162925293)) (.branch 29 (.leaf 2104263839) (.leaf 2047575927)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1992777822) (.branch 32 (.leaf 1939790082) (.leaf 1888537304))) (.branch 35 (.branch 34 (.leaf 1838947889) (.leaf 1790953818)) (.branch 36 (.leaf 1744490444) (.leaf 1699496303)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1655912931) (.leaf 1613684694)) (.branch 40 (.leaf 1572758629) (.leaf 1533084300))) (.branch 43 (.branch 42 (.leaf 1494613653) (.leaf 1457300889)) (.branch 44 (.leaf 1421102341) (.leaf 1385976360))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1351883204) (.branch 47 (.leaf 1318784938) (.leaf 1286645338))) (.branch 50 (.branch 49 (.leaf 1255429805) (.leaf 1225105272)) (.branch 51 (.leaf 1195640134) (.leaf 1167004165)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1139168454) (.leaf 1112105331)) (.branch 55 (.leaf 1085788312) (.leaf 1060192034))) (.branch 58 (.branch 57 (.leaf 1035292200) (.leaf 1011065528)) (.branch 59 (.leaf 987489702) (.leaf 964543319))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 942205853) (.branch 62 (.leaf 920457603) (.leaf 899279664))) (.branch 65 (.branch 64 (.leaf 878653878) (.leaf 858562810)) (.branch 66 (.leaf 838989704) (.leaf 819918456)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 801333584) (.leaf 783220200)) (.branch 70 (.leaf 765563976) (.leaf 748351129))) (.branch 73 (.branch 72 (.leaf 731568389) (.leaf 715202975)) (.branch 74 (.leaf 699242580) (.leaf 683675345))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 668489837) (.branch 77 (.leaf 653675037) (.leaf 639220317))) (.branch 80 (.branch 79 (.leaf 625115424) (.leaf 611350466)) (.branch 81 (.leaf 597915893) (.leaf 584802485)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 572001339) (.leaf 559503852)) (.branch 85 (.leaf 547301713) (.leaf 535386888))) (.branch 88 (.branch 87 (.leaf 523751610) (.leaf 512388365)) (.branch 89 (.leaf 501289889) (.leaf 490449149)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 479859342) (.branch 92 (.leaf 469513879) (.leaf 459406382))) (.branch 95 (.branch 94 (.leaf 449530673) (.leaf 439880765)) (.branch 96 (.leaf 430450859) (.leaf 421235333)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 412228738) (.leaf 403425788)) (.branch 100 (.leaf 394821357) (.leaf 386410473))) (.branch 103 (.branch 102 (.leaf 378188310) (.leaf 370150186)) (.branch 104 (.leaf 362291555) (.leaf 354608002))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 347095242) (.leaf 339749110)) (.branch 108 (.leaf 332565562) (.leaf 325540667))) (.branch 111 (.branch 110 (.leaf 318670604) (.leaf 311951662)) (.branch 112 (.leaf 305380228) (.leaf 298952793)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 292665942) (.leaf 286516354)) (.branch 116 (.leaf 280500797) (.leaf 274616126))) (.branch 119 (.branch 118 (.leaf 268859282) (.leaf 263227285)) (.branch 120 (.leaf 257717236) (.leaf 252326311)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 541).prefactor = (947272095848599/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 541).cutoff/(generalMeanRows 541).c)).2 =
    (23478625639083/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 541).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 541).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 541).q*(generalMeanRows 541).c/2-2 = (261/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable137.value]
    have hcontinuation : (generalMeanRows 541).q*(generalMeanRows 541).cutoff/2-2 = (13094/6237:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable197.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 541).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 541

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 541).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 541).criticalRate j.val*(generalMeanRows 541).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 541).c*(generalMeanRows 541).criticalPoint j.val)).2-
      (generalMeanRows 541).J/2-(generalMeanRows 541).error (generalMeanGrid j.val)+
      (generalMeanRows 541).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 541).c)).2-
      (generalMeanRows 541).J/2-(generalMeanRows 541).error 4 := by
  have he : (generalMeanRows 541).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 541) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 541)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0541

/-! Kernel-checked entropy margins for general spectral rectangle 542. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0542
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4994536889) (.branch 2 (.leaf 4822926817) (.leaf 4659017697))) (.branch 5 (.branch 4 (.leaf 4502370115) (.leaf 4352575689)) (.branch 6 (.leaf 4209254355) (.leaf 4072051958)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3940638085) (.leaf 3814704130)) (.branch 10 (.leaf 3693961544) (.leaf 3578140257))) (.branch 13 (.branch 12 (.leaf 3466987259) (.leaf 3360265303)) (.branch 14 (.leaf 3257751730) (.leaf 3159237404))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3064525732) (.branch 17 (.leaf 2973431778) (.leaf 2885781441))) (.branch 20 (.branch 19 (.leaf 2801410712) (.leaf 2720164983)) (.branch 21 (.leaf 2641898418) (.leaf 2566473368)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2493759836) (.leaf 2423634982)) (.branch 25 (.leaf 2355982661) (.leaf 2290693001))) (.branch 28 (.branch 27 (.leaf 2227662010) (.leaf 2166791210)) (.branch 29 (.leaf 2107987299) (.leaf 2051161837)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1996230949) (.branch 32 (.leaf 1943115058) (.leaf 1891738627))) (.branch 35 (.branch 34 (.leaf 1842029923) (.leaf 1793920795)) (.branch 36 (.leaf 1747346470) (.leaf 1702245355)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1658558862) (.leaf 1616231235)) (.branch 40 (.leaf 1575209394) (.leaf 1535442782))) (.branch 43 (.branch 42 (.leaf 1496883234) (.leaf 1459484839)) (.branch 44 (.leaf 1423203821) (.leaf 1387998425))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1353828804) (.branch 47 (.leaf 1320656924) (.leaf 1288446464))) (.branch 50 (.branch 49 (.leaf 1257162727) (.leaf 1226772556)) (.branch 51 (.leaf 1197244253) (.leaf 1168547508)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1140653323) (.leaf 1113533946)) (.branch 55 (.leaf 1087162814) (.leaf 1061514485))) (.branch 58 (.branch 57 (.leaf 1036564590) (.leaf 1012289773)) (.branch 59 (.leaf 988667646) (.leaf 965676741))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 943296464) (.branch 62 (.leaf 921507053) (.leaf 900289539))) (.branch 65 (.branch 64 (.leaf 879625706) (.leaf 859498061)) (.branch 66 (.leaf 839889793) (.leaf 820784746)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 802167384) (.leaf 784022769)) (.branch 70 (.leaf 766336528) (.leaf 749094829))) (.branch 73 (.branch 72 (.leaf 732284357) (.leaf 715892290)) (.branch 74 (.leaf 699906279) (.leaf 684314423))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 669105252) (.branch 77 (.leaf 654267711) (.leaf 639791133))) (.branch 80 (.branch 79 (.leaf 625665234) (.leaf 611880086)) (.branch 81 (.leaf 598426109) (.leaf 585294051)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 572474980) (.leaf 559960265)) (.branch 85 (.leaf 547741567) (.leaf 535810825))) (.branch 88 (.branch 87 (.leaf 524160247) (.leaf 512782296)) (.branch 89 (.leaf 501669683) (.leaf 490815354)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 480212482) (.branch 92 (.leaf 469854459) (.leaf 459734887))) (.branch 95 (.branch 94 (.leaf 449847567) (.leaf 440186496)) (.branch 96 (.leaf 430745856) (.leaf 421520008)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 412503486) (.leaf 403690988)) (.branch 100 (.leaf 395077376) (.leaf 386657660))) (.branch 103 (.branch 102 (.leaf 378427002) (.leaf 370380705)) (.branch 104 (.leaf 362514211) (.leaf 354823093))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 347303054) (.leaf 339949917)) (.branch 108 (.leaf 332759628) (.leaf 325728244))) (.branch 111 (.branch 110 (.leaf 318851937) (.leaf 312126982)) (.branch 112 (.leaf 305549761) (.leaf 299116753)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 292824536) (.leaf 286669780)) (.branch 116 (.leaf 280649246) (.leaf 274759782))) (.branch 119 (.branch 118 (.leaf 268998319) (.leaf 263361873)) (.branch 120 (.leaf 257847537) (.leaf 252452480)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 542).prefactor = (1184426201210899/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 542).cutoff/(generalMeanRows 542).c)).2 =
    (187108024454213/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 542).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 542).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 542).q*(generalMeanRows 542).c/2-2 = (261/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable137.value]
    have hcontinuation : (generalMeanRows 542).q*(generalMeanRows 542).cutoff/2-2 = (6538/3123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable193.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 542).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 542

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 542).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 542).criticalRate j.val*(generalMeanRows 542).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 542).c*(generalMeanRows 542).criticalPoint j.val)).2-
      (generalMeanRows 542).J/2-(generalMeanRows 542).error (generalMeanGrid j.val)+
      (generalMeanRows 542).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 542).c)).2-
      (generalMeanRows 542).J/2-(generalMeanRows 542).error 4 := by
  have he : (generalMeanRows 542).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 542) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 542)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0542

/-! Kernel-checked entropy margins for general spectral rectangle 543. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0543
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4920802469) (.branch 2 (.leaf 4749395796) (.leaf 4585711359))) (.branch 5 (.branch 4 (.leaf 4429308769) (.leaf 4279778709)) (.branch 6 (.leaf 4136740222) (.leaf 3999838289)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3868741671) (.leaf 3743140966)) (.branch 10 (.leaf 3622746857) (.leaf 3507288536))) (.branch 13 (.branch 12 (.leaf 3396512281) (.leaf 3290180156)) (.branch 14 (.leaf 3188068841) (.leaf 3089968557))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2995682095) (.branch 17 (.leaf 2905023919) (.leaf 2817819352))) (.branch 20 (.branch 19 (.leaf 2733903826) (.leaf 2653122194)) (.branch 21 (.leaf 2575328097) (.leaf 2500383383)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2428157567) (.leaf 2358527335)) (.branch 25 (.leaf 2291376088) (.leaf 2226593513))) (.branch 28 (.branch 27 (.leaf 2164075190) (.leaf 2103722231)) (.branch 29 (.leaf 2045440933) (.leaf 1989142472)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1934742601) (.branch 32 (.leaf 1882161382) (.leaf 1831322931))) (.branch 35 (.branch 34 (.leaf 1782155180) (.leaf 1734589653)) (.branch 36 (.leaf 1688561263) (.leaf 1644008118)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1600871336) (.leaf 1559094880)) (.branch 40 (.leaf 1518625398) (.leaf 1479412075))) (.branch 43 (.branch 42 (.leaf 1441406490) (.leaf 1404562492)) (.branch 44 (.leaf 1368836071) (.leaf 1334185244))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1300569952) (.branch 47 (.leaf 1267951949) (.leaf 1236294716))) (.branch 50 (.branch 49 (.leaf 1205563362) (.leaf 1175724546)) (.branch 51 (.leaf 1146746393) (.leaf 1118598421)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1091251469) (.leaf 1064677631)) (.branch 55 (.leaf 1038850192) (.leaf 1013743566))) (.branch 58 (.branch 57 (.leaf 989333247) (.leaf 965595749)) (.branch 59 (.leaf 942508558) (.leaf 920050086))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 898199625) (.branch 62 (.leaf 876937303) (.leaf 856244049))) (.branch 65 (.branch 64 (.leaf 836101550) (.leaf 816492217)) (.branch 66 (.leaf 797399150) (.leaf 778806110)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 760697481) (.leaf 743058251)) (.branch 70 (.leaf 725873974) (.leaf 709130751))) (.branch 73 (.branch 72 (.leaf 692815205) (.leaf 676914456)) (.branch 74 (.leaf 661416096) (.leaf 646308174))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 631579173) (.branch 77 (.leaf 617217990) (.leaf 603213920))) (.branch 80 (.branch 79 (.leaf 589556636) (.leaf 576236177)) (.branch 81 (.leaf 563242930) (.leaf 550567613)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 538201267) (.leaf 526135237)) (.branch 85 (.leaf 514361161) (.leaf 502870960))) (.branch 88 (.branch 87 (.leaf 491656823) (.leaf 480711201)) (.branch 89 (.leaf 470026791) (.leaf 459596528)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 449413579) (.branch 92 (.leaf 439471327) (.leaf 429763372))) (.branch 95 (.branch 94 (.leaf 420283511) (.leaf 411025741)) (.branch 96 (.leaf 401984244) (.leaf 393153385)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 384527701) (.leaf 376101897)) (.branch 100 (.leaf 367870840) (.leaf 359829551))) (.branch 103 (.branch 102 (.leaf 351973200) (.leaf 344297102)) (.branch 104 (.leaf 336796711) (.leaf 329467614))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 322305527) (.leaf 315306292)) (.branch 108 (.leaf 308465868) (.leaf 301780333))) (.branch 111 (.branch 110 (.leaf 295245874) (.leaf 288858790)) (.branch 112 (.leaf 282615479) (.leaf 276512444)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 270546285) (.leaf 264713692)) (.branch 116 (.leaf 259011452) (.leaf 253436435))) (.branch 119 (.branch 118 (.leaf 247985600) (.leaf 242655984)) (.branch 120 (.leaf 237444708) (.leaf 232348968)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 543).prefactor = (4745962890700141/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 543).cutoff/(generalMeanRows 543).c)).2 =
    (366697216494399/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 543).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 543).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 543).q*(generalMeanRows 543).c/2-2 = (1339/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable194.value]
    have hcontinuation : (generalMeanRows 543).q*(generalMeanRows 543).cutoff/2-2 = (6538/3123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable193.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 543).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 543

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 543).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 543).criticalRate j.val*(generalMeanRows 543).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 543).c*(generalMeanRows 543).criticalPoint j.val)).2-
      (generalMeanRows 543).J/2-(generalMeanRows 543).error (generalMeanGrid j.val)+
      (generalMeanRows 543).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 543).c)).2-
      (generalMeanRows 543).J/2-(generalMeanRows 543).error 4 := by
  have he : (generalMeanRows 543).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 543) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 543)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0543

/-! Kernel-checked entropy margins for general spectral rectangle 544. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0544
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5315920753) (.branch 2 (.leaf 5148355822) (.leaf 4988172025))) (.branch 5 (.branch 4 (.leaf 4834944127) (.leaf 4688277174)) (.branch 6 (.leaf 4547803852) (.leaf 4413182122)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4284093104) (.leaf 4160239186)) (.branch 10 (.leaf 4041342308) (.leaf 3927142423))) (.branch 13 (.branch 12 (.leaf 3817396106) (.leaf 3711875279)) (.branch 14 (.leaf 3610366071) (.leaf 3512667768))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3418591857) (.branch 17 (.leaf 3327961153) (.leaf 3240609003))) (.branch 20 (.branch 19 (.leaf 3156378553) (.leaf 3075122072)) (.branch 21 (.leaf 2996700336) (.leaf 2920982059)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2847843365) (.leaf 2777167304)) (.branch 25 (.leaf 2708843404) (.leaf 2642767257))) (.branch 28 (.branch 27 (.leaf 2578840130) (.leaf 2516968615)) (.branch 29 (.leaf 2457064292) (.leaf 2399043425)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2342826674) (.branch 32 (.leaf 2288338833) (.leaf 2235508574))) (.branch 35 (.branch 34 (.leaf 2184268225) (.leaf 2134553547)) (.branch 36 (.leaf 2086303538) (.leaf 2039460242)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1993968573) (.leaf 1949776155)) (.branch 40 (.leaf 1906833159) (.leaf 1865092171))) (.branch 43 (.branch 42 (.leaf 1824508047) (.leaf 1785037789)) (.branch 44 (.leaf 1746640432) (.leaf 1709276923))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1672910025) (.branch 47 (.leaf 1637504212) (.leaf 1603025584))) (.branch 50 (.branch 49 (.leaf 1569441773) (.leaf 1536721865)) (.branch 51 (.leaf 1504836323) (.leaf 1473756915)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1443456645) (.leaf 1413909689)) (.branch 55 (.leaf 1385091335) (.leaf 1356977927))) (.branch 58 (.branch 57 (.leaf 1329546808) (.leaf 1302776274)) (.branch 59 (.leaf 1276645522) (.leaf 1251134609))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1226224405) (.branch 62 (.leaf 1201896557) (.leaf 1178133446))) (.branch 65 (.branch 64 (.leaf 1154918157) (.leaf 1132234441)) (.branch 66 (.leaf 1110066684) (.leaf 1088399877)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1067219586) (.leaf 1046511928)) (.branch 70 (.leaf 1026263540) (.leaf 1006461561))) (.branch 73 (.branch 72 (.leaf 987093603) (.leaf 968147732)) (.branch 74 (.leaf 949612450) (.leaf 931476669))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 913729697) (.branch 77 (.leaf 896361220) (.leaf 879361283))) (.branch 80 (.branch 79 (.leaf 862720276) (.leaf 846428920)) (.branch 81 (.leaf 830478249) (.leaf 814859600)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 799564597) (.leaf 784585142)) (.branch 85 (.leaf 769913401) (.leaf 755541793))) (.branch 88 (.branch 87 (.leaf 741462982) (.leaf 727669863)) (.branch 89 (.leaf 714155555) (.leaf 700913392)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 687936913) (.branch 92 (.leaf 675219856) (.leaf 662756146))) (.branch 95 (.branch 94 (.leaf 650539895) (.leaf 638565385)) (.branch 96 (.leaf 626827069) (.leaf 615319562)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 604037634) (.leaf 592976206)) (.branch 100 (.leaf 582130342) (.leaf 571495245))) (.branch 103 (.branch 102 (.leaf 561066254) (.leaf 550838834)) (.branch 104 (.leaf 540808577) (.leaf 530971192))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 521322506) (.leaf 511858458)) (.branch 108 (.leaf 502575091) (.leaf 493468556))) (.branch 111 (.branch 110 (.leaf 484535102) (.leaf 475771076)) (.branch 112 (.leaf 467172918) (.leaf 458737160)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 450460420) (.leaf 442339402)) (.branch 116 (.leaf 434370890) (.leaf 426551750))) (.branch 119 (.branch 118 (.leaf 418878922) (.leaf 411349424)) (.branch 120 (.leaf 403960342) (.leaf 396708835)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 544).prefactor = (4610961204339809/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 544).cutoff/(generalMeanRows 544).c)).2 =
    (424464946023869/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 544).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 544).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 544).q*(generalMeanRows 544).c/2-2 = (1397/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable189.value]
    have hcontinuation : (generalMeanRows 544).q*(generalMeanRows 544).cutoff/2-2 = (678/319:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable198.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 544).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 544

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 544).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 544).criticalRate j.val*(generalMeanRows 544).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 544).c*(generalMeanRows 544).criticalPoint j.val)).2-
      (generalMeanRows 544).J/2-(generalMeanRows 544).error (generalMeanGrid j.val)+
      (generalMeanRows 544).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 544).c)).2-
      (generalMeanRows 544).J/2-(generalMeanRows 544).error 4 := by
  have he : (generalMeanRows 544).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 544) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 544)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0544

/-! Kernel-checked entropy margins for general spectral rectangle 545. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0545
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5243509425) (.branch 2 (.leaf 5075660420) (.leaf 4915228217))) (.branch 5 (.branch 4 (.leaf 4761786073) (.leaf 4614937604)) (.branch 6 (.leaf 4474314138) (.leaf 4339572344)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4210392113) (.leaf 4086474657)) (.branch 10 (.leaf 3967540798) (.leaf 3853329416))) (.branch 13 (.branch 12 (.leaf 3743596057) (.leaf 3638111663)) (.branch 14 (.leaf 3536661417) (.leaf 3439043700))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3345069125) (.branch 17 (.leaf 3254559673) (.leaf 3167347883))) (.branch 20 (.branch 19 (.leaf 3083276124) (.leaf 3002195917)) (.branch 21 (.leaf 2923967315) (.leaf 2848458337)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2775544434) (.leaf 2705108007)) (.branch 25 (.leaf 2637037957) (.leaf 2571229269))) (.branch 28 (.branch 27 (.leaf 2507582626) (.leaf 2446004051)) (.branch 29 (.leaf 2386404577) (.leaf 2328699938)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2272810280) (.branch 32 (.leaf 2218659900) (.leaf 2166176990))) (.branch 35 (.branch 34 (.leaf 2115293411) (.leaf 2065944475)) (.branch 36 (.leaf 2018068742) (.leaf 1971607832)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1926506252) (.leaf 1882711226)) (.branch 40 (.leaf 1840172543) (.leaf 1798842416))) (.branch 43 (.branch 42 (.leaf 1758675338) (.leaf 1719627965)) (.branch 44 (.leaf 1681658991) (.leaf 1644729036))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1608800544) (.branch 47 (.leaf 1573837684) (.leaf 1539806255))) (.branch 50 (.branch 49 (.leaf 1506673602) (.leaf 1474408531)) (.branch 51 (.leaf 1442981234) (.leaf 1412363218)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1382527232) (.leaf 1353447208)) (.branch 55 (.leaf 1325098195) (.leaf 1297456307))) (.branch 58 (.branch 57 (.leaf 1270498666) (.leaf 1244203352)) (.branch 59 (.leaf 1218549354) (.leaf 1193516527))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1169085548) (.branch 62 (.leaf 1145237874) (.leaf 1121955706))) (.branch 65 (.branch 64 (.leaf 1099221952) (.leaf 1077020195)) (.branch 66 (.leaf 1055334656) (.leaf 1034150168)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1013452145) (.leaf 993226555)) (.branch 70 (.leaf 973459896) (.leaf 954139168))) (.branch 73 (.branch 72 (.leaf 935251851) (.leaf 916785885)) (.branch 74 (.leaf 898729648) (.leaf 881071935))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 863801941) (.branch 77 (.leaf 846909241) (.leaf 830383776))) (.branch 80 (.branch 79 (.leaf 814215836) (.leaf 798396042)) (.branch 81 (.leaf 782915338) (.leaf 767764969)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 752936475) (.leaf 738421675)) (.branch 85 (.leaf 724212657) (.leaf 710301763))) (.branch 88 (.branch 87 (.leaf 696681585) (.leaf 683344950)) (.branch 89 (.leaf 670284910) (.leaf 657494736)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 644967908) (.branch 92 (.leaf 632698105) (.leaf 620679200))) (.branch 95 (.branch 94 (.leaf 608905250) (.leaf 597370488)) (.branch 96 (.leaf 586069323) (.leaf 574996323)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 564146216) (.leaf 553513884)) (.branch 100 (.leaf 543094354) (.leaf 532882793))) (.branch 103 (.branch 102 (.leaf 522874506) (.leaf 513064928)) (.branch 104 (.leaf 503449620) (.leaf 494024266))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 484784666) (.leaf 475726734)) (.branch 108 (.leaf 466846493) (.leaf 458140074))) (.branch 111 (.branch 110 (.leaf 449603706) (.leaf 441233720)) (.branch 112 (.leaf 433026540) (.leaf 424978683)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 417086756) (.leaf 409347450)) (.branch 116 (.leaf 401757540) (.leaf 394313884))) (.branch 119 (.branch 118 (.leaf 387013415) (.leaf 379853143)) (.branch 120 (.leaf 372830151) (.leaf 365941593)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 545).prefactor = (1156657481611239/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 545).cutoff/(generalMeanRows 545).c)).2 =
    (208356484609779/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 545).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 545).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 545).q*(generalMeanRows 545).c/2-2 = (1439/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable199.value]
    have hcontinuation : (generalMeanRows 545).q*(generalMeanRows 545).cutoff/2-2 = (678/319:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable198.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 545).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 545

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 545).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 545).criticalRate j.val*(generalMeanRows 545).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 545).c*(generalMeanRows 545).criticalPoint j.val)).2-
      (generalMeanRows 545).J/2-(generalMeanRows 545).error (generalMeanGrid j.val)+
      (generalMeanRows 545).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 545).c)).2-
      (generalMeanRows 545).J/2-(generalMeanRows 545).error 4 := by
  have he : (generalMeanRows 545).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 545) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 545)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0545

/-! Kernel-checked entropy margins for general spectral rectangle 546. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0546
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4993155874) (.branch 2 (.leaf 4821567154) (.leaf 4657685671))) (.branch 5 (.branch 4 (.leaf 4501071150) (.leaf 4351314430)) (.branch 6 (.leaf 4208034744) (.leaf 4070877299)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3939511110) (.leaf 3813627052)) (.branch 10 (.leaf 3692936111) (.leaf 3577167801))) (.branch 13 (.branch 12 (.leaf 3466068735) (.leaf 3359401333)) (.branch 14 (.leaf 3256942636) (.leaf 3158483242))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3063826322) (.branch 17 (.leaf 2972786732) (.leaf 2885190187))) (.branch 20 (.branch 19 (.leaf 2800872517) (.leaf 2719678974)) (.branch 21 (.leaf 2641463601) (.leaf 2566088645)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2493424020) (.leaf 2423346811)) (.branch 25 (.leaf 2355740812) (.leaf 2290496101))) (.branch 28 (.branch 27 (.leaf 2227508645) (.leaf 2166679937)) (.branch 29 (.leaf 2107916652) (.leaf 2051130335)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1996237106) (.branch 32 (.leaf 1943157383) (.leaf 1891815636))) (.branch 35 (.branch 34 (.leaf 1842140138) (.leaf 1794062753)) (.branch 36 (.leaf 1747518723) (.leaf 1702446477)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1658787448) (.leaf 1616485906)) (.branch 40 (.leaf 1575488797) (.leaf 1535745597))) (.branch 43 (.branch 42 (.leaf 1497208168) (.leaf 1459830632)) (.branch 44 (.leaf 1423569248) (.leaf 1388382291))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1354229952) (.branch 47 (.leaf 1321074230) (.leaf 1288878839))) (.branch 50 (.branch 49 (.leaf 1257609118) (.leaf 1227231945)) (.branch 51 (.leaf 1197715658) (.leaf 1169029980)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1141145948) (.leaf 1114035846)) (.branch 55 (.leaf 1087673143) (.leaf 1062032432))) (.branch 58 (.branch 57 (.leaf 1037089374) (.leaf 1012820647)) (.branch 59 (.leaf 989203895) (.leaf 966217680))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 943841438) (.branch 62 (.leaf 922055435) (.leaf 900840732))) (.branch 65 (.branch 64 (.leaf 880179143) (.leaf 860053198)) (.branch 66 (.leaf 840446115) (.leaf 821341761)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 802724628) (.leaf 784579800)) (.branch 70 (.leaf 766892927) (.leaf 749650200))) (.branch 73 (.branch 72 (.leaf 732838326) (.leaf 716444503)) (.branch 74 (.leaf 700456403) (.leaf 684862144))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 669650275) (.branch 77 (.leaf 654809758) (.leaf 640329946))) (.branch 80 (.branch 79 (.leaf 626200569) (.leaf 612411716)) (.branch 81 (.leaf 598953821) (.leaf 585817650)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 572994282) (.leaf 560475101)) (.branch 85 (.leaf 548251780) (.leaf 536316272))) (.branch 88 (.branch 87 (.leaf 524660795) (.leaf 513277826)) (.branch 89 (.leaf 502160083) (.leaf 491300525)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 480692335) (.branch 92 (.leaf 470328913) (.leaf 460203871))) (.branch 95 (.branch 94 (.leaf 450311018) (.leaf 440644358)) (.branch 96 (.leaf 431198083) (.leaf 421966560)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 412944330) (.leaf 404126099)) (.branch 100 (.leaf 395506731) (.leaf 387081247))) (.branch 103 (.branch 102 (.leaf 378844811) (.leaf 370792734)) (.branch 104 (.leaf 362920461) (.leaf 355223570))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 347697768) (.leaf 340338884)) (.branch 108 (.leaf 333142866) (.leaf 326105776))) (.branch 111 (.branch 110 (.leaf 319223788) (.leaf 312493182)) (.branch 112 (.leaf 305910341) (.leaf 299471748)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 293173984) (.leaf 287013721)) (.branch 116 (.leaf 280987721) (.leaf 275092835))) (.branch 119 (.branch 118 (.leaf 269325998) (.leaf 263684224)) (.branch 120 (.leaf 258164610) (.leaf 252764327)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 546).prefactor = (4744582376510151/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 546).cutoff/(generalMeanRows 546).c)).2 =
    (23478625639083/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 546).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 546).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 546).q*(generalMeanRows 546).c/2-2 = (261/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable137.value]
    have hcontinuation : (generalMeanRows 546).q*(generalMeanRows 546).cutoff/2-2 = (13094/6237:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable197.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 546).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 546

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 546).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 546).criticalRate j.val*(generalMeanRows 546).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 546).c*(generalMeanRows 546).criticalPoint j.val)).2-
      (generalMeanRows 546).J/2-(generalMeanRows 546).error (generalMeanGrid j.val)+
      (generalMeanRows 546).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 546).c)).2-
      (generalMeanRows 546).J/2-(generalMeanRows 546).error 4 := by
  have he : (generalMeanRows 546).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 546) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 546)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0546

/-! Kernel-checked entropy margins for general spectral rectangle 547. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0547
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4919301452) (.branch 2 (.leaf 4747917105) (.leaf 4584261251))) (.branch 5 (.branch 4 (.leaf 4427892647) (.leaf 4278401199)) (.branch 6 (.leaf 4135405246) (.leaf 3998549139)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3867501066) (.leaf 3741951109)) (.branch 10 (.leaf 3621609487) (.leaf 3506204978))) (.branch 13 (.branch 12 (.leaf 3395483484) (.leaf 3289206738)) (.branch 14 (.leaf 3187151120) (.leaf 3089106588))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2994875696) (.branch 17 (.leaf 2904272701) (.leaf 2817122742))) (.branch 20 (.branch 19 (.leaf 2733261093) (.leaf 2652532465)) (.branch 21 (.leaf 2574790379) (.leaf 2499896580)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2427720493) (.leaf 2358138731)) (.branch 25 (.leaf 2291034633) (.leaf 2226297835))) (.branch 28 (.branch 27 (.leaf 2163823880) (.leaf 2103513845)) (.branch 29 (.leaf 2045274009) (.leaf 1989015531)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1934654158) (.branch 32 (.leaf 1882109950) (.leaf 1831307026))) (.branch 35 (.branch 34 (.leaf 1782173327) (.leaf 1734640390)) (.branch 36 (.leaf 1688643144) (.leaf 1644119717)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1601011250) (.leaf 1559261731)) (.branch 40 (.leaf 1518817835) (.leaf 1479628776))) (.branch 43 (.branch 42 (.leaf 1441646164) (.leaf 1404823878)) (.branch 44 (.leaf 1369117942) (.leaf 1334486408))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1300889249) (.branch 47 (.leaf 1268288255) (.leaf 1236646940))) (.branch 50 (.branch 49 (.leaf 1205930451) (.leaf 1176105479)) (.branch 51 (.leaf 1147140186) (.leaf 1119004124)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1091668167) (.leaf 1065104441)) (.branch 55 (.leaf 1039286266) (.leaf 1014188090))) (.branch 58 (.branch 57 (.leaf 989785439) (.leaf 966054857)) (.branch 59 (.leaf 942973863) (.leaf 920520900))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 898675288) (.branch 62 (.leaf 877417187) (.leaf 856727552))) (.branch 65 (.branch 64 (.leaf 836588099) (.leaf 816981264)) (.branch 66 (.leaf 797890176) (.leaf 779298619)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 761191004) (.leaf 743552340)) (.branch 70 (.leaf 726368206) (.leaf 709624725))) (.branch 73 (.branch 72 (.leaf 693308542) (.leaf 677406795)) (.branch 74 (.leaf 661907100) (.leaf 646797523))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 632066567) (.branch 77 (.leaf 617703145) (.leaf 603696570))) (.branch 80 (.branch 79 (.leaf 590036533) (.leaf 576713088)) (.branch 81 (.leaf 563716637) (.leaf 551037913)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 538667971) (.leaf 526598169)) (.branch 85 (.leaf 514820159) (.leaf 503325874))) (.branch 88 (.branch 87 (.leaf 492107515) (.leaf 481157543)) (.branch 89 (.leaf 470468667) (.leaf 460033832)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 449846214) (.branch 92 (.leaf 439899209) (.leaf 430186420))) (.branch 95 (.branch 94 (.leaf 420701657) (.leaf 411438924)) (.branch 96 (.leaf 402392410) (.leaf 393556488)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 384925702) (.leaf 376494763)) (.branch 100 (.leaf 368258544) (.leaf 360212072))) (.branch 103 (.branch 102 (.leaf 352350523) (.leaf 344669218)) (.branch 104 (.leaf 337163614) (.leaf 329829305))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 322662010) (.leaf 315657575)) (.branch 108 (.leaf 308811964) (.leaf 302121258))) (.branch 111 (.branch 110 (.leaf 295581648) (.leaf 289189434)) (.branch 112 (.leaf 282941021) (.leaf 276832911)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 270861708) (.leaf 265024107)) (.branch 116 (.leaf 259316893) (.leaf 253736942))) (.branch 119 (.branch 118 (.leaf 248281211) (.leaf 242946742)) (.branch 120 (.leaf 237730657) (.leaf 232630152)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 547).prefactor = (4752818546254019/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 547).cutoff/(generalMeanRows 547).c)).2 =
    (368139177811301/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 547).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 547).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 547).q*(generalMeanRows 547).c/2-2 = (1339/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable194.value]
    have hcontinuation : (generalMeanRows 547).q*(generalMeanRows 547).cutoff/2-2 = (13094/6237:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable197.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 547).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 547

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 547).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 547).criticalRate j.val*(generalMeanRows 547).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 547).c*(generalMeanRows 547).criticalPoint j.val)).2-
      (generalMeanRows 547).J/2-(generalMeanRows 547).error (generalMeanGrid j.val)+
      (generalMeanRows 547).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 547).c)).2-
      (generalMeanRows 547).J/2-(generalMeanRows 547).error 4 := by
  have he : (generalMeanRows 547).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 547) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 547)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0547

/-! Kernel-checked entropy margins for general spectral rectangle 548. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0548
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4929379704) (.branch 2 (.leaf 4757674260) (.leaf 4593704511))) (.branch 5 (.branch 4 (.leaf 4437029303) (.leaf 4287238604)) (.branch 6 (.leaf 4143950792) (.leaf 4006810232)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3875485106) (.leaf 3749665471)) (.branch 10 (.leaf 3629061508) (.leaf 3513401937))) (.branch 13 (.branch 12 (.leaf 3402432593) (.leaf 3295915125)) (.branch 14 (.leaf 3193625824) (.leaf 3095354546))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3000903737) (.branch 17 (.leaf 2910087539) (.leaf 2822730970))) (.branch 20 (.branch 19 (.leaf 2738669174) (.leaf 2657746735)) (.branch 21 (.leaf 2579817039) (.leaf 2504741692)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2432389982) (.leaf 2362638381)) (.branch 25 (.leaf 2295370086) (.leaf 2230474591))) (.branch 28 (.branch 27 (.leaf 2167847295) (.leaf 2107389137)) (.branch 29 (.leaf 2049006252) (.leaf 1992609659)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1938114966) (.branch 32 (.leaf 1885442095) (.leaf 1834515030))) (.branch 35 (.branch 34 (.leaf 1785261576) (.leaf 1737613140)) (.branch 36 (.leaf 1691504520) (.leaf 1646873716)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1603661744) (.leaf 1561812470)) (.branch 40 (.leaf 1521272448) (.leaf 1481990773))) (.branch 43 (.branch 42 (.leaf 1443918943) (.leaf 1407010724)) (.branch 44 (.leaf 1371222029) (.leaf 1336510804))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1302836918) (.branch 47 (.leaf 1270162061) (.leaf 1238449647))) (.branch 50 (.branch 49 (.leaf 1207664727) (.leaf 1177773900)) (.branch 51 (.leaf 1148745236) (.leaf 1120548201)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1093153582) (.leaf 1066533424)) (.branch 55 (.leaf 1040660966) (.leaf 1015510578))) (.branch 58 (.branch 57 (.leaf 991057711) (.leaf 967278837)) (.branch 59 (.leaf 944151403) (.leaf 921653785))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 899765237) (.branch 62 (.leaf 878465854) (.leaf 857736531))) (.branch 65 (.branch 64 (.leaf 837558922) (.leaf 817915408)) (.branch 66 (.leaf 798789062) (.leaf 780163612)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 762023420) (.leaf 744353443)) (.branch 70 (.leaf 727139213) (.leaf 710366806))) (.branch 73 (.branch 72 (.leaf 694022821) (.leaf 678094356)) (.branch 74 (.leaf 662568981) (.leaf 647434726))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 632680051) (.branch 77 (.leaf 618293836) (.leaf 604265356))) (.branch 80 (.branch 79 (.leaf 590584266) (.leaf 577240589)) (.branch 81 (.leaf 564224694) (.leaf 551527284)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 539139382) (.leaf 527052320)) (.branch 85 (.leaf 515257721) (.leaf 503747492))) (.branch 88 (.branch 87 (.leaf 492513809) (.leaf 481549108)) (.branch 89 (.leaf 470846074) (.leaf 460397631)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 450196932) (.branch 92 (.leaf 440237351) (.leaf 430512473))) (.branch 95 (.branch 94 (.leaf 421016089) (.leaf 411742182)) (.branch 96 (.leaf 402684925) (.leaf 393838673)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 385197954) (.leaf 376757464)) (.branch 100 (.leaf 368512060) (.leaf 360456754))) (.branch 103 (.branch 102 (.leaf 352586709) (.leaf 344897231)) (.branch 104 (.leaf 337383767) (.leaf 330041895))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 322867324) (.leaf 315855888)) (.branch 108 (.leaf 309003541) (.leaf 302306353))) (.branch 111 (.branch 110 (.leaf 295760505) (.leaf 289362287)) (.branch 112 (.leaf 283108094) (.leaf 276994421)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 271017862) (.leaf 265175103)) (.branch 116 (.leaf 259462924) (.leaf 253878189))) (.branch 119 (.branch 118 (.leaf 248417853) (.leaf 243078947)) (.branch 120 (.leaf 237858588) (.leaf 232753965)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 548).prefactor = (297139710679041/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 548).cutoff/(generalMeanRows 548).c)).2 =
    (366697216494399/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 548).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 548).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 548).q*(generalMeanRows 548).c/2-2 = (1339/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable194.value]
    have hcontinuation : (generalMeanRows 548).q*(generalMeanRows 548).cutoff/2-2 = (6538/3123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable193.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 548).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 548

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 548).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 548).criticalRate j.val*(generalMeanRows 548).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 548).c*(generalMeanRows 548).criticalPoint j.val)).2-
      (generalMeanRows 548).J/2-(generalMeanRows 548).error (generalMeanGrid j.val)+
      (generalMeanRows 548).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 548).c)).2-
      (generalMeanRows 548).J/2-(generalMeanRows 548).error 4 := by
  have he : (generalMeanRows 548).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 548) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 548)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0548

/-! Kernel-checked entropy margins for general spectral rectangle 549. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0549
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4937971890) (.branch 2 (.leaf 4765967154) (.leaf 4601711597))) (.branch 5 (.branch 4 (.leaf 4444763295) (.leaf 4294711502)) (.branch 6 (.leaf 4151173932) (.leaf 4013794327)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3882240294) (.leaf 3756201349)) (.branch 10 (.leaf 3635387166) (.leaf 3519525994))) (.branch 13 (.branch 12 (.leaf 3408363224) (.leaf 3301660090)) (.branch 14 (.leaf 3199192493) (.leaf 3100749923))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3006134481) (.branch 17 (.leaf 2915159986) (.leaf 2827651149))) (.branch 20 (.branch 19 (.leaf 2743442829) (.leaf 2662379337)) (.branch 21 (.leaf 2584313805) (.leaf 2509107597)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2436629774) (.leaf 2366756593)) (.branch 25 (.leaf 2299371045) (.leaf 2234362433))) (.branch 28 (.branch 27 (.leaf 2171625975) (.leaf 2111062435)) (.branch 29 (.leaf 2052577785) (.leaf 1996082890)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1941493209) (.branch 32 (.leaf 1888728527) (.leaf 1837712693))) (.branch 35 (.branch 34 (.leaf 1788373388) (.leaf 1740641897)) (.branch 36 (.leaf 1694452908) (.leaf 1649744310)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1606457017) (.leaf 1564534797)) (.branch 40 (.leaf 1523924111) (.leaf 1484573966))) (.branch 43 (.branch 42 (.leaf 1446435775) (.leaf 1409463222)) (.branch 44 (.leaf 1373612146) (.leaf 1338840418))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1305107836) (.branch 47 (.leaf 1272376025) (.leaf 1240608334))) (.branch 50 (.branch 49 (.leaf 1209769754) (.leaf 1179826826)) (.branch 51 (.leaf 1150747564) (.leaf 1122501379)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1095059010) (.leaf 1068392452)) (.branch 55 (.leaf 1042474896) (.leaf 1017280670))) (.branch 58 (.branch 57 (.leaf 992785180) (.leaf 968964858)) (.branch 59 (.leaf 945797112) (.leaf 923260279))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 901333578) (.branch 62 (.leaf 879997070) (.leaf 859231614))) (.branch 65 (.branch 64 (.leaf 839018834) (.leaf 819341081)) (.branch 66 (.leaf 800181396) (.leaf 781523481)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 763351670) (.leaf 745650893)) (.branch 70 (.leaf 728406657) (.leaf 711605015))) (.branch 73 (.branch 72 (.leaf 695232542) (.leaf 679276312)) (.branch 74 (.leaf 663723876) (.leaf 648563241))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 633782848) (.branch 77 (.leaf 619371557) (.leaf 605318624))) (.branch 80 (.branch 79 (.leaf 591613688) (.leaf 578246752)) (.branch 81 (.leaf 565208169) (.leaf 552488627)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 540079133) (.leaf 527971002)) (.branch 85 (.leaf 516155844) (.leaf 504625552))) (.branch 88 (.branch 87 (.leaf 493372288) (.leaf 482388475)) (.branch 89 (.leaf 471666785) (.leaf 461200130)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 450981650) (.branch 92 (.leaf 441004709) (.leaf 431262881))) (.branch 95 (.branch 94 (.leaf 421749943) (.leaf 412459871)) (.branch 96 (.leaf 403386828) (.leaf 394525156)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 385869376) (.leaf 377414174)) (.branch 100 (.leaf 369154397) (.leaf 361085050))) (.branch 103 (.branch 102 (.leaf 353201287) (.leaf 345498407)) (.branch 104 (.leaf 337971846) (.leaf 330617176))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 323430100) (.leaf 316406443)) (.branch 108 (.leaf 309542152) (.leaf 302833290))) (.branch 111 (.branch 110 (.leaf 296276032) (.leaf 289866662)) (.branch 112 (.leaf 283601567) (.leaf 277477238)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 271490261) (.leaf 265637318)) (.branch 116 (.leaf 259915182) (.leaf 254320713))) (.branch 119 (.branch 118 (.leaf 248850859) (.leaf 243502648)) (.branch 120 (.leaf 238273189) (.leaf 233159669)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 549).prefactor = (4762522270427219/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 549).cutoff/(generalMeanRows 549).c)).2 =
    (366697216494399/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 549).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 549).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 549).q*(generalMeanRows 549).c/2-2 = (1339/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable194.value]
    have hcontinuation : (generalMeanRows 549).q*(generalMeanRows 549).cutoff/2-2 = (6538/3123:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable193.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 549).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 549

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 549).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 549).criticalRate j.val*(generalMeanRows 549).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 549).c*(generalMeanRows 549).criticalPoint j.val)).2-
      (generalMeanRows 549).J/2-(generalMeanRows 549).error (generalMeanGrid j.val)+
      (generalMeanRows 549).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 549).c)).2-
      (generalMeanRows 549).J/2-(generalMeanRows 549).error 4 := by
  have he : (generalMeanRows 549).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 549) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 549)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0549

/-! Kernel-checked entropy margins for general spectral rectangle 550. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0550
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4927840918) (.branch 2 (.leaf 4756159063) (.leaf 4592219118))) (.branch 5 (.branch 4 (.leaf 4435579072) (.leaf 4285828120)) (.branch 6 (.leaf 4142583939) (.leaf 4005490262)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3874214701) (.leaf 3748446800)) (.branch 10 (.leaf 3627896276) (.leaf 3512291435))) (.branch 13 (.branch 12 (.leaf 3401377739) (.leaf 3294916506)) (.branch 14 (.leaf 3192683729) (.leaf 3094469000))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3000074532) (.branch 17 (.leaf 2909314258) (.leaf 2822013015))) (.branch 20 (.branch 19 (.leaf 2738005789) (.leaf 2657137023)) (.branch 21 (.leaf 2579259984) (.leaf 2504236176)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2431934798) (.leaf 2362232249)) (.branch 25 (.leaf 2295011664) (.leaf 2230162489))) (.branch 28 (.branch 27 (.leaf 2167580084) (.leaf 2107165356)) (.branch 29 (.leaf 2048824421) (.leaf 1992468284)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1938012544) (.branch 32 (.leaf 1885377124) (.leaf 1834486011))) (.branch 35 (.branch 34 (.leaf 1785267020) (.leaf 1737651570)) (.branch 36 (.leaf 1691574478) (.leaf 1646973762)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1603790462) (.leaf 1561968470)) (.branch 40 (.leaf 1521454367) (.leaf 1482197278))) (.branch 43 (.branch 42 (.leaf 1444148732) (.leaf 1407262526)) (.branch 44 (.leaf 1371494608) (.leaf 1336802957))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1303147476) (.branch 47 (.leaf 1270489890) (.leaf 1238793649))) (.branch 50 (.branch 49 (.leaf 1208023838) (.leaf 1178147093)) (.branch 51 (.leaf 1149131519) (.leaf 1120946615)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1093563205) (.leaf 1066953367)) (.branch 55 (.leaf 1041090374) (.leaf 1015948630))) (.branch 58 (.branch 57 (.leaf 991503617) (.leaf 967731841)) (.branch 59 (.leaf 944610781) (.leaf 922118842))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 900235308) (.branch 62 (.leaf 878940305) (.leaf 858214755))) (.branch 65 (.branch 64 (.leaf 838040341) (.leaf 818399471)) (.branch 66 (.leaf 799275242) (.leaf 780651412)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 762512364) (.leaf 744843080)) (.branch 70 (.leaf 727629116) (.leaf 710856570))) (.branch 73 (.branch 72 (.leaf 694512063) (.leaf 678582713)) (.branch 74 (.leaf 663056111) (.leaf 647920306))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 633163777) (.branch 77 (.leaf 618775422) (.leaf 604744533))) (.branch 80 (.branch 79 (.leaf 591060784) (.leaf 577714211)) (.branch 81 (.leaf 564695198) (.leaf 551994466)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 539603050) (.leaf 527512296)) (.branch 85 (.leaf 515713841) (.leaf 504199602))) (.branch 88 (.branch 87 (.leaf 492961769) (.leaf 481992789)) (.branch 89 (.leaf 471285358) (.leaf 460832410)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 450627107) (.branch 92 (.leaf 440662834) (.leaf 430933185))) (.branch 95 (.branch 94 (.leaf 421431958) (.leaf 412153145)) (.branch 96 (.leaf 403090927) (.leaf 394239667)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 385593898) (.leaf 377148324)) (.branch 100 (.leaf 368897807) (.leaf 360837367))) (.branch 103 (.branch 102 (.leaf 352962172) (.leaf 345267533)) (.branch 104 (.leaf 337748900) (.leaf 330401859))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 323222123) (.leaf 316205528)) (.branch 108 (.leaf 309348034) (.leaf 302645713))) (.branch 111 (.branch 110 (.leaf 296094751) (.leaf 289691441)) (.branch 112 (.leaf 283432181) (.leaf 277313469)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 271331900) (.leaf 265484165)) (.branch 116 (.leaf 259767044) (.leaf 254177406))) (.branch 119 (.branch 118 (.leaf 248712205) (.leaf 243368476)) (.branch 120 (.leaf 238143336) (.leaf 233033977)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 550).prefactor = (2380534506625177/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 550).cutoff/(generalMeanRows 550).c)).2 =
    (368139177811301/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 550).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 550).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 550).q*(generalMeanRows 550).c/2-2 = (1339/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable194.value]
    have hcontinuation : (generalMeanRows 550).q*(generalMeanRows 550).cutoff/2-2 = (13094/6237:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable197.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 550).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 550

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 550).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 550).criticalRate j.val*(generalMeanRows 550).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 550).c*(generalMeanRows 550).criticalPoint j.val)).2-
      (generalMeanRows 550).J/2-(generalMeanRows 550).error (generalMeanGrid j.val)+
      (generalMeanRows 550).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 550).c)).2-
      (generalMeanRows 550).J/2-(generalMeanRows 550).error 4 := by
  have he : (generalMeanRows 550).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 550) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 550)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0550

/-! Kernel-checked entropy margins for general spectral rectangle 551. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0551
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4936395209) (.branch 2 (.leaf 4764415329) (.leaf 4600190798))) (.branch 5 (.branch 4 (.leaf 4443278839) (.leaf 4293267933)) (.branch 6 (.leaf 4149775093) (.leaf 4012443434)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3880939991) (.leaf 3754953768)) (.branch 10 (.leaf 3634193979) (.leaf 3518388458))) (.branch 13 (.branch 12 (.leaf 3407282226) (.leaf 3300636186)) (.branch 14 (.leaf 3198225942) (.leaf 3099840721))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3005282392) (.branch 17 (.leaf 2914364567) (.leaf 2826911777))) (.branch 20 (.branch 19 (.leaf 2742758721) (.leaf 2661749575)) (.branch 21 (.leaf 2583737349) (.leaf 2508583305)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2436156419) (.leaf 2366332872)) (.branch 25 (.leaf 2298995598) (.leaf 2234033851))) (.branch 28 (.branch 27 (.leaf 2171342809) (.leaf 2110823207)) (.branch 29 (.leaf 2052380997) (.leaf 1995927030)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1941376760) (.branch 32 (.leaf 1888649970) (.leaf 1837670514))) (.branch 35 (.branch 34 (.leaf 1788366083) (.leaf 1740667977)) (.branch 36 (.leaf 1694510899) (.leaf 1649832760)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1606574499) (.leaf 1564679907)) (.branch 40 (.leaf 1524095475) (.leaf 1484770240))) (.branch 43 (.branch 42 (.leaf 1446655645) (.leaf 1409705408)) (.branch 44 (.leaf 1373875400) (.leaf 1339123527))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1305409623) (.branch 47 (.leaf 1272695346) (.leaf 1240944083))) (.branch 50 (.branch 49 (.leaf 1210120859) (.leaf 1180192251)) (.branch 51 (.leaf 1151126308) (.leaf 1122892478)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1095461533) (.leaf 1068805503)) (.branch 55 (.leaf 1042897614) (.leaf 1017712226))) (.branch 58 (.branch 57 (.leaf 993224779) (.leaf 969411737)) (.branch 59 (.leaf 946250541) (.leaf 923719557))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 901798036) (.branch 62 (.leaf 880466066) (.leaf 859704538))) (.branch 65 (.branch 64 (.leaf 839495104) (.leaf 819820139)) (.branch 66 (.leaf 800662712) (.leaf 782006553)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 763836017) (.leaf 746136061)) (.branch 70 (.leaf 728892215) (.leaf 712090554))) (.branch 73 (.branch 72 (.leaf 695717674) (.leaf 679760672)) (.branch 74 (.leaf 664207117) (.leaf 649045037))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 634262893) (.branch 77 (.leaf 619849561) (.leaf 605794316))) (.branch 80 (.branch 79 (.leaf 592086812) (.leaf 578717071)) (.branch 81 (.leaf 565675459) (.leaf 552952679)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 540539753) (.leaf 528428010)) (.branch 85 (.leaf 516609074) (.leaf 505074848))) (.branch 88 (.branch 87 (.leaf 493817507) (.leaf 482829486)) (.branch 89 (.leaf 472103467) (.leaf 461632373)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 451409355) (.branch 92 (.leaf 441427785) (.leaf 431681246))) (.branch 95 (.branch 94 (.leaf 422163526) (.leaf 412868606)) (.branch 96 (.leaf 403790657) (.leaf 394924032)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 386263255) (.leaf 377803019)) (.branch 100 (.leaf 369538181) (.leaf 361463749))) (.branch 103 (.branch 102 (.leaf 353574883) (.leaf 345866886)) (.branch 104 (.leaf 338335202) (.leaf 330975407))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 323783207) (.leaf 316754433)) (.branch 108 (.leaf 309885034) (.leaf 303171079))) (.branch 111 (.branch 110 (.leaf 296608745) (.leaf 290194319)) (.branch 112 (.leaf 283924194) (.leaf 277794860)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 271802908) (.leaf 265945022)) (.branch 116 (.leaf 260217977) (.leaf 254618635))) (.branch 119 (.branch 118 (.leaf 249143947) (.leaf 243790942)) (.branch 120 (.leaf 238556732) (.leaf 233438504)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 551).prefactor = (74520840661217/15625000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 551).cutoff/(generalMeanRows 551).c)).2 =
    (368139177811301/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 551).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 551).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 551).q*(generalMeanRows 551).c/2-2 = (1339/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable194.value]
    have hcontinuation : (generalMeanRows 551).q*(generalMeanRows 551).cutoff/2-2 = (13094/6237:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable197.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 551).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 551

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 551).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 551).criticalRate j.val*(generalMeanRows 551).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 551).c*(generalMeanRows 551).criticalPoint j.val)).2-
      (generalMeanRows 551).J/2-(generalMeanRows 551).error (generalMeanGrid j.val)+
      (generalMeanRows 551).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 551).c)).2-
      (generalMeanRows 551).J/2-(generalMeanRows 551).error 4 := by
  have he : (generalMeanRows 551).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 551) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 551)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0551

/-! Kernel-checked entropy margins for general spectral rectangle 552. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0552
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5323564369) (.branch 2 (.leaf 5155766887) (.leaf 4995374154))) (.branch 5 (.branch 4 (.leaf 4841958573) (.leaf 4695123043)) (.branch 6 (.leaf 4554498291) (.leaf 4419740494)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4290529156) (.leaf 4166565186)) (.branch 10 (.leaf 4047569185) (.leaf 3933279891))) (.branch 13 (.branch 12 (.leaf 3823452768) (.leaf 3717858740)) (.branch 14 (.leaf 3616283024) (.leaf 3518524081))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3424392655) (.branch 17 (.leaf 3333710888) (.leaf 3246311519))) (.branch 20 (.branch 19 (.leaf 3162037145) (.leaf 3080739543)) (.branch 21 (.leaf 3002279048) (.leaf 2926523975)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2853350094) (.leaf 2782640140)) (.branch 25 (.leaf 2714283358) (.leaf 2648175090))) (.branch 28 (.branch 27 (.leaf 2584216384) (.leaf 2522313636)) (.branch 29 (.leaf 2462378256) (.leaf 2404326359)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2348078478) (.branch 32 (.leaf 2293559293) (.leaf 2240697385))) (.branch 35 (.branch 34 (.leaf 2189425000) (.leaf 2139677834)) (.branch 36 (.leaf 2091394830) (.leaf 2044517989)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1998992190) (.leaf 1954765031)) (.branch 40 (.leaf 1911786669) (.leaf 1870009676))) (.branch 43 (.branch 42 (.leaf 1829388905) (.leaf 1789881360)) (.branch 44 (.leaf 1751446080) (.leaf 1714044024))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1677637967) (.branch 47 (.leaf 1642192403) (.leaf 1607673449))) (.branch 50 (.branch 49 (.leaf 1574048760) (.leaf 1541287446)) (.branch 51 (.leaf 1509359997) (.leaf 1478238208)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1447895110) (.leaf 1418304909)) (.branch 55 (.leaf 1389442923) (.leaf 1361285525))) (.branch 58 (.branch 57 (.leaf 1333810090) (.leaf 1306994944)) (.branch 59 (.leaf 1280819316) (.leaf 1255263291))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1230307770) (.branch 62 (.leaf 1205934429) (.leaf 1182125680))) (.branch 65 (.branch 64 (.leaf 1158864635) (.leaf 1136135075)) (.branch 66 (.leaf 1113921412) (.leaf 1092208664)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1070982423) (.leaf 1050228831)) (.branch 70 (.leaf 1029934551) (.leaf 1010086744))) (.branch 73 (.branch 72 (.leaf 990673045) (.leaf 971681543)) (.branch 74 (.leaf 953100760) (.leaf 934919629))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 917127477) (.branch 77 (.leaf 899714008) (.leaf 882669286))) (.branch 80 (.branch 79 (.leaf 865983719) (.leaf 849648040)) (.branch 81 (.leaf 833653302) (.leaf 817990854)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 802652336) (.leaf 787629661)) (.branch 85 (.leaf 772915009) (.leaf 758500808))) (.branch 88 (.branch 87 (.leaf 744379735) (.leaf 730544693)) (.branch 89 (.leaf 716988812) (.leaf 703705434)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 690688107) (.branch 92 (.leaf 677930575) (.leaf 665426771))) (.branch 95 (.branch 94 (.leaf 653170812) (.leaf 641156987)) (.branch 96 (.leaf 629379754) (.leaf 617833732)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 606513696) (.leaf 595414570)) (.branch 100 (.leaf 584531422) (.leaf 573859458))) (.branch 103 (.branch 102 (.leaf 563394018) (.leaf 553130571)) (.branch 104 (.leaf 543064708) (.leaf 533192142))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 523508699) (.leaf 514010319)) (.branch 108 (.leaf 504693046) (.leaf 495553031))) (.branch 111 (.branch 110 (.leaf 486586522) (.leaf 477789865)) (.branch 112 (.leaf 469159501) (.leaf 460691959)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 452383856) (.leaf 444231894)) (.branch 116 (.leaf 436232857) (.leaf 428383607))) (.branch 119 (.branch 118 (.leaf 420681085) (.leaf 413122302)) (.branch 120 (.leaf 405704346) (.leaf 398424371)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 552).prefactor = (4632009897500649/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 552).cutoff/(generalMeanRows 552).c)).2 =
    (427342645851489/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 552).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 552).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 552).q*(generalMeanRows 552).c/2-2 = (1397/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable189.value]
    have hcontinuation : (generalMeanRows 552).q*(generalMeanRows 552).cutoff/2-2 = (8158/3817:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable200.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 552).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 552

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 552).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 552).criticalRate j.val*(generalMeanRows 552).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 552).c*(generalMeanRows 552).criticalPoint j.val)).2-
      (generalMeanRows 552).J/2-(generalMeanRows 552).error (generalMeanGrid j.val)+
      (generalMeanRows 552).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 552).c)).2-
      (generalMeanRows 552).J/2-(generalMeanRows 552).error 4 := by
  have he : (generalMeanRows 552).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 552) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 552)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0552

/-! Kernel-checked entropy margins for general spectral rectangle 553. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0553
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5241867463) (.branch 2 (.leaf 5074071544) (.leaf 4913703475))) (.branch 5 (.branch 4 (.leaf 4760334881) (.leaf 4613567906)) (.branch 6 (.leaf 4473032549) (.leaf 4338384281)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4209301920) (.leaf 4085485712)) (.branch 10 (.leaf 3966655613) (.leaf 3852549731))) (.branch 13 (.branch 12 (.leaf 3742922922) (.leaf 3637545514)) (.branch 14 (.leaf 3536202147) (.leaf 3438690718))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3344821421) (.branch 17 (.leaf 3254415862) (.leaf 3167306258))) (.branch 20 (.branch 19 (.leaf 3083334696) (.leaf 3002352458)) (.branch 21 (.leaf 2924219392) (.leaf 2848803342)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2775979614) (.leaf 2705630494)) (.branch 25 (.leaf 2637644788) (.leaf 2571917408))) (.branch 28 (.branch 27 (.leaf 2508348984) (.leaf 2446845504)) (.branch 29 (.leaf 2387317979) (.leaf 2329682136)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2273858130) (.branch 32 (.leaf 2219770270) (.leaf 2167346778))) (.branch 35 (.branch 34 (.leaf 2116519548) (.leaf 2067223934)) (.branch 36 (.leaf 2019398544) (.leaf 1972985055)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1927928030) (.leaf 1884174758)) (.branch 40 (.leaf 1841675094) (.leaf 1800381319))) (.branch 43 (.branch 42 (.leaf 1760248001) (.leaf 1721231866)) (.branch 44 (.leaf 1683291684) (.leaf 1646388152))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1610483790) (.branch 47 (.leaf 1575542843) (.leaf 1541531187))) (.branch 50 (.branch 49 (.leaf 1508416243) (.leaf 1476166893)) (.branch 51 (.leaf 1444753407) (.leaf 1414147364)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1384321587) (.leaf 1355250080)) (.branch 55 (.leaf 1326907964) (.leaf 1299271423))) (.branch 58 (.branch 57 (.leaf 1272317647) (.leaf 1246024782)) (.branch 59 (.leaf 1220371884) (.leaf 1195338871))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1170906482) (.branch 62 (.leaf 1147056233) (.leaf 1123770386))) (.branch 65 (.branch 64 (.leaf 1101031906) (.leaf 1078824428)) (.branch 66 (.leaf 1057132230) (.leaf 1035940195)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1015233789) (.leaf 994999026)) (.branch 70 (.leaf 975222452) (.leaf 955891112))) (.branch 73 (.branch 72 (.leaf 936992530) (.leaf 918514687)) (.branch 74 (.leaf 900446001) (.leaf 882775307))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 865491836) (.branch 77 (.leaf 848585200) (.leaf 832045374))) (.branch 80 (.branch 79 (.leaf 815862680) (.leaf 800027772)) (.branch 81 (.leaf 784531622) (.leaf 769365507)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 754520992) (.leaf 739989924)) (.branch 85 (.leaf 725764414) (.leaf 711836832))) (.branch 88 (.branch 87 (.leaf 698199790) (.leaf 684846137)) (.branch 89 (.leaf 671768947) (.leaf 658961511)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 646417327) (.branch 92 (.leaf 634130092) (.leaf 622093696))) (.branch 95 (.branch 94 (.leaf 610302211) (.leaf 598749889)) (.branch 96 (.leaf 587431150) (.leaf 576340577)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 565472911) (.leaf 554823046)) (.branch 100 (.leaf 544386020) (.leaf 534157012))) (.branch 103 (.branch 102 (.leaf 524131337) (.leaf 514304439)) (.branch 104 (.leaf 504671889) (.leaf 495229378))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 485972715) (.leaf 476897822)) (.branch 108 (.leaf 468000729) (.leaf 459277571))) (.branch 111 (.branch 110 (.leaf 450724586) (.leaf 442338108)) (.branch 112 (.leaf 434114568) (.leaf 426050487)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 418142477) (.leaf 410387232)) (.branch 116 (.leaf 402781532) (.leaf 395322238))) (.branch 119 (.branch 118 (.leaf 388006285) (.leaf 380830686)) (.branch 120 (.leaf 373792528) (.leaf 366888965)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 553).prefactor = (4639809859591029/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 553).cutoff/(generalMeanRows 553).c)).2 =
    (419590669047169/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 553).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 553).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 553).q*(generalMeanRows 553).c/2-2 = (1439/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable199.value]
    have hcontinuation : (generalMeanRows 553).q*(generalMeanRows 553).cutoff/2-2 = (8158/3817:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable200.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 553).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 553

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 553).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 553).criticalRate j.val*(generalMeanRows 553).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 553).c*(generalMeanRows 553).criticalPoint j.val)).2-
      (generalMeanRows 553).J/2-(generalMeanRows 553).error (generalMeanGrid j.val)+
      (generalMeanRows 553).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 553).c)).2-
      (generalMeanRows 553).J/2-(generalMeanRows 553).error 4 := by
  have he : (generalMeanRows 553).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 553) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 553)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0553

/-! Kernel-checked entropy margins for general spectral rectangle 554. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0554
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5172524216) (.branch 2 (.leaf 5004429664) (.leaf 4843787350))) (.branch 5 (.branch 4 (.leaf 4690168988) (.leaf 4543176731)) (.branch 6 (.leaf 4402440517) (.leaf 4267615695)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4138380899) (.leaf 4014436142)) (.branch 10 (.leaf 3895501099) (.leaf 3781313558))) (.branch 13 (.branch 12 (.leaf 3671628017) (.leaf 3566214414)) (.branch 14 (.leaf 3464856973) (.leaf 3367353149))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3273512672) (.branch 17 (.leaf 3183156669) (.leaf 3096116860))) (.branch 20 (.branch 19 (.leaf 3012234825) (.leaf 2931361326)) (.branch 21 (.leaf 2853355686) (.leaf 2778085216)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2705424689) (.leaf 2635255850)) (.branch 25 (.leaf 2567466966) (.leaf 2501952410))) (.branch 28 (.branch 27 (.leaf 2438612275) (.leaf 2377352013)) (.branch 29 (.leaf 2318082107) (.leaf 2260717756)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2205178594) (.branch 32 (.leaf 2151388417) (.leaf 2099274937))) (.branch 35 (.branch 34 (.leaf 2048769549) (.leaf 1999807114)) (.branch 36 (.leaf 1952325756) (.leaf 1906266675)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1861573969) (.leaf 1818194466)) (.branch 40 (.leaf 1776077577) (.leaf 1735175140))) (.branch 43 (.branch 42 (.leaf 1695441297) (.leaf 1656832353)) (.branch 44 (.leaf 1619306670) (.leaf 1582824544))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1547348107) (.branch 47 (.leaf 1512841223) (.leaf 1479269401))) (.branch 50 (.branch 49 (.leaf 1446599699) (.leaf 1414800653)) (.branch 51 (.leaf 1383842189) (.leaf 1353695557)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1324333260) (.leaf 1295728989)) (.branch 55 (.leaf 1267857565) (.leaf 1240694877))) (.branch 58 (.branch 57 (.leaf 1214217832) (.leaf 1188404301)) (.branch 59 (.leaf 1163233073) (.leaf 1138683810))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1114736999) (.branch 62 (.leaf 1091373918) (.leaf 1068576594))) (.branch 65 (.branch 64 (.leaf 1046327768) (.leaf 1024610858)) (.branch 66 (.leaf 1003409932) (.leaf 982709672)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 962495346) (.leaf 942752785)) (.branch 70 (.leaf 923468350) (.leaf 904628913))) (.branch 73 (.branch 72 (.leaf 886221831) (.leaf 868234924)) (.branch 74 (.leaf 850656456) (.leaf 833475110))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 816679977) (.branch 77 (.leaf 800260530) (.leaf 784206615))) (.branch 80 (.branch 79 (.leaf 768508425) (.leaf 753156496)) (.branch 81 (.leaf 738141683) (.leaf 723455151)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 709088363) (.leaf 695033061)) (.branch 85 (.leaf 681281262) (.leaf 667825243))) (.branch 88 (.branch 87 (.leaf 654657529) (.leaf 641770886)) (.branch 89 (.leaf 629158307) (.leaf 616813009)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 604728417) (.branch 92 (.leaf 592898161) (.leaf 581316066))) (.branch 95 (.branch 94 (.leaf 569976145) (.leaf 558872590)) (.branch 96 (.leaf 547999766) (.leaf 537352208)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 526924608) (.leaf 516711813)) (.branch 100 (.leaf 506708820) (.leaf 496910768))) (.branch 103 (.branch 102 (.leaf 487312935) (.leaf 477910730)) (.branch 104 (.leaf 468699694) (.leaf 459675487))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 450833892) (.leaf 442170804)) (.branch 108 (.leaf 433682232) (.leaf 425364289))) (.branch 111 (.branch 110 (.leaf 417213195) (.leaf 409225268)) (.branch 112 (.leaf 401396923) (.leaf 393724669)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 386205104) (.leaf 378834915)) (.branch 116 (.leaf 371610874) (.leaf 364529832))) (.branch 119 (.branch 118 (.leaf 357588723) (.leaf 350784554)) (.branch 120 (.leaf 344114410) (.leaf 337575446)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 554).prefactor = (4642351893164733/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 554).cutoff/(generalMeanRows 554).c)).2 =
    (204510311798199/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 554).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 554).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 554).q*(generalMeanRows 554).c/2-2 = (1481/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable171.value]
    have hcontinuation : (generalMeanRows 554).q*(generalMeanRows 554).cutoff/2-2 = (678/319:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable198.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 554).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 554

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 554).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 554).criticalRate j.val*(generalMeanRows 554).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 554).c*(generalMeanRows 554).criticalPoint j.val)).2-
      (generalMeanRows 554).J/2-(generalMeanRows 554).error (generalMeanGrid j.val)+
      (generalMeanRows 554).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 554).c)).2-
      (generalMeanRows 554).J/2-(generalMeanRows 554).error 4 := by
  have he : (generalMeanRows 554).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 554) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 554)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0554

/-! Kernel-checked entropy margins for general spectral rectangle 555. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0555
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5251585194) (.branch 2 (.leaf 5083477369) (.leaf 4922804501))) (.branch 5 (.branch 4 (.leaf 4769138304) (.leaf 4622080984)) (.branch 6 (.leaf 4481262575) (.leaf 4346338565)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4216987760) (.leaf 4092910384)) (.branch 10 (.leaf 3973826346) (.leaf 3859473699))) (.branch 13 (.branch 12 (.leaf 3749607226) (.leaf 3643997170)) (.branch 14 (.leaf 3542428079) (.leaf 3444697746))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3350616254) (.branch 17 (.leaf 3260005091) (.leaf 3172696351))) (.branch 20 (.branch 19 (.leaf 3088531993) (.leaf 3007363163)) (.branch 21 (.leaf 2929049577) (.leaf 2853458937)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2780466413) (.leaf 2709954146)) (.branch 25 (.leaf 2641810800) (.leaf 2575931145))) (.branch 28 (.branch 27 (.leaf 2512215667) (.leaf 2450570212)) (.branch 29 (.leaf 2390905651) (.leaf 2333137570)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2277185983) (.branch 32 (.leaf 2222975065) (.leaf 2170432899))) (.branch 35 (.branch 34 (.leaf 2119491248) (.leaf 2070085334)) (.branch 36 (.leaf 2022153636) (.leaf 1975637703)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1930481976) (.leaf 1886633621)) (.branch 40 (.leaf 1844042375) (.leaf 1802660402))) (.branch 43 (.branch 42 (.leaf 1762442157) (.leaf 1723344256)) (.branch 44 (.leaf 1685325361) (.leaf 1648346064))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1612368781) (.branch 47 (.leaf 1577357660) (.leaf 1543278480))) (.branch 50 (.branch 49 (.leaf 1510098568) (.leaf 1477786715)) (.branch 51 (.leaf 1446313102) (.leaf 1415649221)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1385767815) (.leaf 1356642805)) (.branch 55 (.leaf 1328249236) (.leaf 1300563214))) (.branch 58 (.branch 57 (.leaf 1273561858) (.leaf 1247223242)) (.branch 59 (.leaf 1221526355) (.leaf 1196451047))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1171977994) (.branch 62 (.leaf 1148088652) (.leaf 1124765221))) (.branch 65 (.branch 64 (.leaf 1101990609) (.leaf 1079748397)) (.branch 66 (.leaf 1058022808) (.leaf 1036798674)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1016061410) (.leaf 995796985)) (.branch 70 (.leaf 975991895) (.leaf 956633142))) (.branch 73 (.branch 72 (.leaf 937708207) (.leaf 919205031)) (.branch 74 (.leaf 901111991) (.leaf 883417883))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 866111901) (.branch 77 (.leaf 849183622) (.leaf 832622988))) (.branch 80 (.branch 79 (.leaf 816420286) (.leaf 800566140)) (.branch 81 (.leaf 785051491) (.leaf 769867586)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 755005963) (.leaf 740458441)) (.branch 85 (.leaf 726217106) (.leaf 712274301))) (.branch 88 (.branch 87 (.leaf 698622617) (.leaf 685254877)) (.branch 89 (.leaf 672164135) (.leaf 659343659)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 646786927) (.branch 92 (.leaf 634487618) (.leaf 622439601))) (.branch 95 (.branch 94 (.leaf 610636932) (.leaf 599073843)) (.branch 96 (.leaf 587744738) (.leaf 576644185)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 565766910) (.leaf 555107791)) (.branch 100 (.leaf 544661852) (.leaf 534424259))) (.branch 103 (.branch 102 (.leaf 524390313) (.leaf 514555447)) (.branch 104 (.leaf 504915218) (.leaf 495465307))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 486201511) (.leaf 477119742)) (.branch 108 (.leaf 468216020) (.leaf 459486469))) (.branch 111 (.branch 110 (.leaf 450927319) (.leaf 442534894)) (.branch 112 (.leaf 434305617) (.leaf 426236002)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 418322649) (.leaf 410562249)) (.branch 116 (.leaf 402951573) (.leaf 395487473))) (.branch 119 (.branch 118 (.leaf 388166880) (.leaf 380986800)) (.branch 120 (.leaf 373944313) (.leaf 367036568)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 555).prefactor = (4641081102085827/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 555).cutoff/(generalMeanRows 555).c)).2 =
    (209075391994591/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 555).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 555).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 555).q*(generalMeanRows 555).c/2-2 = (1439/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable199.value]
    have hcontinuation : (generalMeanRows 555).q*(generalMeanRows 555).cutoff/2-2 = (16294/7645:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable201.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 555).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 555

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 555).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 555).criticalRate j.val*(generalMeanRows 555).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 555).c*(generalMeanRows 555).criticalPoint j.val)).2-
      (generalMeanRows 555).J/2-(generalMeanRows 555).error (generalMeanGrid j.val)+
      (generalMeanRows 555).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 555).c)).2-
      (generalMeanRows 555).J/2-(generalMeanRows 555).error 4 := by
  have he : (generalMeanRows 555).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 555) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 555)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0555

/-! Kernel-checked entropy margins for general spectral rectangle 556. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0556
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5260464341) (.branch 2 (.leaf 5092072287) (.leaf 4931127760))) (.branch 5 (.branch 4 (.leaf 4777201751) (.leaf 4629895793)) (.branch 6 (.leaf 4488839295) (.leaf 4353687161)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4224117656) (.leaf 4099830495)) (.branch 10 (.leaf 3980545116) (.leaf 3865999126))) (.branch 13 (.branch 12 (.leaf 3755946895) (.leaf 3650158279)) (.branch 14 (.leaf 3548417459) (.leaf 3450521888))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3356281327) (.branch 17 (.leaf 3265516963) (.leaf 3178060605))) (.branch 20 (.branch 19 (.leaf 3093753945) (.leaf 3012447880)) (.branch 21 (.leaf 2934001884) (.leaf 2858283439)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2785167502) (.leaf 2714536016)) (.branch 25 (.leaf 2646277456) (.leaf 2580286415))) (.branch 28 (.branch 27 (.leaf 2516463210) (.leaf 2454713527)) (.branch 29 (.leaf 2394948088) (.leaf 2337082335)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2281036148) (.branch 32 (.leaf 2226733573) (.leaf 2174102571))) (.branch 35 (.branch 34 (.leaf 2123074790) (.leaf 2073585342)) (.branch 36 (.leaf 2025572604) (.leaf 1978978024)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1933745949) (.leaf 1889823457)) (.branch 40 (.leaf 1847160200) (.leaf 1805708260))) (.branch 43 (.branch 42 (.leaf 1765422016) (.leaf 1726258010)) (.branch 44 (.leaf 1688174835) (.leaf 1651133014))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1615094903) (.branch 47 (.leaf 1580024587) (.leaf 1545887787))) (.branch 50 (.branch 49 (.leaf 1512651776) (.leaf 1480285291)) (.branch 51 (.leaf 1448758464) (.leaf 1418042738)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1388110810) (.leaf 1358936557)) (.branch 55 (.leaf 1330494981) (.leaf 1302762149))) (.branch 58 (.branch 57 (.leaf 1275715140) (.leaf 1249331992)) (.branch 59 (.leaf 1223591657) (.leaf 1198473954))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1173959522) (.branch 62 (.leaf 1150029789) (.leaf 1126666924))) (.branch 65 (.branch 64 (.leaf 1103853806) (.leaf 1081573988)) (.branch 66 (.leaf 1059811666) (.leaf 1038551647)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1017779321) (.leaf 997480634)) (.branch 70 (.leaf 977642059) (.leaf 958250575))) (.branch 73 (.branch 72 (.leaf 939293643) (.leaf 920759182)) (.branch 74 (.leaf 902635551) (.leaf 884911526))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 867576285) (.branch 77 (.leaf 850619384) (.leaf 834030750))) (.branch 80 (.branch 79 (.leaf 817800653) (.leaf 801919702)) (.branch 81 (.leaf 786378821) (.leaf 771169244)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 756282494) (.leaf 741710375)) (.branch 85 (.leaf 727444961) (.leaf 713478583))) (.branch 88 (.branch 87 (.leaf 699803817) (.leaf 686413476)) (.branch 89 (.leaf 673300600) (.leaf 660458448)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 647880486) (.branch 92 (.leaf 635560381) (.leaf 623491994))) (.branch 95 (.branch 94 (.leaf 611669369) (.leaf 600086730)) (.branch 96 (.leaf 588738471) (.leaf 577619150)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 566723484) (.leaf 556046343)) (.branch 100 (.leaf 545582743) (.leaf 535327840))) (.branch 103 (.branch 102 (.leaf 525276929) (.leaf 515425434)) (.branch 104 (.leaf 505768906) (.leaf 496303018))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 487023559) (.leaf 477926435)) (.branch 108 (.leaf 469007658) (.leaf 460263348))) (.branch 111 (.branch 110 (.leaf 451689726) (.leaf 443283113)) (.branch 112 (.leaf 435039922) (.leaf 426956663)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 419029931) (.leaf 411256410)) (.branch 116 (.leaf 403632866) (.leaf 396156146))) (.branch 119 (.branch 118 (.leaf 388823175) (.leaf 381630956)) (.branch 120 (.leaf 374576561) (.leaf 367657138)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 556).prefactor = (4648928035861097/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 556).cutoff/(generalMeanRows 556).c)).2 =
    (209075391994591/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 556).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 556).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 556).q*(generalMeanRows 556).c/2-2 = (1439/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable199.value]
    have hcontinuation : (generalMeanRows 556).q*(generalMeanRows 556).cutoff/2-2 = (16294/7645:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable201.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 556).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 556

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 556).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 556).criticalRate j.val*(generalMeanRows 556).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 556).c*(generalMeanRows 556).criticalPoint j.val)).2-
      (generalMeanRows 556).J/2-(generalMeanRows 556).error (generalMeanGrid j.val)+
      (generalMeanRows 556).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 556).c)).2-
      (generalMeanRows 556).J/2-(generalMeanRows 556).error 4 := by
  have he : (generalMeanRows 556).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 556) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 556)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0556

/-! Kernel-checked entropy margins for general spectral rectangle 557. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0557
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5181305260) (.branch 2 (.leaf 5012925346) (.leaf 4852010320))) (.branch 5 (.branch 4 (.leaf 4698131170) (.leaf 4550889375)) (.branch 6 (.leaf 4409914243) (.leaf 4274860538)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4145406348) (.leaf 4021251178)) (.branch 10 (.leaf 3902114227) (.leaf 3787732838))) (.branch 13 (.branch 12 (.leaf 3677861091) (.leaf 3572268535)) (.branch 14 (.leaf 3470739026) (.leaf 3373069677))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3279069893) (.branch 17 (.leaf 3188560498) (.leaf 3101372928))) (.branch 20 (.branch 19 (.leaf 3017348492) (.leaf 2936337699)) (.branch 21 (.leaf 2858199635) (.leaf 2782801384)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2710017506) (.leaf 2639729546)) (.branch 25 (.leaf 2571825581) (.leaf 2506199805))) (.branch 28 (.branch 27 (.leaf 2442752142) (.leaf 2381387883)) (.branch 29 (.leaf 2322017358) (.leaf 2264555624)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2208922177) (.branch 32 (.leaf 2155040684) (.leaf 2102838734))) (.branch 35 (.branch 34 (.leaf 2052247607) (.leaf 2003202051)) (.branch 36 (.leaf 1955640088) (.leaf 1909502815)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1864734237) (.leaf 1821281092)) (.branch 40 (.leaf 1779092703) (.leaf 1738120830))) (.branch 43 (.branch 42 (.leaf 1698319533) (.leaf 1659645046)) (.branch 44 (.leaf 1622055657) (.leaf 1585511598))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1549974935) (.branch 47 (.leaf 1515409472) (.leaf 1481780656))) (.branch 50 (.branch 49 (.leaf 1449055494) (.leaf 1417202464)) (.branch 51 (.leaf 1386191444) (.leaf 1355993634)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1326581491) (.leaf 1297928661)) (.branch 55 (.leaf 1270009921) (.leaf 1242801121))) (.branch 58 (.branch 57 (.leaf 1216279127) (.leaf 1190421775)) (.branch 59 (.leaf 1165207816) (.leaf 1140616876))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1116629412) (.branch 62 (.leaf 1093226670) (.leaf 1070390644))) (.branch 65 (.branch 64 (.leaf 1048104048) (.leaf 1026350271)) (.branch 66 (.leaf 1005113353) (.leaf 984377951)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 964129309) (.leaf 944353232)) (.branch 70 (.leaf 925036060) (.leaf 906164640))) (.branch 73 (.branch 72 (.leaf 887726310) (.leaf 869708868)) (.branch 74 (.leaf 852100557) (.leaf 834890044))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 818066399) (.branch 77 (.leaf 801619079) (.leaf 785537909))) (.branch 80 (.branch 79 (.leaf 769813070) (.leaf 754435079)) (.branch 81 (.leaf 739394776) (.leaf 724683312)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 710292134) (.leaf 696212971)) (.branch 85 (.leaf 682437827) (.leaf 668958965))) (.branch 88 (.branch 87 (.leaf 655768897) (.leaf 642860377)) (.branch 89 (.leaf 630226387) (.leaf 617860130)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 605755023) (.branch 92 (.leaf 593904684) (.leaf 582302927))) (.branch 95 (.branch 94 (.leaf 570943755) (.leaf 559821350)) (.branch 96 (.leaf 548930069) (.leaf 538264435)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 527819132) (.leaf 517588999)) (.branch 100 (.leaf 507569025) (.leaf 497754340))) (.branch 103 (.branch 102 (.leaf 488140213) (.leaf 478722047)) (.branch 104 (.leaf 469495374) (.leaf 460455847))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 451599242) (.leaf 442921447)) (.branch 108 (.leaf 434418465) (.leaf 426086401))) (.branch 111 (.branch 110 (.leaf 417921470) (.leaf 409919982)) (.branch 112 (.leaf 402078348) (.leaf 394393069)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 386860738) (.leaf 379478038)) (.branch 116 (.leaf 372241732) (.leaf 365148670))) (.branch 119 (.branch 118 (.leaf 358195777) (.leaf 351380058)) (.branch 120 (.leaf 344698590) (.leaf 338148525)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 557).prefactor = (4650232899772679/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 557).cutoff/(generalMeanRows 557).c)).2 =
    (204510311798199/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 557).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 557).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 557).q*(generalMeanRows 557).c/2-2 = (1481/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable171.value]
    have hcontinuation : (generalMeanRows 557).q*(generalMeanRows 557).cutoff/2-2 = (678/319:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable198.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 557).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 557

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 557).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 557).criticalRate j.val*(generalMeanRows 557).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 557).c*(generalMeanRows 557).criticalPoint j.val)).2-
      (generalMeanRows 557).J/2-(generalMeanRows 557).error (generalMeanGrid j.val)+
      (generalMeanRows 557).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 557).c)).2-
      (generalMeanRows 557).J/2-(generalMeanRows 557).error 4 := by
  have he : (generalMeanRows 557).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 557) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 557)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0557

/-! Kernel-checked entropy margins for general spectral rectangle 558. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0558
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5190101212) (.branch 2 (.leaf 5021435450) (.leaf 4860247250))) (.branch 5 (.branch 4 (.leaf 4706106870) (.leaf 4558615111)) (.branch 6 (.leaf 4417400655) (.leaf 4282117679)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4152443724) (.leaf 4028077784)) (.branch 10 (.leaf 3908738583) (.leaf 3794163015))) (.branch 13 (.branch 12 (.leaf 3684104747) (.leaf 3578332934)) (.branch 14 (.leaf 3476631065) (.leaf 3378795909))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3284636548) (.branch 17 (.leaf 3193973502) (.leaf 3106637918))) (.branch 20 (.branch 19 (.leaf 3022470840) (.leaf 2941322521)) (.branch 21 (.leaf 2863051807) (.leaf 2787525557)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2714618119) (.leaf 2644210836)) (.branch 25 (.leaf 2576191595) (.leaf 2510454411))) (.branch 28 (.branch 27 (.leaf 2446899037) (.leaf 2385430604)) (.branch 29 (.leaf 2325959290) (.leaf 2268400007)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2212672114) (.branch 32 (.leaf 2158699151) (.leaf 2106408581))) (.branch 35 (.branch 34 (.leaf 2055731569) (.leaf 2006602752)) (.branch 36 (.leaf 1958960046) (.leaf 1912744449)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1867899870) (.leaf 1824372958)) (.branch 40 (.leaf 1782112949) (.leaf 1741071520))) (.branch 43 (.branch 42 (.leaf 1701202655) (.leaf 1662462513)) (.branch 44 (.leaf 1624809312) (.leaf 1588203214))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1552606223) (.branch 47 (.leaf 1517982080) (.leaf 1484296175))) (.branch 50 (.branch 49 (.leaf 1451515457) (.leaf 1419608353)) (.branch 51 (.leaf 1388544687) (.leaf 1358295613)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1328833538) (.leaf 1300132066)) (.branch 55 (.leaf 1272165931) (.leaf 1244910940))) (.branch 58 (.branch 57 (.leaf 1218343922) (.leaf 1192442673)) (.branch 59 (.leaf 1167185910) (.leaf 1142553224))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1118525038) (.branch 62 (.leaf 1095082567) (.leaf 1072207774))) (.branch 65 (.branch 64 (.leaf 1049883343) (.leaf 1028092636)) (.branch 66 (.leaf 1006819666) (.leaf 986049063)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 965766047) (.leaf 945956397)) (.branch 70 (.leaf 926606431) (.leaf 907702975))) (.branch 73 (.branch 72 (.leaf 889233343) (.leaf 871185314)) (.branch 74 (.leaf 853547111) (.leaf 836307381))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 819455175) (.branch 77 (.leaf 802979933) (.leaf 786871464))) (.branch 80 (.branch 79 (.leaf 771119930) (.leaf 755715832)) (.branch 81 (.leaf 740649997) (.leaf 725913558)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 711497949) (.leaf 697394885)) (.branch 85 (.leaf 683596356) (.leaf 670094611))) (.branch 88 (.branch 87 (.leaf 656882152) (.leaf 643951717)) (.branch 89 (.leaf 631296279) (.leaf 618909030)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 606783372) (.branch 92 (.leaf 594912916) (.leaf 583291463))) (.branch 95 (.branch 94 (.leaf 571913007) (.leaf 560771721)) (.branch 96 (.leaf 549861950) (.leaf 539178210)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 528715175) (.leaf 518467675)) (.branch 100 (.leaf 508430690) (.leaf 498599343))) (.branch 103 (.branch 102 (.leaf 488968895) (.leaf 479534741)) (.branch 104 (.leaf 470292404) (.leaf 461237532))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 452365891) (.leaf 443673365)) (.branch 108 (.leaf 435155947) (.leaf 426809739))) (.branch 111 (.branch 110 (.leaf 418630947) (.leaf 410615876)) (.branch 112 (.leaf 402760929) (.leaf 395062603)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 387517486) (.leaf 380122252)) (.branch 116 (.leaf 372873662) (.leaf 365768558))) (.branch 119 (.branch 118 (.leaf 358803862) (.leaf 351976572)) (.branch 120 (.leaf 345283762) (.leaf 338722577)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 558).prefactor = (1164531821358037/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 558).cutoff/(generalMeanRows 558).c)).2 =
    (204510311798199/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 558).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 558).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 558).q*(generalMeanRows 558).c/2-2 = (1481/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable171.value]
    have hcontinuation : (generalMeanRows 558).q*(generalMeanRows 558).cutoff/2-2 = (678/319:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable198.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 558).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 558

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 558).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 558).criticalRate j.val*(generalMeanRows 558).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 558).c*(generalMeanRows 558).criticalPoint j.val)).2-
      (generalMeanRows 558).J/2-(generalMeanRows 558).error (generalMeanGrid j.val)+
      (generalMeanRows 558).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 558).c)).2-
      (generalMeanRows 558).J/2-(generalMeanRows 558).error 4 := by
  have he : (generalMeanRows 558).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 558) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 558)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0558

/-! Kernel-checked entropy margins for general spectral rectangle 559. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0559
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5157867064) (.branch 2 (.leaf 4990276850) (.leaf 4830089499))) (.branch 5 (.branch 4 (.leaf 4676881514) (.leaf 4530259419)) (.branch 6 (.leaf 4389857134) (.leaf 4255333638)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4126370874) (.leaf 4002671870)) (.branch 10 (.leaf 3883959045) (.leaf 3769972686))) (.branch 13 (.branch 12 (.leaf 3660469564) (.leaf 3555221685)) (.branch 14 (.leaf 3454015149) (.leaf 3356649117))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3262934865) (.branch 17 (.leaf 3172694920) (.leaf 3085762273))) (.branch 20 (.branch 19 (.leaf 3001979650) (.leaf 2921198849)) (.branch 21 (.leaf 2843280125) (.leaf 2768091630)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2695508893) (.leaf 2625414334)) (.branch 25 (.leaf 2557696827) (.leaf 2492251286))) (.branch 28 (.branch 27 (.leaf 2428978285) (.leaf 2367783703)) (.branch 29 (.leaf 2308578401) (.leaf 2251277910)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2195802156) (.branch 32 (.leaf 2142075189) (.leaf 2090024943))) (.branch 35 (.branch 34 (.leaf 2039583001) (.leaf 1990684387)) (.branch 36 (.leaf 1943267362) (.leaf 1897273239)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1852646211) (.leaf 1809333182)) (.branch 40 (.leaf 1767283619) (.leaf 1726449406))) (.branch 43 (.branch 42 (.leaf 1686784713) (.leaf 1648245868)) (.branch 44 (.leaf 1610791236) (.leaf 1574381114))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1538977624) (.branch 47 (.leaf 1504544615) (.leaf 1471047570))) (.branch 50 (.branch 49 (.leaf 1438453522) (.leaf 1406730970)) (.branch 51 (.leaf 1375849805) (.leaf 1345781236)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1316497722) (.leaf 1287972910)) (.branch 55 (.leaf 1260181570) (.leaf 1233099545))) (.branch 58 (.branch 57 (.leaf 1206703690) (.leaf 1180971827)) (.branch 59 (.leaf 1155882692) (.leaf 1131415895))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1107551874) (.branch 62 (.leaf 1084271855) (.leaf 1061557814))) (.branch 65 (.branch 64 (.leaf 1039392443) (.leaf 1017759111)) (.branch 66 (.leaf 996641836) (.leaf 976025255)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 955894590) (.leaf 936235626)) (.branch 70 (.leaf 917034683) (.leaf 898278589))) (.branch 73 (.branch 72 (.leaf 879954661) (.leaf 862050679)) (.branch 74 (.leaf 844554870) (.leaf 827455881))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 810742768) (.branch 77 (.leaf 794404971) (.leaf 778432302))) (.branch 80 (.branch 79 (.leaf 762814927) (.leaf 747543350)) (.branch 81 (.leaf 732608400) (.leaf 718001216)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 703713234) (.leaf 689736177)) (.branch 85 (.leaf 676062037) (.leaf 662683070))) (.branch 88 (.branch 87 (.leaf 649591784) (.leaf 636780924)) (.branch 89 (.leaf 624243469) (.leaf 611972618)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 599961783) (.branch 92 (.leaf 588204580) (.leaf 576694822))) (.branch 95 (.branch 94 (.leaf 565426510) (.leaf 554393827)) (.branch 96 (.leaf 543591128) (.leaf 533012939)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 522653945) (.leaf 512508987)) (.branch 100 (.leaf 502573056) (.leaf 492841287))) (.branch 103 (.branch 102 (.leaf 483308952) (.leaf 473971458)) (.branch 104 (.leaf 464824343) (.leaf 455863265))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 447084005) (.leaf 438482459)) (.branch 108 (.leaf 430054634) (.leaf 421796645))) (.branch 111 (.branch 110 (.leaf 413704711) (.leaf 405775153)) (.branch 112 (.leaf 398004388) (.leaf 390388926)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 382925370) (.leaf 375610409)) (.branch 116 (.leaf 368440817) (.leaf 361413452))) (.branch 119 (.branch 118 (.leaf 354525250) (.leaf 347773224)) (.branch 120 (.leaf 341154463) (.leaf 334666128)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 559).prefactor = (4599603533063833/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 559).cutoff/(generalMeanRows 559).c)).2 =
    (80657989777483/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 559).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 559).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 559).q*(generalMeanRows 559).c/2-2 = (1481/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable171.value]
    have hcontinuation : (generalMeanRows 559).q*(generalMeanRows 559).cutoff/2-2 = (578/275:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable129.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 559).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 559

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 559).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 559).criticalRate j.val*(generalMeanRows 559).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 559).c*(generalMeanRows 559).criticalPoint j.val)).2-
      (generalMeanRows 559).J/2-(generalMeanRows 559).error (generalMeanGrid j.val)+
      (generalMeanRows 559).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 559).c)).2-
      (generalMeanRows 559).J/2-(generalMeanRows 559).error 4 := by
  have he : (generalMeanRows 559).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 559) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 559)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0559

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock07 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 7 i) := by
  fin_cases i
  · exact EntropyRow0490.numerical
  · exact EntropyRow0491.numerical
  · exact EntropyRow0492.numerical
  · exact EntropyRow0493.numerical
  · exact EntropyRow0494.numerical
  · exact EntropyRow0495.numerical
  · exact EntropyRow0496.numerical
  · exact EntropyRow0497.numerical
  · exact EntropyRow0498.numerical
  · exact EntropyRow0499.numerical
  · exact EntropyRow0500.numerical
  · exact EntropyRow0501.numerical
  · exact EntropyRow0502.numerical
  · exact EntropyRow0503.numerical
  · exact EntropyRow0504.numerical
  · exact EntropyRow0505.numerical
  · exact EntropyRow0506.numerical
  · exact EntropyRow0507.numerical
  · exact EntropyRow0508.numerical
  · exact EntropyRow0509.numerical
  · exact EntropyRow0510.numerical
  · exact EntropyRow0511.numerical
  · exact EntropyRow0512.numerical
  · exact EntropyRow0513.numerical
  · exact EntropyRow0514.numerical
  · exact EntropyRow0515.numerical
  · exact EntropyRow0516.numerical
  · exact EntropyRow0517.numerical
  · exact EntropyRow0518.numerical
  · exact EntropyRow0519.numerical
  · exact EntropyRow0520.numerical
  · exact EntropyRow0521.numerical
  · exact EntropyRow0522.numerical
  · exact EntropyRow0523.numerical
  · exact EntropyRow0524.numerical
  · exact EntropyRow0525.numerical
  · exact EntropyRow0526.numerical
  · exact EntropyRow0527.numerical
  · exact EntropyRow0528.numerical
  · exact EntropyRow0529.numerical
  · exact EntropyRow0530.numerical
  · exact EntropyRow0531.numerical
  · exact EntropyRow0532.numerical
  · exact EntropyRow0533.numerical
  · exact EntropyRow0534.numerical
  · exact EntropyRow0535.numerical
  · exact EntropyRow0536.numerical
  · exact EntropyRow0537.numerical
  · exact EntropyRow0538.numerical
  · exact EntropyRow0539.numerical
  · exact EntropyRow0540.numerical
  · exact EntropyRow0541.numerical
  · exact EntropyRow0542.numerical
  · exact EntropyRow0543.numerical
  · exact EntropyRow0544.numerical
  · exact EntropyRow0545.numerical
  · exact EntropyRow0546.numerical
  · exact EntropyRow0547.numerical
  · exact EntropyRow0548.numerical
  · exact EntropyRow0549.numerical
  · exact EntropyRow0550.numerical
  · exact EntropyRow0551.numerical
  · exact EntropyRow0552.numerical
  · exact EntropyRow0553.numerical
  · exact EntropyRow0554.numerical
  · exact EntropyRow0555.numerical
  · exact EntropyRow0556.numerical
  · exact EntropyRow0557.numerical
  · exact EntropyRow0558.numerical
  · exact EntropyRow0559.numerical
end SingularValueBounds.KL.Certificates
