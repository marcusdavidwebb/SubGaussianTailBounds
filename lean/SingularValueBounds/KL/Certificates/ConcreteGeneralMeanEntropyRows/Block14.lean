import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block00
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block01
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block02
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block03
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block04
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block05
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block06
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block07
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block08
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block11
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block15
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block16
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block17
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block18
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block19
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block20
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block21
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 980. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0980
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6162938361) (.branch 2 (.leaf 5980022132) (.leaf 5804468994))) (.branch 5 (.branch 4 (.leaf 5635885390) (.leaf 5473904945)) (.branch 6 (.leaf 5318186064) (.leaf 5168409801)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5024277948) (.leaf 4885511335)) (.branch 10 (.leaf 4751848301) (.leaf 4623043313))) (.branch 13 (.branch 12 (.leaf 4498865728) (.leaf 4379098666)) (.branch 14 (.leaf 4263537995) (.leaf 4151991403))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4044277553) (.branch 17 (.leaf 3940225321) (.leaf 3839673084))) (.branch 20 (.branch 19 (.leaf 3742468083) (.leaf 3648465827)) (.branch 21 (.leaf 3557529556) (.leaf 3469529734)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3384343593) (.leaf 3301854707)) (.branch 25 (.leaf 3221952598) (.leaf 3144532371))) (.branch 28 (.branch 27 (.leaf 3069494380) (.leaf 2996743910)) (.branch 29 (.leaf 2926190890) (.leaf 2857749620)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2791338521) (.branch 32 (.leaf 2726879899) (.leaf 2664299725))) (.branch 35 (.branch 34 (.leaf 2603527433) (.leaf 2544495727)) (.branch 36 (.leaf 2487140401) (.leaf 2431400174)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2377216532) (.leaf 2324533582)) (.branch 40 (.leaf 2273297910) (.leaf 2223458456))) (.branch 43 (.branch 42 (.leaf 2174966391) (.leaf 2127775000)) (.branch 44 (.leaf 2081839576) (.leaf 2037117320))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1993567243) (.branch 47 (.leaf 1951150076) (.leaf 1909828187))) (.branch 50 (.branch 49 (.leaf 1869565500) (.leaf 1830327417)) (.branch 51 (.leaf 1792080749) (.leaf 1754793650)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1718435548) (.leaf 1682977089)) (.branch 55 (.leaf 1648390080) (.leaf 1614647430))) (.branch 58 (.branch 57 (.leaf 1581723106) (.leaf 1549592077)) (.branch 59 (.leaf 1518230273) (.leaf 1487614542))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1457722603) (.branch 62 (.leaf 1428533013) (.leaf 1400025126))) (.branch 65 (.branch 64 (.leaf 1372179060) (.leaf 1344975659)) (.branch 66 (.leaf 1318396469) (.leaf 1292423698)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1267040196) (.leaf 1242229423)) (.branch 70 (.leaf 1217975420) (.leaf 1194262793))) (.branch 73 (.branch 72 (.leaf 1171076681) (.leaf 1148402737)) (.branch 74 (.leaf 1126227107) (.leaf 1104536410))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1083317714) (.branch 77 (.leaf 1062558524) (.leaf 1042246761))) (.branch 80 (.branch 79 (.leaf 1022370745) (.leaf 1002919178)) (.branch 81 (.leaf 983881132) (.leaf 965246032)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 947003643) (.leaf 929144056)) (.branch 85 (.leaf 911657674) (.leaf 894535203))) (.branch 88 (.branch 87 (.leaf 877767639) (.leaf 861346255)) (.branch 89 (.leaf 845262594) (.leaf 829508457)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 814075891) (.branch 92 (.leaf 798957184) (.leaf 784144854))) (.branch 95 (.branch 94 (.leaf 769631639) (.leaf 755410494)) (.branch 96 (.leaf 741474576) (.leaf 727817242)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 714432041) (.leaf 701312706)) (.branch 100 (.leaf 688453146) (.leaf 675847445))) (.branch 103 (.branch 102 (.leaf 663489849) (.leaf 651374766)) (.branch 104 (.leaf 639496759) (.leaf 627850538))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 616430958) (.leaf 605233012)) (.branch 108 (.leaf 594251830) (.leaf 583482670))) (.branch 111 (.branch 110 (.leaf 572920915) (.leaf 562562071)) (.branch 112 (.leaf 552401760) (.leaf 542435719)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 532659794) (.leaf 523069939)) (.branch 116 (.leaf 513662209) (.leaf 504432760))) (.branch 119 (.branch 118 (.leaf 495377844) (.leaf 486493808)) (.branch 120 (.leaf 477777088) (.leaf 469224209)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 980).prefactor = (1175004534835341/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 980).cutoff/(generalMeanRows 980).c)).2 =
    (350282048251219/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 980).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 980).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 980).q*(generalMeanRows 980).c/2-2 = (1377/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable318.value]
    have hcontinuation : (generalMeanRows 980).q*(generalMeanRows 980).cutoff/2-2 = (425/234:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable319.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 980).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 980

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 980).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 980).criticalRate j.val*(generalMeanRows 980).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 980).c*(generalMeanRows 980).criticalPoint j.val)).2-
      (generalMeanRows 980).J/2-(generalMeanRows 980).error (generalMeanGrid j.val)+
      (generalMeanRows 980).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 980).c)).2-
      (generalMeanRows 980).J/2-(generalMeanRows 980).error 4 := by
  have he : (generalMeanRows 980).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 980) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 980)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0980

/-! Kernel-checked entropy margins for general spectral rectangle 981. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0981
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5670765865) (.branch 2 (.leaf 5483974959) (.leaf 5304931112))) (.branch 5 (.branch 4 (.leaf 5133222578) (.leaf 4968465812)) (.branch 6 (.leaf 4810302983) (.leaf 4658399767)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4512443379) (.leaf 4372140811)) (.branch 10 (.leaf 4237217247) (.leaf 4107414640))) (.branch 13 (.branch 12 (.leaf 3982490428) (.leaf 3862216373)) (.branch 14 (.leaf 3746377501) (.leaf 3634771151))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3527206096) (.branch 17 (.leaf 3423501753) (.leaf 3323487450))) (.branch 20 (.branch 19 (.leaf 3227001761) (.leaf 3133891897)) (.branch 21 (.leaf 3044013136) (.leaf 2957228314)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2873407339) (.leaf 2792426759)) (.branch 25 (.leaf 2714169344) (.leaf 2638523719))) (.branch 28 (.branch 27 (.leaf 2565384007) (.leaf 2494649504)) (.branch 29 (.leaf 2426224382) (.leaf 2360017404)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2295941664) (.branch 32 (.leaf 2233914341) (.leaf 2173856475))) (.branch 35 (.branch 34 (.leaf 2115692751) (.leaf 2059351301)) (.branch 36 (.leaf 2004763519) (.leaf 1951863887)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1900589808) (.leaf 1850881457)) (.branch 40 (.leaf 1802681635) (.leaf 1755935635))) (.branch 43 (.branch 42 (.leaf 1710591113) (.leaf 1666597970)) (.branch 44 (.leaf 1623908240) (.leaf 1582475980))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1542257177) (.branch 47 (.leaf 1503209647) (.leaf 1465292950))) (.branch 50 (.branch 49 (.leaf 1428468304) (.leaf 1392698509)) (.branch 51 (.leaf 1357947867) (.leaf 1324182115)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1291368355) (.leaf 1259474996)) (.branch 55 (.leaf 1228471686) (.leaf 1198329262))) (.branch 58 (.branch 57 (.leaf 1169019691) (.leaf 1140516024)) (.branch 59 (.leaf 1112792342) (.leaf 1085823714))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1059586150) (.branch 62 (.leaf 1034056564) (.leaf 1009212730))) (.branch 65 (.branch 64 (.leaf 985033248) (.leaf 961497505)) (.branch 66 (.leaf 938585644) (.leaf 916278531)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 894557725) (.leaf 873405445)) (.branch 70 (.leaf 852804548) (.leaf 832738499))) (.branch 73 (.branch 72 (.leaf 813191347) (.leaf 794147700)) (.branch 74 (.leaf 775592703) (.leaf 757512014))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 739891789) (.branch 77 (.leaf 722718654) (.leaf 705979693))) (.branch 80 (.branch 79 (.leaf 689662427) (.leaf 673754795)) (.branch 81 (.leaf 658245141) (.leaf 643122196)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 628375064) (.leaf 613993207)) (.branch 85 (.leaf 599966431) (.leaf 586284874))) (.branch 88 (.branch 87 (.leaf 572938992) (.leaf 559919549)) (.branch 89 (.leaf 547217601) (.leaf 534824493)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 522731839) (.branch 92 (.leaf 510931518) (.leaf 499415665))) (.branch 95 (.branch 94 (.leaf 488176657) (.leaf 477207107)) (.branch 96 (.leaf 466499856) (.leaf 456047963)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 445844699) (.leaf 435883538)) (.branch 100 (.leaf 426158151) (.leaf 416662399))) (.branch 103 (.branch 102 (.leaf 407390325) (.leaf 398336148)) (.branch 104 (.leaf 389494260) (.leaf 380859215))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 372425727) (.leaf 364188665)) (.branch 108 (.leaf 356143043) (.leaf 348284022))) (.branch 111 (.branch 110 (.leaf 340606900) (.leaf 333107109)) (.branch 112 (.leaf 325780209) (.leaf 318621890)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 311627957) (.leaf 304794338)) (.branch 116 (.leaf 298117070) (.leaf 291592302))) (.branch 119 (.branch 118 (.leaf 285216290) (.leaf 278985391)) (.branch 120 (.leaf 272896063) (.leaf 266944858)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 981).prefactor = (975774615203619/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 981).cutoff/(generalMeanRows 981).c)).2 =
    (29528537250377/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 981).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 981).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 981).q*(generalMeanRows 981).c/2-2 = (1681/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable302.value]
    have hcontinuation : (generalMeanRows 981).q*(generalMeanRows 981).cutoff/2-2 = (425/234:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable319.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 981).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 981

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 981).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 981).criticalRate j.val*(generalMeanRows 981).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 981).c*(generalMeanRows 981).criticalPoint j.val)).2-
      (generalMeanRows 981).J/2-(generalMeanRows 981).error (generalMeanGrid j.val)+
      (generalMeanRows 981).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 981).c)).2-
      (generalMeanRows 981).J/2-(generalMeanRows 981).error 4 := by
  have he : (generalMeanRows 981).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 981) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 981)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0981

/-! Kernel-checked entropy margins for general spectral rectangle 982. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0982
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5505220499) (.branch 2 (.leaf 5322988390) (.leaf 5148374206))) (.branch 5 (.branch 4 (.leaf 4980969873) (.leaf 4820395353)) (.branch 6 (.leaf 4666296184) (.leaf 4518341286)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4376221005) (.leaf 4239645363)) (.branch 10 (.leaf 4108342485) (.leaf 3982057179))) (.branch 13 (.branch 12 (.leaf 3860549664) (.leaf 3743594403)) (.branch 14 (.leaf 3630979062) (.leaf 3522503551))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3417979156) (.branch 17 (.leaf 3317227744) (.leaf 3220081038))) (.branch 20 (.branch 19 (.leaf 3126379952) (.leaf 3035973980)) (.branch 21 (.leaf 2948720637) (.leaf 2864484937)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2783138923) (.leaf 2704561223)) (.branch 25 (.leaf 2628636643) (.leaf 2555255794))) (.branch 28 (.branch 27 (.leaf 2484314737) (.leaf 2415714663)) (.branch 29 (.leaf 2349361592) (.leaf 2285166089)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2223043008) (.branch 32 (.leaf 2162911243) (.leaf 2104693506))) (.branch 35 (.branch 34 (.leaf 2048316112) (.leaf 1993708782)) (.branch 36 (.leaf 1940804459) (.leaf 1889539130)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1839851667) (.leaf 1791683675)) (.branch 40 (.leaf 1744979344) (.leaf 1699685320))) (.branch 43 (.branch 42 (.leaf 1655750576) (.leaf 1613126292)) (.branch 44 (.leaf 1571765747) (.leaf 1531624208))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1492658837) (.branch 47 (.leaf 1454828593) (.leaf 1418094145))) (.branch 50 (.branch 49 (.leaf 1382417790) (.leaf 1347763372)) (.branch 51 (.leaf 1314096210) (.leaf 1281383027)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1249591882) (.leaf 1218692112)) (.branch 55 (.leaf 1188654266) (.leaf 1159450054))) (.branch 58 (.branch 57 (.leaf 1131052291) (.leaf 1103434848)) (.branch 59 (.leaf 1076572602) (.leaf 1050441395))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1025017986) (.branch 62 (.leaf 1000280011) (.leaf 976205948))) (.branch 65 (.branch 64 (.leaf 952775077) (.leaf 929967443)) (.branch 66 (.leaf 907763828) (.leaf 886145716)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 865095264) (.leaf 844595271)) (.branch 70 (.leaf 824629155) (.leaf 805180924))) (.branch 73 (.branch 72 (.leaf 786235151) (.leaf 767776954)) (.branch 74 (.leaf 749791969) (.leaf 732266332))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 715186658) (.branch 77 (.leaf 698540020) (.leaf 682313934))) (.branch 80 (.branch 79 (.leaf 666496336) (.leaf 651075570)) (.branch 81 (.leaf 636040371) (.leaf 621379846)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 607083466) (.leaf 593141045)) (.branch 85 (.leaf 579542731) (.leaf 566278992))) (.branch 88 (.branch 87 (.leaf 553340604) (.leaf 540718639)) (.branch 89 (.leaf 528404454) (.leaf 516389680)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 504666212) (.branch 92 (.leaf 493226200) (.leaf 482062038))) (.branch 95 (.branch 94 (.leaf 471166357) (.leaf 460532013)) (.branch 96 (.leaf 450152084) (.leaf 440019858)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 430128826) (.leaf 420472675)) (.branch 100 (.leaf 411045284) (.leaf 401840712))) (.branch 103 (.branch 102 (.leaf 392853196) (.leaf 384077142)) (.branch 104 (.leaf 375507123) (.leaf 367137866))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 358964257) (.leaf 350981324)) (.branch 108 (.leaf 343184244) (.leaf 335568328))) (.branch 111 (.branch 110 (.leaf 328129023) (.leaf 320861903)) (.branch 112 (.leaf 313762670) (.leaf 306827143)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 300051261) (.leaf 293431076)) (.branch 116 (.leaf 286962747) (.leaf 280642541))) (.branch 119 (.branch 118 (.leaf 274466826) (.leaf 268432072)) (.branch 120 (.leaf 262534841) (.leaf 256771792)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 982).prefactor = (4834017356809923/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 982).cutoff/(generalMeanRows 982).c)).2 =
    (30687212145493/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 982).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 982).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 982).q*(generalMeanRows 982).c/2-2 = (17/20:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable055.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 982).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 982

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 982).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 982).criticalRate j.val*(generalMeanRows 982).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 982).c*(generalMeanRows 982).criticalPoint j.val)).2-
      (generalMeanRows 982).J/2-(generalMeanRows 982).error (generalMeanGrid j.val)+
      (generalMeanRows 982).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 982).c)).2-
      (generalMeanRows 982).J/2-(generalMeanRows 982).error 4 := by
  have he : (generalMeanRows 982).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 982) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 982)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0982

/-! Kernel-checked entropy margins for general spectral rectangle 983. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0983
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5423089362) (.branch 2 (.leaf 5245150584) (.leaf 5074673315))) (.branch 5 (.branch 4 (.leaf 4911254434) (.leaf 4754518660)) (.branch 6 (.leaf 4604116105) (.leaf 4459720100)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4321025257) (.leaf 4187745727)) (.branch 10 (.leaf 4059613633) (.leaf 3936377669))) (.branch 13 (.branch 12 (.leaf 3817801822) (.leaf 3703664224)) (.branch 14 (.leaf 3593756105) (.leaf 3487880846))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3385853107) (.branch 17 (.leaf 3287498046) (.leaf 3192650588))) (.branch 20 (.branch 19 (.leaf 3101154764) (.leaf 3012863106)) (.branch 21 (.leaf 2927636085) (.leaf 2845341598)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2765854491) (.leaf 2689056122)) (.branch 25 (.leaf 2614833956) (.leaf 2543081190))) (.branch 28 (.branch 27 (.leaf 2473696403) (.leaf 2406583235)) (.branch 29 (.leaf 2341650086) (.leaf 2278809840)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2217979599) (.branch 32 (.leaf 2159080448) (.leaf 2102037225))) (.branch 35 (.branch 34 (.leaf 2046778309) (.leaf 1993235430)) (.branch 36 (.leaf 1941343475) (.leaf 1891040323)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1842266682) (.leaf 1794965934)) (.branch 40 (.leaf 1749083997) (.leaf 1704569190))) (.branch 43 (.branch 42 (.leaf 1661372109) (.leaf 1619445507)) (.branch 44 (.leaf 1578744185) (.leaf 1539224888))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1500846205) (.branch 47 (.leaf 1463568479) (.leaf 1427353720))) (.branch 50 (.branch 49 (.leaf 1392165519) (.leaf 1357968975)) (.branch 51 (.leaf 1324730620) (.leaf 1292418349)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1261001356) (.leaf 1230450072)) (.branch 55 (.leaf 1200736107) (.leaf 1171832193))) (.branch 58 (.branch 57 (.leaf 1143712133) (.leaf 1116350753)) (.branch 59 (.leaf 1089723852) (.leaf 1063808160))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1038581294) (.branch 62 (.leaf 1014021720) (.leaf 990108713))) (.branch 65 (.branch 64 (.leaf 966822322) (.leaf 944143338)) (.branch 66 (.leaf 922053258) (.leaf 900534255)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 879569150) (.leaf 859141384)) (.branch 70 (.leaf 839234992) (.leaf 819834575))) (.branch 73 (.branch 72 (.leaf 800925279) (.leaf 782492772)) (.branch 74 (.leaf 764523219) (.leaf 747003266))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 729920018) (.branch 77 (.leaf 713261021) (.leaf 697014241))) (.branch 80 (.branch 79 (.leaf 681168053) (.leaf 665711217)) (.branch 81 (.leaf 650632871) (.leaf 635922510)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 621569974) (.leaf 607565433)) (.branch 85 (.leaf 593899379) (.leaf 580562607))) (.branch 88 (.branch 87 (.leaf 567546207) (.leaf 554841554)) (.branch 89 (.leaf 542440294) (.leaf 530334335)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 518515840) (.branch 92 (.leaf 506977212) (.leaf 495711090))) (.branch 95 (.branch 94 (.leaf 484710337) (.leaf 473968036)) (.branch 96 (.leaf 463477477) (.leaf 453232152)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 443225749) (.leaf 433452144)) (.branch 100 (.leaf 423905393) (.leaf 414579727))) (.branch 103 (.branch 102 (.leaf 405469545) (.leaf 396569411)) (.branch 104 (.leaf 387874044) (.leaf 379378316))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 371077246) (.leaf 362965994)) (.branch 108 (.leaf 355039857) (.leaf 347294265))) (.branch 111 (.branch 110 (.leaf 339724775) (.leaf 332327069)) (.branch 112 (.leaf 325096947) (.leaf 318030327)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 311123237) (.leaf 304371815)) (.branch 116 (.leaf 297772304) (.leaf 291321047))) (.branch 119 (.branch 118 (.leaf 285014487) (.leaf 278849162)) (.branch 120 (.leaf 272821701) (.leaf 266928826)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 983).prefactor = (1195538871920363/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 983).cutoff/(generalMeanRows 983).c)).2 =
    (326039612147207/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 983).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 983).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 983).q*(generalMeanRows 983).c/2-2 = (3359/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable311.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 983).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 983

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 983).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 983).criticalRate j.val*(generalMeanRows 983).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 983).c*(generalMeanRows 983).criticalPoint j.val)).2-
      (generalMeanRows 983).J/2-(generalMeanRows 983).error (generalMeanGrid j.val)+
      (generalMeanRows 983).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 983).c)).2-
      (generalMeanRows 983).J/2-(generalMeanRows 983).error 4 := by
  have he : (generalMeanRows 983).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 983) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 983)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0983

/-! Kernel-checked entropy margins for general spectral rectangle 984. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0984
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5262798019) (.branch 2 (.leaf 5089811696) (.leaf 4924127078))) (.branch 5 (.branch 4 (.leaf 4765346282) (.leaf 4613099029)) (.branch 6 (.leaf 4467040231) (.leaf 4326847831)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4192220883) (.leaf 4062877820)) (.branch 10 (.leaf 3938554904) (.leaf 3819004830))) (.branch 13 (.branch 12 (.leaf 3703995456) (.leaf 3593308668)) (.branch 14 (.leaf 3486739334) (.leaf 3384094359))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3285191832) (.branch 17 (.leaf 3189860229) (.leaf 3097937702))) (.branch 20 (.branch 19 (.leaf 3009271417) (.leaf 2923716946)) (.branch 21 (.leaf 2841137716) (.leaf 2761404492)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2684394907) (.leaf 2609993026)) (.branch 25 (.leaf 2538088941) (.leaf 2468578401))) (.branch 28 (.branch 27 (.leaf 2401362461) (.leaf 2336347165)) (.branch 29 (.leaf 2273443247) (.leaf 2212565853)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2153634282) (.branch 32 (.leaf 2096571749) (.leaf 2041305157))) (.branch 35 (.branch 34 (.leaf 1987764890) (.leaf 1935884616)) (.branch 36 (.leaf 1885601106) (.leaf 1836854061)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1789585956) (.leaf 1743741884)) (.branch 40 (.leaf 1699269420) (.leaf 1656118487))) (.branch 43 (.branch 42 (.leaf 1614241233) (.leaf 1573591915)) (.branch 44 (.leaf 1534126788) (.leaf 1495804003))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1458583513) (.branch 47 (.leaf 1422426976) (.leaf 1387297674))) (.branch 50 (.branch 49 (.leaf 1353160429) (.leaf 1319981531)) (.branch 51 (.leaf 1287728660) (.leaf 1256370823)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1225878288) (.leaf 1196222522)) (.branch 55 (.leaf 1167376137) (.leaf 1139312832))) (.branch 58 (.branch 57 (.leaf 1112007346) (.leaf 1085435405)) (.branch 59 (.leaf 1059573680) (.leaf 1034399740))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1009892014) (.branch 62 (.leaf 986029751) (.leaf 962792981))) (.branch 65 (.branch 64 (.leaf 940162483) (.leaf 918119750)) (.branch 66 (.leaf 896646956) (.leaf 875726930)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 855343124) (.leaf 835479586)) (.branch 70 (.leaf 816120939) (.leaf 797252348))) (.branch 73 (.branch 72 (.leaf 778859506) (.leaf 760928605)) (.branch 74 (.leaf 743446319) (.leaf 726399781))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 709776568) (.branch 77 (.leaf 693564679) (.leaf 677752517))) (.branch 80 (.branch 79 (.leaf 662328879) (.leaf 647282933)) (.branch 81 (.leaf 632604207) (.leaf 618282572)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 604308233) (.leaf 590671710)) (.branch 85 (.leaf 577363832) (.leaf 564375720))) (.branch 88 (.branch 87 (.leaf 551698778) (.leaf 539324681)) (.branch 89 (.leaf 527245366) (.leaf 515453023)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 503940084) (.branch 92 (.leaf 492699211) (.leaf 481723295))) (.branch 95 (.branch 94 (.leaf 471005442) (.leaf 460538964)) (.branch 96 (.leaf 450317378) (.leaf 440334391)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 430583901) (.leaf 421059982)) (.branch 100 (.leaf 411756885) (.leaf 402669026))) (.branch 103 (.branch 102 (.leaf 393790986) (.leaf 385117501)) (.branch 104 (.leaf 376643456) (.leaf 368363885))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 360273962) (.leaf 352368996)) (.branch 108 (.leaf 344644428) (.leaf 337095827))) (.branch 111 (.branch 110 (.leaf 329718885) (.leaf 322509413)) (.branch 112 (.leaf 315463336) (.leaf 308576691)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 301845624) (.leaf 295266383)) (.branch 116 (.leaf 288835320) (.leaf 282548883))) (.branch 119 (.branch 118 (.leaf 276403614) (.leaf 270396150)) (.branch 120 (.leaf 264523213) (.leaf 258781615)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 984).prefactor = (236206984854869/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 984).cutoff/(generalMeanRows 984).c)).2 =
    (339737135074603/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 984).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 984).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 984).q*(generalMeanRows 984).c/2-2 = (847/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable287.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 984).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 984

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 984).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 984).criticalRate j.val*(generalMeanRows 984).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 984).c*(generalMeanRows 984).criticalPoint j.val)).2-
      (generalMeanRows 984).J/2-(generalMeanRows 984).error (generalMeanGrid j.val)+
      (generalMeanRows 984).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 984).c)).2-
      (generalMeanRows 984).J/2-(generalMeanRows 984).error 4 := by
  have he : (generalMeanRows 984).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 984) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 984)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0984

/-! Kernel-checked entropy margins for general spectral rectangle 985. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0985
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5345985204) (.branch 2 (.leaf 5176860142) (.leaf 5014826566))) (.branch 5 (.branch 4 (.leaf 4859493895) (.leaf 4710498902)) (.branch 6 (.leaf 4567503306) (.leaf 4430191643)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4298269347) (.leaf 4171461039)) (.branch 10 (.leaf 4049508985) (.leaf 3932171703))) (.branch 13 (.branch 12 (.leaf 3819222713) (.leaf 3710449393)) (.branch 14 (.leaf 3605651950) (.leaf 3504642478))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3407244106) (.branch 17 (.leaf 3313290208) (.leaf 3222623697))) (.branch 20 (.branch 19 (.leaf 3135096362) (.leaf 3050568270)) (.branch 21 (.leaf 2968907209) (.leaf 2889988183)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2813692942) (.leaf 2739909543)) (.branch 25 (.leaf 2668531957) (.leaf 2599459693))) (.branch 28 (.branch 27 (.leaf 2532597456) (.leaf 2467854830)) (.branch 29 (.leaf 2405145978) (.leaf 2344389374)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2285507539) (.branch 32 (.leaf 2228426809) (.leaf 2173077111))) (.branch 35 (.branch 34 (.leaf 2119391757) (.leaf 2067307248)) (.branch 36 (.leaf 2016763097) (.leaf 1967701658)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1920067968) (.leaf 1873809601)) (.branch 40 (.leaf 1828876529) (.leaf 1785220990))) (.branch 43 (.branch 42 (.leaf 1742797370) (.leaf 1701562084)) (.branch 44 (.leaf 1661473474) (.leaf 1622491702))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1584578662) (.branch 47 (.leaf 1547697885) (.leaf 1511814458))) (.branch 50 (.branch 49 (.leaf 1476894945) (.leaf 1442907312)) (.branch 51 (.leaf 1409820854) (.leaf 1377606135)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1346234920) (.leaf 1315680119)) (.branch 55 (.leaf 1285915730) (.leaf 1256916787))) (.branch 58 (.branch 57 (.leaf 1228659311) (.leaf 1201120262)) (.branch 59 (.leaf 1174277494) (.leaf 1148109716))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1122596449) (.branch 62 (.leaf 1097717991) (.leaf 1073455379))) (.branch 65 (.branch 64 (.leaf 1049790357) (.leaf 1026705343)) (.branch 66 (.leaf 1004183400) (.leaf 982208205)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 960764025) (.leaf 939835687)) (.branch 70 (.leaf 919408559) (.leaf 899468521))) (.branch 73 (.branch 72 (.leaf 880001946) (.leaf 860995679)) (.branch 74 (.leaf 842437014) (.leaf 824313679))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 806613818) (.branch 77 (.leaf 789325969) (.leaf 772439051))) (.branch 80 (.branch 79 (.leaf 755942351) (.leaf 739825503)) (.branch 81 (.leaf 724078479) (.leaf 708691574)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 693655391) (.leaf 678960832)) (.branch 85 (.leaf 664599086) (.leaf 650561616))) (.branch 88 (.branch 87 (.leaf 636840148) (.leaf 623426665)) (.branch 89 (.leaf 610313394) (.leaf 597492795)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 584957558) (.branch 92 (.leaf 572700588) (.leaf 560715004))) (.branch 95 (.branch 94 (.leaf 548994123) (.leaf 537531460)) (.branch 96 (.leaf 526320718) (.leaf 515355782)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 504630709) (.leaf 494139727)) (.branch 100 (.leaf 483877229) (.leaf 473837760))) (.branch 103 (.branch 102 (.leaf 464016022) (.leaf 454406860)) (.branch 104 (.leaf 445005263) (.leaf 435806357))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 426805399) (.leaf 417997775)) (.branch 108 (.leaf 409378994) (.leaf 400944685))) (.branch 111 (.branch 110 (.leaf 392690595) (.leaf 384612579)) (.branch 112 (.leaf 376706603) (.leaf 368968740)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 361395162) (.leaf 353982139)) (.branch 116 (.leaf 346726040) (.leaf 339623325))) (.branch 119 (.branch 118 (.leaf 332670542) (.leaf 325864329)) (.branch 120 (.leaf 319201407) (.leaf 312678578)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 985).prefactor = (2330378611657859/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 985).cutoff/(generalMeanRows 985).c)).2 =
    (373719069371603/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 985).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 985).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 985).q*(generalMeanRows 985).c/2-2 = (799/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable320.value]
    have hcontinuation : (generalMeanRows 985).q*(generalMeanRows 985).cutoff/2-2 = (215/104:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable321.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 985).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 985

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 985).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 985).criticalRate j.val*(generalMeanRows 985).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 985).c*(generalMeanRows 985).criticalPoint j.val)).2-
      (generalMeanRows 985).J/2-(generalMeanRows 985).error (generalMeanGrid j.val)+
      (generalMeanRows 985).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 985).c)).2-
      (generalMeanRows 985).J/2-(generalMeanRows 985).error 4 := by
  have he : (generalMeanRows 985).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 985) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 985)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0985

/-! Kernel-checked entropy margins for general spectral rectangle 986. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0986
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5427880230) (.branch 2 (.leaf 5253918277) (.leaf 5087280195))) (.branch 5 (.branch 4 (.leaf 4927562891) (.leaf 4774391465)) (.branch 6 (.leaf 4627416738) (.leaf 4486313051)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4350776290) (.leaf 4220522125)) (.branch 10 (.leaf 4095284418) (.leaf 3974813790))) (.branch 13 (.branch 12 (.leaf 3858876331) (.leaf 3747252424)) (.branch 14 (.leaf 3639735683) (.leaf 3536131981))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3436258574) (.branch 17 (.leaf 3339943289) (.leaf 3247023788))) (.branch 20 (.branch 19 (.leaf 3157346895) (.leaf 3070767973)) (.branch 21 (.leaf 2987150354) (.leaf 2906364816)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2828289096) (.leaf 2752807447)) (.branch 25 (.leaf 2679810220) (.leaf 2609193488))) (.branch 28 (.branch 27 (.leaf 2540858687) (.leaf 2474712289)) (.branch 29 (.leaf 2410665498) (.leaf 2348633965)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2288537527) (.branch 32 (.leaf 2230299957) (.leaf 2173848741))) (.branch 35 (.branch 34 (.leaf 2119114859) (.leaf 2066032589)) (.branch 36 (.leaf 2014539320) (.leaf 1964575380)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1916083867) (.leaf 1869010504)) (.branch 40 (.leaf 1823303492) (.leaf 1778913375))) (.branch 43 (.branch 42 (.leaf 1735792919) (.leaf 1693896990)) (.branch 44 (.leaf 1653182445) (.leaf 1613608025))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1575134263) (.branch 47 (.leaf 1537723385) (.leaf 1501339231))) (.branch 50 (.branch 49 (.leaf 1465947165) (.leaf 1431514005)) (.branch 51 (.leaf 1398007946) (.leaf 1365398494)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1333656401) (.leaf 1302753605)) (.branch 55 (.leaf 1272663171) (.leaf 1243359236))) (.branch 58 (.branch 57 (.leaf 1214816961) (.leaf 1187012480)) (.branch 59 (.leaf 1159922853) (.leaf 1133526028))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1107800792) (.branch 62 (.leaf 1082726740) (.leaf 1058284232))) (.branch 65 (.branch 64 (.leaf 1034454362) (.leaf 1011218922)) (.branch 66 (.leaf 988560376) (.leaf 966461821)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 944906970) (.leaf 923880114)) (.branch 70 (.leaf 903366107) (.leaf 883350335))) (.branch 73 (.branch 72 (.leaf 863818694) (.leaf 844757570)) (.branch 74 (.leaf 826153819) (.leaf 807994744))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 790268079) (.branch 77 (.leaf 772961971) (.leaf 756064962))) (.branch 80 (.branch 79 (.leaf 739565971) (.leaf 723454286)) (.branch 81 (.leaf 707719538) (.leaf 692351699)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 677341059) (.leaf 662678221)) (.branch 85 (.leaf 648354081) (.leaf 634359824))) (.branch 88 (.branch 87 (.leaf 620686909) (.leaf 607327059)) (.branch 89 (.leaf 594272252) (.leaf 581514708)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 569046887) (.branch 92 (.leaf 556861471) (.leaf 544951365))) (.branch 95 (.branch 94 (.leaf 533309680) (.leaf 521929735)) (.branch 96 (.leaf 510805039) (.leaf 499929294)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 489296381) (.leaf 478900359)) (.branch 100 (.leaf 468735453) (.leaf 458796055))) (.branch 103 (.branch 102 (.leaf 449076712) (.leaf 439572126)) (.branch 104 (.leaf 430277144) (.leaf 421186757))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 412296091) (.leaf 403600409)) (.branch 108 (.leaf 395095099) (.leaf 386775676))) (.branch 111 (.branch 110 (.leaf 378637773) (.leaf 370677141)) (.branch 112 (.leaf 362889643) (.leaf 355271252)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 347818047) (.leaf 340526207)) (.branch 116 (.leaf 333392013) (.leaf 326411841))) (.branch 119 (.branch 118 (.leaf 319582160) (.leaf 312899530)) (.branch 120 (.leaf 306360598) (.leaf 299962096)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 986).prefactor = (4804797862881839/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 986).cutoff/(generalMeanRows 986).c)).2 =
    (91827197752671/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 986).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 986).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 986).q*(generalMeanRows 986).cutoff/2-2 = (215/104:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable321.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 986).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 986

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 986).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 986).criticalRate j.val*(generalMeanRows 986).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 986).c*(generalMeanRows 986).criticalPoint j.val)).2-
      (generalMeanRows 986).J/2-(generalMeanRows 986).error (generalMeanGrid j.val)+
      (generalMeanRows 986).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 986).c)).2-
      (generalMeanRows 986).J/2-(generalMeanRows 986).error 4 := by
  have he : (generalMeanRows 986).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 986) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 986)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0986

/-! Kernel-checked entropy margins for general spectral rectangle 987. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0987
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5428632683) (.branch 2 (.leaf 5250182939) (.leaf 5079309159))) (.branch 5 (.branch 4 (.leaf 4915594820) (.leaf 4758652467)) (.branch 6 (.leaf 4608121164) (.leaf 4463664223)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4324967180) (.leaf 4191735973)) (.branch 10 (.leaf 4063695304) (.leaf 3940587165))) (.branch 13 (.branch 12 (.leaf 3822169509) (.leaf 3708215034)) (.branch 14 (.leaf 3598510095) (.leaf 3492853701))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3391056610) (.branch 17 (.leaf 3292940494) (.leaf 3198337183))) (.branch 20 (.branch 19 (.leaf 3107087966) (.leaf 3019042954)) (.branch 21 (.leaf 2934060491) (.leaf 2852006616)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2772754557) (.leaf 2696184278)) (.branch 25 (.leaf 2622182051) (.leaf 2550640060))) (.branch 28 (.branch 27 (.leaf 2481456038) (.leaf 2414532927)) (.branch 29 (.leaf 2349778565) (.leaf 2287105391)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2226430179) (.branch 32 (.leaf 2167673777) (.leaf 2110760875))) (.branch 35 (.branch 34 (.leaf 2055619787) (.leaf 2002182240)) (.branch 36 (.leaf 1950383185) (.leaf 1900160619)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1851455413) (.leaf 1804211157)) (.branch 40 (.leaf 1758374012) (.leaf 1713892570))) (.branch 43 (.branch 42 (.leaf 1670717728) (.leaf 1628802562)) (.branch 44 (.leaf 1588102217) (.leaf 1548573793))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1510176250) (.branch 47 (.leaf 1472870311) (.leaf 1436618370))) (.branch 50 (.branch 49 (.leaf 1401384411) (.leaf 1367133924)) (.branch 51 (.leaf 1333833837) (.leaf 1301452437)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1269959311) (.leaf 1239325275)) (.branch 55 (.leaf 1209522323) (.leaf 1180523563))) (.branch 58 (.branch 57 (.leaf 1152303171) (.leaf 1124836334)) (.branch 59 (.leaf 1098099206) (.leaf 1072068864))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1046723263) (.branch 62 (.leaf 1022041198) (.leaf 998002261))) (.branch 65 (.branch 64 (.leaf 974586812) (.leaf 951775939)) (.branch 66 (.leaf 929551428) (.leaf 907895730)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 886791935) (.leaf 866223741)) (.branch 70 (.leaf 846175429) (.leaf 826631838))) (.branch 73 (.branch 72 (.leaf 807578342) (.leaf 789000824)) (.branch 74 (.leaf 770885658) (.leaf 753219687))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 735990203) (.branch 77 (.leaf 719184931) (.leaf 702792007))) (.branch 80 (.branch 79 (.leaf 686799966) (.leaf 671197721)) (.branch 81 (.leaf 655974552) (.leaf 641120089)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 626624301) (.leaf 612477477)) (.branch 85 (.leaf 598670220) (.leaf 585193430))) (.branch 88 (.branch 87 (.leaf 572038296) (.leaf 559196283)) (.branch 89 (.leaf 546659122) (.leaf 534418800)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 522467550) (.branch 92 (.leaf 510797843) (.leaf 499402378))) (.branch 95 (.branch 94 (.leaf 488274075) (.leaf 477406065)) (.branch 96 (.leaf 466791685) (.leaf 456424468)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 446298138) (.leaf 436406603)) (.branch 100 (.leaf 426743945) (.leaf 417304421))) (.branch 103 (.branch 102 (.leaf 408082451) (.leaf 399072614)) (.branch 104 (.leaf 390269644) (.leaf 381668423))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 373263976) (.leaf 365051469)) (.branch 108 (.leaf 357026199) (.leaf 349183597))) (.branch 111 (.branch 110 (.leaf 341519217) (.leaf 334028734)) (.branch 112 (.leaf 326707942) (.leaf 319552749)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 312559172) (.leaf 305723335)) (.branch 116 (.leaf 299041467) (.leaf 292509894))) (.branch 119 (.branch 118 (.leaf 286125043) (.leaf 279883432)) (.branch 120 (.leaf 273781671) (.leaf 267816458)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 987).prefactor = (4953290076484661/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 987).cutoff/(generalMeanRows 987).c)).2 =
    (354610207673557/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 987).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 987).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 987).q*(generalMeanRows 987).c/2-2 = (853/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable322.value]
    have hcontinuation : (generalMeanRows 987).q*(generalMeanRows 987).cutoff/2-2 = (215/104:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable321.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 987).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 987

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 987).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 987).criticalRate j.val*(generalMeanRows 987).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 987).c*(generalMeanRows 987).criticalPoint j.val)).2-
      (generalMeanRows 987).J/2-(generalMeanRows 987).error (generalMeanGrid j.val)+
      (generalMeanRows 987).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 987).c)).2-
      (generalMeanRows 987).J/2-(generalMeanRows 987).error 4 := by
  have he : (generalMeanRows 987).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 987) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 987)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0987

/-! Kernel-checked entropy margins for general spectral rectangle 988. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0988
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5512733157) (.branch 2 (.leaf 5329267560) (.leaf 5153624519))) (.branch 5 (.branch 4 (.leaf 4985374112) (.leaf 4824116385)) (.branch 6 (.leaf 4669478726) (.leaf 4521113529)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4378696100) (.leaf 4241922785)) (.branch 10 (.leaf 4110509285) (.leaf 3984189131))) (.branch 13 (.branch 12 (.leaf 3862712314) (.leaf 3745844041)) (.branch 14 (.leaf 3633363602) (.leaf 3525063343))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3420747730) (.branch 17 (.leaf 3320232493) (.leaf 3223343842))) (.branch 20 (.branch 19 (.leaf 3129917750) (.leaf 3039799293)) (.branch 21 (.leaf 2952842045) (.leaf 2868907522)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2787864664) (.leaf 2709589364)) (.branch 25 (.leaf 2633964027) (.leaf 2560877162))) (.branch 28 (.branch 27 (.leaf 2490223012) (.leaf 2421901197)) (.branch 29 (.leaf 2355816394) (.leaf 2291878035)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2230000028) (.branch 32 (.leaf 2170100491) (.leaf 2112101515))) (.branch 35 (.branch 34 (.leaf 2055928930) (.leaf 2001512100)) (.branch 36 (.leaf 1948783718) (.leaf 1897679625)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1848138635) (.leaf 1800102374)) (.branch 40 (.leaf 1753515125) (.leaf 1708323688))) (.branch 43 (.branch 42 (.leaf 1664477243) (.leaf 1621927228)) (.branch 44 (.leaf 1580627217) (.leaf 1540532813))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1501601539) (.branch 47 (.leaf 1463792744) (.leaf 1427067506))) (.branch 50 (.branch 49 (.leaf 1391388549) (.leaf 1356720159)) (.branch 51 (.leaf 1323028105) (.leaf 1290279569)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1258443076) (.leaf 1227488425)) (.branch 55 (.leaf 1197386635) (.leaf 1168109881))) (.branch 58 (.branch 57 (.leaf 1139631439) (.leaf 1111925638)) (.branch 59 (.leaf 1084967808) (.leaf 1058734234))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1033202112) (.branch 62 (.leaf 1008349508) (.leaf 984155317))) (.branch 65 (.branch 64 (.leaf 960599226) (.leaf 937661679)) (.branch 66 (.leaf 915323844) (.leaf 893567578)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 872375402) (.leaf 851730465)) (.branch 70 (.leaf 831616525) (.leaf 812017914))) (.branch 73 (.branch 72 (.leaf 792919520) (.leaf 774306763)) (.branch 74 (.leaf 756165569) (.leaf 738482351))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 721243988) (.branch 77 (.leaf 704437808) (.leaf 688051567))) (.branch 80 (.branch 79 (.leaf 672073433) (.leaf 656491969)) (.branch 81 (.leaf 641296116) (.leaf 626475181)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 612018818) (.leaf 597917020)) (.branch 85 (.leaf 584160100) (.leaf 570738684))) (.branch 88 (.branch 87 (.leaf 557643693) (.leaf 544866338)) (.branch 89 (.leaf 532398105) (.leaf 520230745)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 508356266) (.branch 92 (.leaf 496766922) (.leaf 485455203))) (.branch 95 (.branch 94 (.leaf 474413829) (.leaf 463635739)) (.branch 96 (.leaf 453114085) (.leaf 442842224)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 432813709) (.leaf 423022284)) (.branch 100 (.leaf 413461877) (.leaf 404126593))) (.branch 103 (.branch 102 (.leaf 395010708) (.leaf 386108664)) (.branch 104 (.leaf 377415060) (.leaf 368924653))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 360632346) (.leaf 352533187)) (.branch 108 (.leaf 344622363) (.leaf 336895195))) (.branch 111 (.branch 110 (.leaf 329347136) (.leaf 321973763)) (.branch 112 (.leaf 314770775) (.leaf 307733989)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 300859338) (.leaf 294142862)) (.branch 116 (.leaf 287580711) (.leaf 281169137))) (.branch 119 (.branch 118 (.leaf 274904492) (.leaf 268783228)) (.branch 120 (.leaf 262801887) (.leaf 256957107)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 988).prefactor = (2553185719980073/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 988).cutoff/(generalMeanRows 988).c)).2 =
    (174160439382997/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 988).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 988).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 988).q*(generalMeanRows 988).cutoff/2-2 = (215/104:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable321.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 988).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 988

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 988).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 988).criticalRate j.val*(generalMeanRows 988).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 988).c*(generalMeanRows 988).criticalPoint j.val)).2-
      (generalMeanRows 988).J/2-(generalMeanRows 988).error (generalMeanGrid j.val)+
      (generalMeanRows 988).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 988).c)).2-
      (generalMeanRows 988).J/2-(generalMeanRows 988).error 4 := by
  have he : (generalMeanRows 988).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 988) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 988)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0988

/-! Kernel-checked entropy margins for general spectral rectangle 989. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0989
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5769361309) (.branch 2 (.leaf 5579711152) (.leaf 5398112463))) (.branch 5 (.branch 4 (.leaf 5224122579) (.leaf 5057329724)) (.branch 6 (.leaf 4897350310) (.leaf 4743826516)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4596424141) (.leaf 4454830665)) (.branch 10 (.leaf 4318753511) (.leaf 4187918479))) (.branch 13 (.branch 12 (.leaf 4062068327) (.leaf 3940961489)) (.branch 14 (.leaf 3824370910) (.leaf 3712082983))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3603896588) (.branch 17 (.leaf 3499622205) (.leaf 3399081108))) (.branch 20 (.branch 19 (.leaf 3302104626) (.leaf 3208533461)) (.branch 21 (.leaf 3118217066) (.leaf 3031013071)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2946786750) (.leaf 2865410531)) (.branch 25 (.leaf 2786763547) (.leaf 2710731217))) (.branch 28 (.branch 27 (.leaf 2637204853) (.leaf 2566081307)) (.branch 29 (.leaf 2497262631) (.leaf 2430655770)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2366172273) (.branch 32 (.leaf 2303728019) (.leaf 2243242974))) (.branch 35 (.branch 34 (.leaf 2184640951) (.leaf 2127849391)) (.branch 36 (.leaf 2072799164) (.leaf 2019424374)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1967662182) (.leaf 1917452636)) (.branch 40 (.leaf 1868738517) (.leaf 1821465194))) (.branch 43 (.branch 42 (.leaf 1775580479) (.leaf 1731034504)) (.branch 44 (.leaf 1687779597) (.leaf 1645770168))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1604962601) (.branch 47 (.leaf 1565315151) (.leaf 1526787853))) (.branch 50 (.branch 49 (.leaf 1489342431) (.leaf 1452942210)) (.branch 51 (.leaf 1417552040) (.leaf 1383138219)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1349668423) (.leaf 1317111639)) (.branch 55 (.leaf 1285438102) (.leaf 1254619233))) (.branch 58 (.branch 57 (.leaf 1224627585) (.leaf 1195436789)) (.branch 59 (.leaf 1167021503) (.leaf 1139357364))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1112420945) (.branch 62 (.leaf 1086189707) (.leaf 1060641964))) (.branch 65 (.branch 64 (.leaf 1035756843) (.leaf 1011514243)) (.branch 66 (.leaf 987894808) (.leaf 964879888)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 942451512) (.leaf 920592353)) (.branch 70 (.leaf 899285707) (.leaf 878515461))) (.branch 73 (.branch 72 (.leaf 858266070) (.leaf 838522533)) (.branch 74 (.leaf 819270366) (.leaf 800495589))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 782184696) (.branch 77 (.leaf 764324639) (.leaf 746902812))) (.branch 80 (.branch 79 (.leaf 729907028) (.leaf 713325507)) (.branch 81 (.leaf 697146855) (.leaf 681360050)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 665954432) (.leaf 650919682)) (.branch 85 (.leaf 636245811) (.leaf 621923149))) (.branch 88 (.branch 87 (.leaf 607942332) (.leaf 594294289)) (.branch 89 (.leaf 580970232) (.leaf 567961645)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 555260274) (.branch 92 (.leaf 542858116) (.leaf 530747414))) (.branch 95 (.branch 94 (.leaf 518920642) (.leaf 507370501)) (.branch 96 (.leaf 496089908) (.leaf 485071992)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 474310082) (.leaf 463797703)) (.branch 100 (.leaf 453528568) (.leaf 443496571))) (.branch 103 (.branch 102 (.leaf 433695783) (.leaf 424120443)) (.branch 104 (.leaf 414764954) (.leaf 405623876))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 396691924) (.leaf 387963957)) (.branch 108 (.leaf 379434982) (.leaf 371100138))) (.branch 111 (.branch 110 (.leaf 362954702) (.leaf 354994078)) (.branch 112 (.leaf 347213796) (.leaf 339609506)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 332176977) (.leaf 324912088)) (.branch 116 (.leaf 317810832) (.leaf 310869305))) (.branch 119 (.branch 118 (.leaf 304083708) (.leaf 297450341)) (.branch 120 (.leaf 290965602) (.leaf 284625983)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 989).prefactor = (2632091890461833/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 989).cutoff/(generalMeanRows 989).c)).2 =
    (354610207673557/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 989).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 989).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 989).q*(generalMeanRows 989).c/2-2 = (853/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable322.value]
    have hcontinuation : (generalMeanRows 989).q*(generalMeanRows 989).cutoff/2-2 = (215/104:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable321.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 989).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 989

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 989).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 989).criticalRate j.val*(generalMeanRows 989).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 989).c*(generalMeanRows 989).criticalPoint j.val)).2-
      (generalMeanRows 989).J/2-(generalMeanRows 989).error (generalMeanGrid j.val)+
      (generalMeanRows 989).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 989).c)).2-
      (generalMeanRows 989).J/2-(generalMeanRows 989).error 4 := by
  have he : (generalMeanRows 989).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 989) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 989)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0989

/-! Kernel-checked entropy margins for general spectral rectangle 990. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0990
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5947663343) (.branch 2 (.leaf 5752152050) (.leaf 5564941056))) (.branch 5 (.branch 4 (.leaf 5385574017) (.leaf 5213626432)) (.branch 6 (.leaf 5048702855) (.leaf 4890434411)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4738476567) (.leaf 4592507147)) (.branch 10 (.leaf 4452224530) (.leaf 4317346043))) (.branch 13 (.branch 12 (.leaf 4187606494) (.leaf 4062756851)) (.branch 14 (.leaf 3942563041) (.leaf 3826804858))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3715274964) (.branch 17 (.leaf 3607777983) (.leaf 3504129665))) (.branch 20 (.branch 19 (.leaf 3404156125) (.leaf 3307693144)) (.branch 21 (.leaf 3214585523) (.leaf 3124686490)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3037857155) (.leaf 2953966005)) (.branch 25 (.leaf 2872888438) (.leaf 2794506329))) (.branch 28 (.branch 27 (.leaf 2718707634) (.leaf 2645386015)) (.branch 29 (.leaf 2574440499) (.leaf 2505775154)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2439298795) (.branch 32 (.leaf 2374924703) (.leaf 2312570368))) (.branch 35 (.branch 34 (.leaf 2252157250) (.leaf 2193610548)) (.branch 36 (.leaf 2136858995) (.leaf 2081834658)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2028472755) (.leaf 1976711484)) (.branch 40 (.leaf 1926491856) (.leaf 1877757551))) (.branch 43 (.branch 42 (.leaf 1830454770) (.leaf 1784532102)) (.branch 44 (.leaf 1739940403) (.leaf 1696632673))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1654563948) (.branch 47 (.leaf 1613691194) (.leaf 1573973212))) (.branch 50 (.branch 49 (.leaf 1535370539) (.leaf 1497845369)) (.branch 51 (.leaf 1461361466) (.leaf 1425884087)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1391379907) (.leaf 1357816957)) (.branch 55 (.leaf 1325164549) (.leaf 1293393223))) (.branch 58 (.branch 57 (.leaf 1262474684) (.leaf 1232381747)) (.branch 59 (.leaf 1203088287) (.leaf 1174569188))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1146800299) (.branch 62 (.leaf 1119758385) (.leaf 1093421090))) (.branch 65 (.branch 64 (.leaf 1067766894) (.leaf 1042775077)) (.branch 66 (.leaf 1018425684) (.leaf 994699488)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 971577963) (.leaf 949043247)) (.branch 70 (.leaf 927078120) (.leaf 905665970))) (.branch 73 (.branch 72 (.leaf 884790772) (.leaf 864437060)) (.branch 74 (.leaf 844589906) (.leaf 825234895))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 806358103) (.branch 77 (.leaf 787946082) (.leaf 769985833))) (.branch 80 (.branch 79 (.leaf 752464795) (.leaf 735370822)) (.branch 81 (.leaf 718692169) (.leaf 702417474)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 686535745) (.leaf 671036346)) (.branch 85 (.leaf 655908979) (.leaf 641143676))) (.branch 88 (.branch 87 (.leaf 626730782) (.leaf 612660946)) (.branch 89 (.leaf 598925109) (.leaf 585514492)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 572420585) (.branch 92 (.leaf 559635139) (.leaf 547150156))) (.branch 95 (.branch 94 (.leaf 534957877) (.leaf 523050779)) (.branch 96 (.leaf 511421560) (.leaf 500063135)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 488968629) (.leaf 478131365)) (.branch 100 (.leaf 467544862) (.leaf 457202827))) (.branch 103 (.branch 102 (.leaf 447099146) (.leaf 437227880)) (.branch 104 (.leaf 427583259) (.leaf 418159677))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 408951682) (.leaf 399953978)) (.branch 108 (.leaf 391161415) (.leaf 382568983))) (.branch 111 (.branch 110 (.leaf 374171812) (.leaf 365965165)) (.branch 112 (.leaf 357944434) (.leaf 350105133)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 342442902) (.leaf 334953492)) (.branch 116 (.leaf 327632771) (.leaf 320476716))) (.branch 119 (.branch 118 (.leaf 313481411) (.leaf 306643040)) (.branch 120 (.leaf 299957891) (.leaf 293422345)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 990).prefactor = (1085374662034223/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 990).cutoff/(generalMeanRows 990).c)).2 =
    (354610207673557/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 990).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 990).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 990).q*(generalMeanRows 990).c/2-2 = (853/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable322.value]
    have hcontinuation : (generalMeanRows 990).q*(generalMeanRows 990).cutoff/2-2 = (215/104:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable321.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 990).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 990

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 990).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 990).criticalRate j.val*(generalMeanRows 990).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 990).c*(generalMeanRows 990).criticalPoint j.val)).2-
      (generalMeanRows 990).J/2-(generalMeanRows 990).error (generalMeanGrid j.val)+
      (generalMeanRows 990).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 990).c)).2-
      (generalMeanRows 990).J/2-(generalMeanRows 990).error 4 := by
  have he : (generalMeanRows 990).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 990) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 990)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0990

/-! Kernel-checked entropy margins for general spectral rectangle 991. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0991
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7464472592) (.branch 2 (.leaf 7248735420) (.leaf 7041236966))) (.branch 5 (.branch 4 (.leaf 6841556867) (.leaf 6649303505)) (.branch 6 (.leaf 6464111417) (.leaf 6285638991)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6113566426) (.leaf 5947593907)) (.branch 10 (.leaf 5787439975) (.leaf 5632840070))) (.branch 13 (.branch 12 (.leaf 5483545209) (.leaf 5339320810)) (.branch 14 (.leaf 5199945611) (.leaf 5065210706))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4934918660) (.branch 17 (.leaf 4808882707) (.leaf 4686926017))) (.branch 20 (.branch 19 (.leaf 4568881030) (.leaf 4454588839)) (.branch 21 (.leaf 4343898630) (.leaf 4236667167)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4132758313) (.leaf 4032042597)) (.branch 25 (.leaf 3934396804) (.leaf 3839703602))) (.branch 28 (.branch 27 (.leaf 3747851198) (.leaf 3658733014)) (.branch 29 (.leaf 3572247389) (.leaf 3488297302)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3406790114) (.branch 32 (.leaf 3327637325) (.leaf 3250754353))) (.branch 35 (.branch 34 (.leaf 3176060320) (.leaf 3103477862)) (.branch 36 (.leaf 3032932936) (.leaf 2964354658)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2897675136) (.leaf 2832829320)) (.branch 40 (.leaf 2769754858) (.leaf 2708391966))) (.branch 43 (.branch 42 (.leaf 2648683300) (.leaf 2590573837)) (.branch 44 (.leaf 2534010767) (.leaf 2478943381))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2425322979) (.branch 47 (.leaf 2373102772) (.leaf 2322237794))) (.branch 50 (.branch 49 (.leaf 2272684821) (.leaf 2224402285)) (.branch 51 (.leaf 2177350209) (.leaf 2131490126)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2086785018) (.leaf 2043199250)) (.branch 55 (.leaf 2000698510) (.leaf 1959249752))) (.branch 58 (.branch 57 (.leaf 1918821137) (.leaf 1879381990)) (.branch 59 (.leaf 1840902742) (.leaf 1803354887))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1766710939) (.branch 62 (.leaf 1730944385) (.leaf 1696029648))) (.branch 65 (.branch 64 (.leaf 1661942050) (.leaf 1628657770)) (.branch 66 (.leaf 1596153813) (.leaf 1564407978)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1533398821) (.leaf 1503105630)) (.branch 70 (.leaf 1473508393) (.leaf 1444587771))) (.branch 73 (.branch 72 (.leaf 1416325071) (.leaf 1388702223)) (.branch 74 (.leaf 1361701755) (.leaf 1335306767))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1309500913) (.branch 77 (.leaf 1284268380) (.leaf 1259593862))) (.branch 80 (.branch 79 (.leaf 1235462550) (.leaf 1211860104)) (.branch 81 (.leaf 1188772643) (.leaf 1166186722)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1144089322) (.leaf 1122467828)) (.branch 85 (.leaf 1101310020) (.leaf 1080604054))) (.branch 88 (.branch 87 (.leaf 1060338451) (.leaf 1040502084)) (.branch 89 (.leaf 1021084162) (.leaf 1002074224)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 983462121) (.branch 92 (.leaf 965238010) (.leaf 947392340))) (.branch 95 (.branch 94 (.leaf 929915842) (.leaf 912799522)) (.branch 96 (.leaf 896034649) (.leaf 879612746)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 863525581) (.leaf 847765161)) (.branch 100 (.leaf 832323721) (.leaf 817193719))) (.branch 103 (.branch 102 (.leaf 802367826) (.leaf 787838921)) (.branch 104 (.leaf 773600080) (.leaf 759644577))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 745965869) (.leaf 732557596)) (.branch 108 (.leaf 719413573) (.leaf 706527783))) (.branch 111 (.branch 110 (.leaf 693894373) (.leaf 681507650)) (.branch 112 (.leaf 669362073) (.leaf 657452250)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 645772932) (.leaf 634319010)) (.branch 116 (.leaf 623085510) (.leaf 612067587))) (.branch 119 (.branch 118 (.leaf 601260526) (.leaf 590659731)) (.branch 120 (.leaf 580260726) (.leaf 570059151)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 991).prefactor = (5107890788590123/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 991).cutoff/(generalMeanRows 991).c)).2 =
    (69570779728617/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 991).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 991).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 991).q*(generalMeanRows 991).c/2-2 = (2611/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable317.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 991).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 991

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 991).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 991).criticalRate j.val*(generalMeanRows 991).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 991).c*(generalMeanRows 991).criticalPoint j.val)).2-
      (generalMeanRows 991).J/2-(generalMeanRows 991).error (generalMeanGrid j.val)+
      (generalMeanRows 991).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 991).c)).2-
      (generalMeanRows 991).J/2-(generalMeanRows 991).error 4 := by
  have he : (generalMeanRows 991).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 991) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 991)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0991

/-! Kernel-checked entropy margins for general spectral rectangle 992. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0992
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7071281766) (.branch 2 (.leaf 6858811223) (.leaf 6654587791))) (.branch 5 (.branch 4 (.leaf 6458189183) (.leaf 6269221922)) (.branch 6 (.leaf 6087318749) (.leaf 5912136329)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5743353213) (.leaf 5580668017)) (.branch 10 (.leaf 5423797792) (.leaf 5272476562))) (.branch 13 (.branch 12 (.leaf 5126454011) (.leaf 4985494295)) (.branch 14 (.leaf 4849374969) (.leaf 4717886012))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4590828946) (.branch 17 (.leaf 4468016027) (.leaf 4349269515))) (.branch 20 (.branch 19 (.leaf 4234420996) (.leaf 4123310774)) (.branch 21 (.leaf 4015787301) (.leaf 3911706656)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3810932076) (.leaf 3713333505)) (.branch 25 (.leaf 3618787193) (.leaf 3527175316))) (.branch 28 (.branch 27 (.leaf 3438385629) (.leaf 3352311143)) (.branch 29 (.leaf 3268849821) (.leaf 3187904300)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3109381634) (.branch 32 (.leaf 3033193046) (.leaf 2959253705))) (.branch 35 (.branch 34 (.leaf 2887482512) (.leaf 2817801906)) (.branch 36 (.leaf 2750137675) (.leaf 2684418784)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2620577213) (.leaf 2558547803)) (.branch 40 (.leaf 2498268115) (.leaf 2439678290))) (.branch 43 (.branch 42 (.leaf 2382720930) (.leaf 2327340969)) (.branch 44 (.leaf 2273485569) (.leaf 2221104010))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2170147589) (.branch 47 (.leaf 2120569525) (.leaf 2072324874))) (.branch 50 (.branch 49 (.leaf 2025370441) (.leaf 1979664699)) (.branch 51 (.leaf 1935167715) (.leaf 1891841080)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1849647839) (.leaf 1808552425)) (.branch 55 (.leaf 1768520602) (.leaf 1729519404))) (.branch 58 (.branch 57 (.leaf 1691517080) (.leaf 1654483044)) (.branch 59 (.leaf 1618387824) (.leaf 1583203014))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1548901228) (.branch 62 (.leaf 1515456063) (.leaf 1482842050))) (.branch 65 (.branch 64 (.leaf 1451034622) (.leaf 1420010074)) (.branch 66 (.leaf 1389745529) (.leaf 1360218903)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1331408873) (.leaf 1303294849)) (.branch 70 (.leaf 1275856943) (.leaf 1249075940))) (.branch 73 (.branch 72 (.leaf 1222933274) (.leaf 1197411002)) (.branch 74 (.leaf 1172491778) (.leaf 1148158832))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1124395945) (.branch 77 (.leaf 1101187434) (.leaf 1078518123))) (.branch 80 (.branch 79 (.leaf 1056373330) (.leaf 1034738848)) (.branch 81 (.leaf 1013600924) (.leaf 992946244)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 972761917) (.leaf 953035460)) (.branch 85 (.leaf 933754780) (.leaf 914908164))) (.branch 88 (.branch 87 (.leaf 896484262) (.leaf 878472074)) (.branch 89 (.leaf 860860938) (.leaf 843640521)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 826800802) (.branch 92 (.leaf 810332064) (.leaf 794224883))) (.branch 95 (.branch 94 (.leaf 778470116) (.leaf 763058894)) (.branch 96 (.leaf 747982612) (.leaf 733232915)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 718801698) (.leaf 704681089)) (.branch 100 (.leaf 690863448) (.leaf 677341352))) (.branch 103 (.branch 102 (.leaf 664107596) (.leaf 651155178)) (.branch 104 (.leaf 638477297) (.leaf 626067343))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 613918896) (.leaf 602025712)) (.branch 108 (.leaf 590381724) (.leaf 578981033))) (.branch 111 (.branch 110 (.leaf 567817904) (.leaf 556886757)) (.branch 112 (.leaf 546182168) (.leaf 535698860)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 525431698) (.leaf 515375686)) (.branch 116 (.leaf 505525964) (.leaf 495877800))) (.branch 119 (.branch 118 (.leaf 486426589) (.leaf 477167847)) (.branch 120 (.leaf 468097210) (.leaf 459210426)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 992).prefactor = (511212072459053/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 992).cutoff/(generalMeanRows 992).c)).2 =
    (134600707193117/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 992).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 992).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 992).q*(generalMeanRows 992).c/2-2 = (71/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable291.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 992).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 992

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 992).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 992).criticalRate j.val*(generalMeanRows 992).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 992).c*(generalMeanRows 992).criticalPoint j.val)).2-
      (generalMeanRows 992).J/2-(generalMeanRows 992).error (generalMeanGrid j.val)+
      (generalMeanRows 992).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 992).c)).2-
      (generalMeanRows 992).J/2-(generalMeanRows 992).error 4 := by
  have he : (generalMeanRows 992).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 992) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 992)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0992

/-! Kernel-checked entropy margins for general spectral rectangle 993. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0993
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6941852812) (.branch 2 (.leaf 6744152178) (.leaf 6554134115))) (.branch 5 (.branch 4 (.leaf 6371398258) (.leaf 6195571729)) (.branch 6 (.leaf 6026306673) (.leaf 5863278087)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5706181880) (.leaf 5554733136)) (.branch 10 (.leaf 5408664571) (.leaf 5267725129))) (.branch 13 (.branch 12 (.leaf 5131678736) (.leaf 5000303162)) (.branch 14 (.leaf 4873388994) (.leaf 4750738706))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4632165814) (.branch 17 (.leaf 4517494100) (.leaf 4406556911))) (.branch 20 (.branch 19 (.leaf 4299196512) (.leaf 4195263499)) (.branch 21 (.leaf 4094616249) (.leaf 3997120429)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3902648529) (.leaf 3811079443)) (.branch 25 (.leaf 3722298075) (.leaf 3636194976))) (.branch 28 (.branch 27 (.leaf 3552666009) (.leaf 3471612034)) (.branch 29 (.leaf 3392938624) (.leaf 3316555790)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3242377733) (.branch 32 (.leaf 3170322609) (.leaf 3100312311))) (.branch 35 (.branch 34 (.leaf 3032272267) (.leaf 2966131246)) (.branch 36 (.leaf 2901821183) (.leaf 2839277008)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2778436494) (.leaf 2719240108)) (.branch 40 (.leaf 2661630871) (.leaf 2605554231))) (.branch 43 (.branch 42 (.leaf 2550957939) (.leaf 2497791938)) (.branch 44 (.leaf 2446008249) (.leaf 2395560873))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2346405696) (.branch 47 (.leaf 2298500394) (.leaf 2251804352))) (.branch 50 (.branch 49 (.leaf 2206278579) (.leaf 2161885635)) (.branch 51 (.leaf 2118589556) (.leaf 2076355788)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2035151120) (.leaf 1994943623)) (.branch 55 (.leaf 1955702596) (.leaf 1917398503))) (.branch 58 (.branch 57 (.leaf 1880002927) (.leaf 1843488519)) (.branch 59 (.leaf 1807828949) (.leaf 1772998865))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1738973845) (.branch 62 (.leaf 1705730363) (.leaf 1673245744))) (.branch 65 (.branch 64 (.leaf 1641498134) (.leaf 1610466460)) (.branch 66 (.leaf 1580130400) (.leaf 1550470351)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1521467396) (.leaf 1493103282)) (.branch 70 (.leaf 1465360386) (.leaf 1438221692))) (.branch 73 (.branch 72 (.leaf 1411670767) (.leaf 1385691736)) (.branch 74 (.leaf 1360269261) (.leaf 1335388517))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1311035173) (.branch 77 (.leaf 1287195374) (.leaf 1263855719))) (.branch 80 (.branch 79 (.leaf 1241003246) (.leaf 1218625413)) (.branch 81 (.leaf 1196710083) (.leaf 1175245507)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1154220312) (.leaf 1133623481)) (.branch 85 (.leaf 1113444346) (.leaf 1093672572))) (.branch 88 (.branch 87 (.leaf 1074298143) (.leaf 1055311351)) (.branch 89 (.leaf 1036702787) (.leaf 1018463327)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1000584123) (.branch 92 (.leaf 983056592) (.leaf 965872406))) (.branch 95 (.branch 94 (.leaf 949023485) (.leaf 932501987)) (.branch 96 (.leaf 916300298) (.leaf 900411025)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 884826989) (.leaf 869541218)) (.branch 100 (.leaf 854546935) (.leaf 839837559))) (.branch 103 (.branch 102 (.leaf 825406689) (.leaf 811248108)) (.branch 104 (.leaf 797355768) (.leaf 783723788))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 770346450) (.leaf 757218190)) (.branch 108 (.leaf 744333594) (.leaf 731687395))) (.branch 111 (.branch 110 (.leaf 719274465) (.leaf 707089814)) (.branch 112 (.leaf 695128580) (.leaf 683386033)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 671857562) (.leaf 660538678)) (.branch 116 (.leaf 649425006) (.leaf 638512282))) (.branch 119 (.branch 118 (.leaf 627796352) (.leaf 617273166)) (.branch 120 (.leaf 606938775) (.leaf 596789329)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 993).prefactor = (4851087689391467/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 993).cutoff/(generalMeanRows 993).c)).2 =
    (32419157065511/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 993).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 993).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 993).q*(generalMeanRows 993).c/2-2 = (253/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable141.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 993).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 993

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 993).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 993).criticalRate j.val*(generalMeanRows 993).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 993).c*(generalMeanRows 993).criticalPoint j.val)).2-
      (generalMeanRows 993).J/2-(generalMeanRows 993).error (generalMeanGrid j.val)+
      (generalMeanRows 993).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 993).c)).2-
      (generalMeanRows 993).J/2-(generalMeanRows 993).error 4 := by
  have he : (generalMeanRows 993).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 993) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 993)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0993

/-! Kernel-checked entropy margins for general spectral rectangle 994. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0994
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6710133902) (.branch 2 (.leaf 6515957921) (.leaf 6329404137))) (.branch 5 (.branch 4 (.leaf 6150072931) (.leaf 5977592139)) (.branch 6 (.leaf 5811614604) (.leaf 5651816013)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5497892960) (.leaf 5349561221)) (.branch 10 (.leaf 5206554206) (.leaf 5068621568))) (.branch 13 (.branch 12 (.leaf 4935527948) (.leaf 4807051843)) (.branch 14 (.leaf 4682984581) (.leaf 4563129389))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4447300544) (.branch 17 (.leaf 4335322603) (.leaf 4227029696))) (.branch 20 (.branch 19 (.leaf 4122264881) (.leaf 4020879552)) (.branch 21 (.leaf 3922732893) (.leaf 3827691380)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3735628321) (.leaf 3646423426)) (.branch 25 (.leaf 3559962418) (.leaf 3476136666))) (.branch 28 (.branch 27 (.leaf 3394842852) (.leaf 3315982653)) (.branch 29 (.leaf 3239462453) (.leaf 3165193072)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3093089516) (.branch 32 (.leaf 3023070739) (.leaf 2955059425))) (.branch 35 (.branch 34 (.leaf 2888981785) (.leaf 2824767365)) (.branch 36 (.leaf 2762348867) (.leaf 2701661980)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2642645224) (.leaf 2585239803)) (.branch 40 (.leaf 2529389466) (.leaf 2475040376))) (.branch 43 (.branch 42 (.leaf 2422140990) (.leaf 2370641943)) (.branch 44 (.leaf 2320495936) (.leaf 2271657640))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2224083596) (.branch 47 (.leaf 2177732126) (.leaf 2132563243))) (.branch 50 (.branch 49 (.leaf 2088538577) (.leaf 2045621293)) (.branch 51 (.leaf 2003776021) (.leaf 1962968785)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1923166944) (.leaf 1884339124)) (.branch 55 (.leaf 1846455164) (.leaf 1809486059))) (.branch 58 (.branch 57 (.leaf 1773403910) (.leaf 1738181873)) (.branch 59 (.leaf 1703794111) (.leaf 1670215751))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1637422842) (.branch 62 (.leaf 1605392313) (.leaf 1574101936))) (.branch 65 (.branch 64 (.leaf 1543530290) (.leaf 1513656726)) (.branch 66 (.leaf 1484461332) (.leaf 1455924907)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1428028925) (.leaf 1400755511)) (.branch 70 (.leaf 1374087412) (.leaf 1348007971))) (.branch 73 (.branch 72 (.leaf 1322501106) (.leaf 1297551280)) (.branch 74 (.leaf 1273143486) (.leaf 1249263221))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1225896465) (.branch 77 (.leaf 1203029667) (.leaf 1180649721))) (.branch 80 (.branch 79 (.leaf 1158743950) (.leaf 1137300091)) (.branch 81 (.leaf 1116306277) (.leaf 1095751022)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1075623207) (.leaf 1055912063)) (.branch 85 (.leaf 1036607162) (.leaf 1017698402))) (.branch 88 (.branch 87 (.leaf 999175993) (.leaf 981030448)) (.branch 89 (.leaf 963252571) (.leaf 945833445)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 928764422) (.branch 92 (.leaf 912037116) (.leaf 895643388))) (.branch 95 (.branch 94 (.leaf 879575342) (.leaf 863825314)) (.branch 96 (.leaf 848385864) (.leaf 833249766)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 818410007) (.leaf 803859770)) (.branch 100 (.leaf 789592434) (.leaf 775601567))) (.branch 103 (.branch 102 (.leaf 761880915) (.leaf 748424400)) (.branch 104 (.leaf 735226111) (.leaf 722280302))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 709581381) (.leaf 697123912)) (.branch 108 (.leaf 684902602) (.leaf 672912304))) (.branch 111 (.branch 110 (.leaf 661148003) (.leaf 649604822)) (.branch 112 (.leaf 638278010) (.leaf 627162940)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 616255106) (.leaf 605550118)) (.branch 116 (.leaf 595043698) (.leaf 584731679))) (.branch 119 (.branch 118 (.leaf 574609999) (.leaf 564674696)) (.branch 120 (.leaf 554921911) (.leaf 545347878)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 994).prefactor = (151055334387707/31250000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 994).cutoff/(generalMeanRows 994).c)).2 =
    (642345529333/1953125000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 994).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 994).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 994).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 994

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 994).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 994).criticalRate j.val*(generalMeanRows 994).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 994).c*(generalMeanRows 994).criticalPoint j.val)).2-
      (generalMeanRows 994).J/2-(generalMeanRows 994).error (generalMeanGrid j.val)+
      (generalMeanRows 994).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 994).c)).2-
      (generalMeanRows 994).J/2-(generalMeanRows 994).error 4 := by
  have he : (generalMeanRows 994).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 994) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 994)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0994

/-! Kernel-checked entropy margins for general spectral rectangle 995. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0995
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6528172872) (.branch 2 (.leaf 6337867470) (.leaf 6155095081))) (.branch 5 (.branch 4 (.leaf 5979457914) (.leaf 5810585558)) (.branch 6 (.leaf 5648132556) (.leaf 5491776246)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5341214838) (.leaf 5196165691)) (.branch 10 (.leaf 5056363774) (.leaf 4921560277))) (.branch 13 (.branch 12 (.leaf 4791521360) (.leaf 4666027023)) (.branch 14 (.leaf 4544870083) (.leaf 4427855241))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4314798235) (.branch 17 (.leaf 4205525072) (.leaf 4099871319))) (.branch 20 (.branch 19 (.leaf 3997681455) (.leaf 3898808285)) (.branch 21 (.leaf 3803112388) (.leaf 3710461624)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3620730664) (.leaf 3533800572)) (.branch 25 (.leaf 3449558405) (.leaf 3367896852))) (.branch 28 (.branch 27 (.leaf 3288713893) (.leaf 3211912491)) (.branch 29 (.leaf 3137400293) (.leaf 3065089367)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2994895944) (.branch 32 (.leaf 2926740185) (.leaf 2860545962))) (.branch 35 (.branch 34 (.leaf 2796240652) (.leaf 2733754947)) (.branch 36 (.leaf 2673022672) (.leaf 2613980620)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2556568395) (.leaf 2500728261)) (.branch 40 (.leaf 2446405005) (.leaf 2393545810))) (.branch 43 (.branch 42 (.leaf 2342100128) (.leaf 2292019568)) (.branch 44 (.leaf 2243257786) (.leaf 2195770384))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2149514814) (.branch 47 (.leaf 2104450286) (.leaf 2060537684))) (.branch 50 (.branch 49 (.leaf 2017739484) (.leaf 1976019679)) (.branch 51 (.leaf 1935343704) (.leaf 1895678373)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1856991809) (.leaf 1819253386)) (.branch 55 (.leaf 1782433672) (.leaf 1746504370))) (.branch 58 (.branch 57 (.leaf 1711438272) (.leaf 1677209204)) (.branch 59 (.leaf 1643791984) (.leaf 1611162376))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1579297045) (.branch 62 (.leaf 1548173524) (.leaf 1517770168))) (.branch 65 (.branch 64 (.leaf 1488066124) (.leaf 1459041296)) (.branch 66 (.leaf 1430676309) (.leaf 1402952480)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1375851792) (.leaf 1349356860)) (.branch 70 (.leaf 1323450907) (.leaf 1298117741))) (.branch 73 (.branch 72 (.leaf 1273341725) (.leaf 1249107762)) (.branch 74 (.leaf 1225401265) (.leaf 1202208141))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1179514768) (.branch 77 (.leaf 1157307980) (.leaf 1135575044))) (.branch 80 (.branch 79 (.leaf 1114303647) (.leaf 1093481876)) (.branch 81 (.leaf 1073098205) (.leaf 1053141475)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1033600888) (.leaf 1014465986)) (.branch 85 (.leaf 995726638) (.leaf 977373033))) (.branch 88 (.branch 87 (.leaf 959395664) (.leaf 941785314)) (.branch 89 (.leaf 924533052) (.leaf 907630215)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 891068404) (.branch 92 (.leaf 874839470) (.leaf 858935507))) (.branch 95 (.branch 94 (.leaf 843348844) (.leaf 828072032)) (.branch 96 (.leaf 813097842) (.leaf 798419253)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 784029447) (.leaf 769921798)) (.branch 100 (.leaf 756089870) (.leaf 742527408))) (.branch 103 (.branch 102 (.leaf 729228331) (.leaf 716186729)) (.branch 104 (.leaf 703396853) (.leaf 690853112))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 678550068) (.leaf 666482429)) (.branch 108 (.leaf 654645047) (.leaf 643032908))) (.branch 111 (.branch 110 (.leaf 631641134) (.leaf 620464975)) (.branch 112 (.leaf 609499804) (.leaf 598741115)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 588184520) (.leaf 577825741)) (.branch 116 (.leaf 567660610) (.leaf 557685066))) (.branch 119 (.branch 118 (.leaf 547895148) (.leaf 538286996)) (.branch 120 (.leaf 528856845) (.leaf 519601025)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 995).prefactor = (2403134730694089/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 995).cutoff/(generalMeanRows 995).c)).2 =
    (67665216318003/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 995).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 995).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 995).q*(generalMeanRows 995).c/2-2 = (1339/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable323.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 995).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 995

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 995).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 995).criticalRate j.val*(generalMeanRows 995).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 995).c*(generalMeanRows 995).criticalPoint j.val)).2-
      (generalMeanRows 995).J/2-(generalMeanRows 995).error (generalMeanGrid j.val)+
      (generalMeanRows 995).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 995).c)).2-
      (generalMeanRows 995).J/2-(generalMeanRows 995).error 4 := by
  have he : (generalMeanRows 995).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 995) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 995)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0995

/-! Kernel-checked entropy margins for general spectral rectangle 996. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0996
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6250118281) (.branch 2 (.leaf 6064285755) (.leaf 5885892123))) (.branch 5 (.branch 4 (.leaf 5714541993) (.leaf 5549867232)) (.branch 6 (.leaf 5391524559) (.leaf 5239193397)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5092573967) (.leaf 4951385572)) (.branch 10 (.leaf 4815365068) (.leaf 4684265479))) (.branch 13 (.branch 12 (.leaf 4557854753) (.leaf 4435914638)) (.branch 14 (.leaf 4318239655) (.leaf 4204636177))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4094921579) (.branch 17 (.leaf 3988923471) (.leaf 3886478994))) (.branch 20 (.branch 19 (.leaf 3787434171) (.leaf 3691643318)) (.branch 21 (.leaf 3598968502) (.leaf 3509279037)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3422451026) (.leaf 3338366932)) (.branch 25 (.leaf 3256915187) (.leaf 3177989826))) (.branch 28 (.branch 27 (.leaf 3101490152) (.leaf 3027320418)) (.branch 29 (.leaf 2955389539) (.leaf 2885610821)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2817901709) (.branch 32 (.leaf 2752183550) (.leaf 2688381376))) (.branch 35 (.branch 34 (.leaf 2626423699) (.leaf 2566242318)) (.branch 36 (.leaf 2507772142) (.leaf 2450951021)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2395719588) (.leaf 2342021115)) (.branch 40 (.leaf 2289801371) (.leaf 2239008496))) (.branch 43 (.branch 42 (.leaf 2189592874) (.leaf 2141507024)) (.branch 44 (.leaf 2094705487) (.leaf 2049144727))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2004783036) (.branch 47 (.leaf 1961580441) (.leaf 1919498620))) (.branch 50 (.branch 49 (.leaf 1878500822) (.leaf 1838551792)) (.branch 51 (.leaf 1799617697) (.leaf 1761666060)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1724665695) (.leaf 1688586647)) (.branch 55 (.leaf 1653400133) (.leaf 1619078492))) (.branch 58 (.branch 57 (.leaf 1585595127) (.leaf 1552924462)) (.branch 59 (.leaf 1521041894) (.leaf 1489923746))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1459547231) (.branch 62 (.leaf 1429890408) (.leaf 1400932146))) (.branch 65 (.branch 64 (.leaf 1372652090) (.leaf 1345030624)) (.branch 66 (.leaf 1318048842) (.leaf 1291688515)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1265932063) (.leaf 1240762529)) (.branch 70 (.leaf 1216163548) (.leaf 1192119329))) (.branch 73 (.branch 72 (.leaf 1168614624) (.leaf 1145634709)) (.branch 74 (.leaf 1123165362) (.leaf 1101192845))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1079703877) (.branch 77 (.leaf 1058685624) (.leaf 1038125675))) (.branch 80 (.branch 79 (.leaf 1018012026) (.leaf 998333068)) (.branch 81 (.leaf 979077566) (.leaf 960234646)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 941793784) (.leaf 923744787)) (.branch 85 (.leaf 906077786) (.leaf 888783217))) (.branch 88 (.branch 87 (.leaf 871851815) (.leaf 855274602)) (.branch 89 (.leaf 839042872) (.leaf 823148186)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 807582357) (.branch 92 (.leaf 792337446) (.leaf 777405749))) (.branch 95 (.branch 94 (.leaf 762779790) (.leaf 748452313)) (.branch 96 (.leaf 734416272) (.leaf 720664825)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 707191329) (.leaf 693989328)) (.branch 100 (.leaf 681052550) (.leaf 668374901))) (.branch 103 (.branch 102 (.leaf 655950455) (.leaf 643773451)) (.branch 104 (.leaf 631838290) (.leaf 620139523))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 608671851) (.leaf 597430118)) (.branch 108 (.leaf 586409306) (.leaf 575604533))) (.branch 111 (.branch 110 (.leaf 565011045) (.leaf 554624213)) (.branch 112 (.leaf 544439530) (.leaf 534452606)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 524659165) (.leaf 515055041)) (.branch 116 (.leaf 505636173) (.leaf 496398606))) (.branch 119 (.branch 118 (.leaf 487338481) (.leaf 478452040)) (.branch 120 (.leaf 469735616) (.leaf 461185633)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 996).prefactor = (47697369695181/10000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 996).cutoff/(generalMeanRows 996).c)).2 =
    (341891147754511/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 996).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 996).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 996).q*(generalMeanRows 996).c/2-2 = (7/10:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable043.value]
    have hcontinuation : (generalMeanRows 996).q*(generalMeanRows 996).cutoff/2-2 = (668/371:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable324.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 996).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 996

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 996).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 996).criticalRate j.val*(generalMeanRows 996).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 996).c*(generalMeanRows 996).criticalPoint j.val)).2-
      (generalMeanRows 996).J/2-(generalMeanRows 996).error (generalMeanGrid j.val)+
      (generalMeanRows 996).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 996).c)).2-
      (generalMeanRows 996).J/2-(generalMeanRows 996).error 4 := by
  have he : (generalMeanRows 996).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 996) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 996)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0996

/-! Kernel-checked entropy margins for general spectral rectangle 997. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0997
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5854178231) (.branch 2 (.leaf 5663665741) (.leaf 5480983448))) (.branch 5 (.branch 4 (.leaf 5305717181) (.leaf 5137481107)) (.branch 6 (.leaf 4975915234) (.leaf 4820683189)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4671470239) (.leaf 4527981514)) (.branch 10 (.leaf 4389940420) (.leaf 4257087205))) (.branch 13 (.branch 12 (.leaf 4129177669) (.leaf 4005981994)) (.branch 14 (.leaf 3887283688) (.leaf 3772878618))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3662574137) (.branch 17 (.leaf 3556188284) (.leaf 3453549053))) (.branch 20 (.branch 19 (.leaf 3354493721) (.leaf 3258868240)) (.branch 21 (.leaf 3166526665) (.leaf 3077330638)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2991148911) (.leaf 2907856898)) (.branch 25 (.leaf 2827336270) (.leaf 2749474578))) (.branch 28 (.branch 27 (.leaf 2674164896) (.leaf 2601305500)) (.branch 29 (.leaf 2530799564) (.leaf 2462554876)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2396483579) (.branch 32 (.leaf 2332501924) (.leaf 2270530044))) (.branch 35 (.branch 34 (.leaf 2210491738) (.leaf 2152314271)) (.branch 36 (.leaf 2095928193) (.leaf 2041267157)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1988267760) (.leaf 1936869387)) (.branch 40 (.leaf 1887014067) (.leaf 1838646340))) (.branch 43 (.branch 42 (.leaf 1791713125) (.leaf 1746163602)) (.branch 44 (.leaf 1701949102) (.leaf 1659022994))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1617340593) (.branch 47 (.leaf 1576859057) (.leaf 1537537305))) (.branch 50 (.branch 49 (.leaf 1499335927) (.leaf 1462217110)) (.branch 51 (.leaf 1426144555) (.leaf 1391083415)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1357000220) (.leaf 1323862817)) (.branch 55 (.leaf 1291640310) (.leaf 1260303000))) (.branch 58 (.branch 57 (.leaf 1229822333) (.leaf 1200170850)) (.branch 59 (.leaf 1171322132) (.leaf 1143250762))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1115932275) (.branch 62 (.leaf 1089343118) (.leaf 1063460611))) (.branch 65 (.branch 64 (.leaf 1038262910) (.leaf 1013728968)) (.branch 66 (.leaf 989838504) (.leaf 966571969)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 943910517) (.leaf 921835973)) (.branch 70 (.leaf 900330805) (.leaf 879378101))) (.branch 73 (.branch 72 (.leaf 858961541) (.leaf 839065371)) (.branch 74 (.leaf 819674384) (.leaf 800773894))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 782349719) (.branch 77 (.leaf 764388156) (.leaf 746875968))) (.branch 80 (.branch 79 (.leaf 729800361) (.leaf 713148966)) (.branch 81 (.leaf 696909827) (.leaf 681071382)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 665622447) (.leaf 650552204)) (.branch 85 (.leaf 635850184) (.leaf 621506258))) (.branch 88 (.branch 87 (.leaf 607510619) (.leaf 593853773)) (.branch 89 (.leaf 580526530) (.leaf 567519985)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 554825515) (.branch 92 (.leaf 542434766) (.leaf 530339640))) (.branch 95 (.branch 94 (.leaf 518532293) (.leaf 507005119)) (.branch 96 (.leaf 495750742) (.leaf 484762015)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 474032002) (.leaf 463553976)) (.branch 100 (.leaf 453321414) (.leaf 443327983))) (.branch 103 (.branch 102 (.leaf 433567539) (.leaf 424034118)) (.branch 104 (.leaf 414721932) (.leaf 405625359))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 396738941) (.leaf 388057378)) (.branch 108 (.leaf 379575522) (.leaf 371288370))) (.branch 111 (.branch 110 (.leaf 363191062) (.leaf 355278877)) (.branch 112 (.leaf 347547225) (.leaf 339991644)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 332607799) (.leaf 325391473)) (.branch 116 (.leaf 318338566) (.leaf 311445090))) (.branch 119 (.branch 118 (.leaf 304707168) (.leaf 298121026)) (.branch 120 (.leaf 291682996) (.leaf 285389505)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 997).prefactor = (4959676953466319/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 997).cutoff/(generalMeanRows 997).c)).2 =
    (294424610515587/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 997).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 997).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 997).q*(generalMeanRows 997).c/2-2 = (133/160:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable309.value]
    have hcontinuation : (generalMeanRows 997).q*(generalMeanRows 997).cutoff/2-2 = (668/371:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable324.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 997).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 997

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 997).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 997).criticalRate j.val*(generalMeanRows 997).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 997).c*(generalMeanRows 997).criticalPoint j.val)).2-
      (generalMeanRows 997).J/2-(generalMeanRows 997).error (generalMeanGrid j.val)+
      (generalMeanRows 997).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 997).c)).2-
      (generalMeanRows 997).J/2-(generalMeanRows 997).error 4 := by
  have he : (generalMeanRows 997).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 997) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 997)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0997

/-! Kernel-checked entropy margins for general spectral rectangle 998. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0998
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5673257040) (.branch 2 (.leaf 5487828038) (.leaf 5310081001))) (.branch 5 (.branch 4 (.leaf 5139606289) (.leaf 4976022382)) (.branch 6 (.leaf 4818973411) (.leaf 4668126951)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4523172064) (.leaf 4383817536)) (.branch 10 (.leaf 4249790303) (.leaf 4120834026))) (.branch 13 (.branch 12 (.leaf 3996707809) (.leaf 3877185039)) (.branch 14 (.leaf 3762052335) (.leaf 3651108587))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3544164088) (.branch 17 (.leaf 3441039735) (.leaf 3341566307))) (.branch 20 (.branch 19 (.leaf 3245583793) (.leaf 3152940783)) (.branch 21 (.leaf 3063493906) (.leaf 2977107311)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2893652193) (.leaf 2813006347)) (.branch 25 (.leaf 2735053766) (.leaf 2659684260))) (.branch 28 (.branch 27 (.leaf 2586793109) (.leaf 2516280735)) (.branch 29 (.leaf 2448052405) (.leaf 2382017946)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2318091486) (.branch 32 (.leaf 2256191210) (.leaf 2196239133))) (.branch 35 (.branch 34 (.leaf 2138160886) (.leaf 2081885520)) (.branch 36 (.leaf 2027345320) (.leaf 1974475629)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1923214688) (.leaf 1873503480)) (.branch 40 (.leaf 1825285589) (.leaf 1778507066))) (.branch 43 (.branch 42 (.leaf 1733116299) (.leaf 1689063898)) (.branch 44 (.leaf 1646302578) (.leaf 1604787059))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1564473964) (.branch 47 (.leaf 1525321724) (.leaf 1487290491))) (.branch 50 (.branch 49 (.leaf 1450342055) (.leaf 1414439766)) (.branch 51 (.leaf 1379548455) (.leaf 1345634369)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1312665103) (.leaf 1280609535)) (.branch 55 (.leaf 1249437768) (.leaf 1219121074))) (.branch 58 (.branch 57 (.leaf 1189631839) (.leaf 1160943515)) (.branch 59 (.leaf 1133030568) (.leaf 1105868437))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1079433486) (.branch 62 (.leaf 1053702967) (.leaf 1028654980))) (.branch 65 (.branch 64 (.leaf 1004268433) (.leaf 980523013)) (.branch 66 (.leaf 957399146) (.leaf 934877969)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 912941298) (.leaf 891571603)) (.branch 70 (.leaf 870751973) (.leaf 850466100))) (.branch 73 (.branch 72 (.leaf 830698245) (.leaf 811433220)) (.branch 74 (.leaf 792656363) (.leaf 774353518))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 756511012) (.branch 77 (.leaf 739115640) (.leaf 722154641))) (.branch 80 (.branch 79 (.leaf 705615685) (.leaf 689486852)) (.branch 81 (.leaf 673756619) (.leaf 658413842)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 643447745) (.leaf 628847900)) (.branch 85 (.leaf 614604219) (.leaf 600706938))) (.branch 88 (.branch 87 (.leaf 587146607) (.leaf 573914075)) (.branch 89 (.leaf 561000482) (.leaf 548397246)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 536096053) (.branch 92 (.leaf 524088850) (.leaf 512367830))) (.branch 95 (.branch 94 (.leaf 500925428) (.leaf 489754310)) (.branch 96 (.leaf 478847363) (.leaf 468197693)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 457798610) (.leaf 447643625)) (.branch 100 (.leaf 437726443) (.leaf 428040954))) (.branch 103 (.branch 102 (.leaf 418581228) (.leaf 409341510)) (.branch 104 (.leaf 400316211) (.leaf 391499905))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 382887321) (.leaf 374473340)) (.branch 108 (.leaf 366252990) (.leaf 358221439))) (.branch 111 (.branch 110 (.leaf 350373992) (.leaf 342706086)) (.branch 112 (.leaf 335213284) (.leaf 327891275)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 320735867) (.leaf 313742982)) (.branch 116 (.leaf 306908656) (.leaf 300229032))) (.branch 119 (.branch 118 (.leaf 293700358) (.leaf 287318985)) (.branch 120 (.leaf 281081360) (.leaf 274984027)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 998).prefactor = (980605053875979/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 998).cutoff/(generalMeanRows 998).c)).2 =
    (306991417176511/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 998).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 998).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 998).q*(generalMeanRows 998).c/2-2 = (3359/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable311.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 998).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 998

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 998).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 998).criticalRate j.val*(generalMeanRows 998).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 998).c*(generalMeanRows 998).criticalPoint j.val)).2-
      (generalMeanRows 998).J/2-(generalMeanRows 998).error (generalMeanGrid j.val)+
      (generalMeanRows 998).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 998).c)).2-
      (generalMeanRows 998).J/2-(generalMeanRows 998).error 4 := by
  have he : (generalMeanRows 998).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 998) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 998)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0998

/-! Kernel-checked entropy margins for general spectral rectangle 999. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0999
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5579242041) (.branch 2 (.leaf 5398613158) (.leaf 5225490759))) (.branch 5 (.branch 4 (.leaf 5059470988) (.leaf 4900177860)) (.branch 6 (.leaf 4747260810) (.leaf 4600392515)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4459266949) (.leaf 4323597638)) (.branch 10 (.leaf 4193116097) (.leaf 4067570418))) (.branch 13 (.branch 12 (.leaf 3946723997) (.leaf 3830354382)) (.branch 14 (.leaf 3718252227) (.leaf 3610220339))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3506072816) (.branch 17 (.leaf 3405634252) (.leaf 3308739016))) (.branch 20 (.branch 19 (.leaf 3215230590) (.leaf 3124960957)) (.branch 21 (.leaf 3037790046) (.leaf 2953585215)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2872220779) (.leaf 2793577565)) (.branch 25 (.leaf 2717542516) (.leaf 2644008309))) (.branch 28 (.branch 27 (.leaf 2572873008) (.leaf 2504039745)) (.branch 29 (.leaf 2437416418) (.leaf 2372915409)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2310453331) (.branch 32 (.leaf 2249950781) (.leaf 2191332114))) (.branch 35 (.branch 34 (.leaf 2134525237) (.leaf 2079461408)) (.branch 36 (.leaf 2026075052) (.leaf 1974303592)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1924087282) (.leaf 1875369062)) (.branch 40 (.leaf 1828094412) (.leaf 1782211218))) (.branch 43 (.branch 42 (.leaf 1737669650) (.leaf 1694422042)) (.branch 44 (.leaf 1652422783) (.leaf 1611628211))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1571996516) (.branch 47 (.leaf 1533487647) (.leaf 1496063226))) (.branch 50 (.branch 49 (.leaf 1459686463) (.leaf 1424322084)) (.branch 51 (.leaf 1389936252) (.leaf 1356496499)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1323971664) (.leaf 1292331827)) (.branch 55 (.leaf 1261548256) (.leaf 1231593344))) (.branch 58 (.branch 57 (.leaf 1202440563) (.leaf 1174064412)) (.branch 59 (.leaf 1146440370) (.leaf 1119544852))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1093355168) (.branch 62 (.leaf 1067849478) (.leaf 1043006762))) (.branch 65 (.branch 64 (.leaf 1018806775) (.leaf 995230022)) (.branch 66 (.leaf 972257716) (.leaf 949871755)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 928054689) (.leaf 906789692)) (.branch 70 (.leaf 886060537) (.leaf 865851568))) (.branch 73 (.branch 72 (.leaf 846147679) (.leaf 826934290)) (.branch 74 (.leaf 808197325) (.leaf 789923191))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 772098760) (.branch 77 (.leaf 754711346) (.leaf 737748691))) (.branch 80 (.branch 79 (.leaf 721198949) (.leaf 705050665)) (.branch 81 (.leaf 689292762) (.leaf 673914525)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 658905591) (.leaf 644255929)) (.branch 85 (.leaf 629955831) (.leaf 615995900))) (.branch 88 (.branch 87 (.leaf 602367036) (.leaf 589060427)) (.branch 89 (.leaf 576067535) (.leaf 563380089)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 550990074) (.branch 92 (.leaf 538889721) (.leaf 527071498))) (.branch 95 (.branch 94 (.leaf 515528102) (.leaf 504252451)) (.branch 96 (.leaf 493237674) (.leaf 482477106)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 471964280) (.leaf 461692918)) (.branch 100 (.leaf 451656927) (.leaf 441850391))) (.branch 103 (.branch 102 (.leaf 432267566) (.leaf 422902874)) (.branch 104 (.leaf 413750894) (.leaf 404806364))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 396064166) (.leaf 387519329)) (.branch 108 (.leaf 379167022) (.leaf 371002546))) (.branch 111 (.branch 110 (.leaf 363021336) (.leaf 355218949)) (.branch 112 (.leaf 347591066) (.leaf 340133487)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 332842123) (.leaf 325712999)) (.branch 116 (.leaf 318742245) (.leaf 311926094))) (.branch 119 (.branch 118 (.leaf 305260882) (.leaf 298743040)) (.branch 120 (.leaf 292369093) (.leaf 286135659)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 999).prefactor = (968009212210663/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 999).cutoff/(generalMeanRows 999).c)).2 =
    (327119830434199/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 999).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 999).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 999).q*(generalMeanRows 999).c/2-2 = (663/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable325.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 999).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 999

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 999).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 999).criticalRate j.val*(generalMeanRows 999).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 999).c*(generalMeanRows 999).criticalPoint j.val)).2-
      (generalMeanRows 999).J/2-(generalMeanRows 999).error (generalMeanGrid j.val)+
      (generalMeanRows 999).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 999).c)).2-
      (generalMeanRows 999).J/2-(generalMeanRows 999).error 4 := by
  have he : (generalMeanRows 999).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 999) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 999)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0999

/-! Kernel-checked entropy margins for general spectral rectangle 1000. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1000
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5571423124) (.branch 2 (.leaf 5395383497) (.leaf 5226647439))) (.branch 5 (.branch 4 (.leaf 5064818037) (.leaf 4909525968)) (.branch 6 (.leaf 4760427078) (.leaf 4617200221)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4479545334) (.leaf 4347181706)) (.branch 10 (.leaf 4219846429) (.leaf 4097292994))) (.branch 13 (.branch 12 (.leaf 3979290031) (.leaf 3865620163)) (.branch 14 (.leaf 3756078967) (.leaf 3650474032))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3548624094) (.branch 17 (.leaf 3450358255) (.leaf 3355515259))) (.branch 20 (.branch 19 (.leaf 3263942840) (.leaf 3175497111)) (.branch 21 (.leaf 3090042012) (.leaf 3007448798)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2927595565) (.leaf 2850366820)) (.branch 25 (.leaf 2775653071) (.leaf 2703350460))) (.branch 28 (.branch 27 (.leaf 2633360415) (.leaf 2565589333)) (.branch 29 (.leaf 2499948278) (.leaf 2436352707)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2374722213) (.branch 32 (.leaf 2314980282) (.leaf 2257054074))) (.branch 35 (.branch 34 (.leaf 2200874211) (.leaf 2146374585)) (.branch 36 (.leaf 2093492172) (.leaf 2042166865)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1992341312) (.leaf 1943960770)) (.branch 40 (.leaf 1896972959) (.leaf 1851327939))) (.branch 43 (.branch 42 (.leaf 1806977977) (.leaf 1763877439)) (.branch 44 (.leaf 1721982679) (.leaf 1681251931))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1641645222) (.branch 47 (.leaf 1603124275) (.leaf 1565652423))) (.branch 50 (.branch 49 (.leaf 1529194534) (.leaf 1493716929)) (.branch 51 (.leaf 1459187313) (.leaf 1425574709)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1392849391) (.leaf 1360982826)) (.branch 55 (.leaf 1329947615) (.leaf 1299717443))) (.branch 58 (.branch 57 (.leaf 1270267021) (.leaf 1241572047)) (.branch 59 (.leaf 1213609153) (.leaf 1186355863))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1159790556) (.branch 62 (.leaf 1133892425) (.leaf 1108641436))) (.branch 65 (.branch 64 (.leaf 1084018301) (.leaf 1060004440)) (.branch 66 (.leaf 1036581949) (.leaf 1013733573)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 991442678) (.leaf 969693219)) (.branch 70 (.leaf 948469721) (.leaf 927757251))) (.branch 73 (.branch 72 (.leaf 907541397) (.leaf 887808244)) (.branch 74 (.leaf 868544353) (.leaf 849736743))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 831372873) (.branch 77 (.leaf 813440620) (.leaf 795928265))) (.branch 80 (.branch 79 (.leaf 778824478) (.leaf 762118296)) (.branch 81 (.leaf 745799116) (.leaf 729856677)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 714281046) (.leaf 699062607)) (.branch 85 (.leaf 684192046) (.leaf 669660344))) (.branch 88 (.branch 87 (.leaf 655458760) (.leaf 641578825)) (.branch 89 (.leaf 628012330) (.leaf 614751316)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 601788064) (.branch 92 (.leaf 589115089) (.leaf 576725129))) (.branch 95 (.branch 94 (.leaf 564611136) (.leaf 552766271)) (.branch 96 (.leaf 541183895) (.leaf 529857562)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 518781012) (.leaf 507948165)) (.branch 100 (.leaf 497353114) (.leaf 486990119))) (.branch 103 (.branch 102 (.leaf 476853603) (.leaf 466938143)) (.branch 104 (.leaf 457238470) (.leaf 447749457))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 438466120) (.leaf 429383611)) (.branch 108 (.leaf 420497213) (.leaf 411802337))) (.branch 111 (.branch 110 (.leaf 403294517) (.leaf 394969405)) (.branch 112 (.leaf 386822771) (.leaf 378850493)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 371048562) (.leaf 363413069)) (.branch 116 (.leaf 355940209) (.leaf 348626276))) (.branch 119 (.branch 118 (.leaf 341467657) (.leaf 334460833)) (.branch 120 (.leaf 327602374) (.leaf 320888937)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1000).prefactor = (4771596813378881/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1000).cutoff/(generalMeanRows 1000).c)).2 =
    (354670874400909/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1000).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1000).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1000).q*(generalMeanRows 1000).c/2-2 = (799/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable320.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1000).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1000

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1000).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1000).criticalRate j.val*(generalMeanRows 1000).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1000).c*(generalMeanRows 1000).criticalPoint j.val)).2-
      (generalMeanRows 1000).J/2-(generalMeanRows 1000).error (generalMeanGrid j.val)+
      (generalMeanRows 1000).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1000).c)).2-
      (generalMeanRows 1000).J/2-(generalMeanRows 1000).error 4 := by
  have he : (generalMeanRows 1000).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1000) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1000)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1000

/-! Kernel-checked entropy margins for general spectral rectangle 1001. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1001
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5401638453) (.branch 2 (.leaf 5231126771) (.leaf 5067728783))) (.branch 5 (.branch 4 (.leaf 4911054268) (.leaf 4760740292)) (.branch 6 (.leaf 4616448815) (.leaf 4477864553)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4344693076) (.leaf 4216659088)) (.branch 10 (.leaf 4093504900) (.leaf 3974989033))) (.branch 13 (.branch 12 (.leaf 3860884970) (.leaf 3750980024)) (.branch 14 (.leaf 3645074301) (.leaf 3542979768))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3444519400) (.branch 17 (.leaf 3349526394) (.leaf 3257843463))) (.branch 20 (.branch 19 (.leaf 3169322178) (.leaf 3083822369)) (.branch 21 (.leaf 3001211573) (.leaf 2921364529)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2844162706) (.leaf 2769493874)) (.branch 25 (.leaf 2697251703) (.leaf 2627335395))) (.branch 28 (.branch 27 (.leaf 2559649340) (.leaf 2494102801)) (.branch 29 (.leaf 2430609616) (.leaf 2369087926)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2309459921) (.branch 32 (.leaf 2251651599) (.leaf 2195592551))) (.branch 35 (.branch 34 (.leaf 2141215748) (.leaf 2088457353)) (.branch 36 (.leaf 2037256538) (.leaf 1987555319)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1939298396) (.leaf 1892433007)) (.branch 40 (.leaf 1846908789) (.leaf 1802677649))) (.branch 43 (.branch 42 (.leaf 1759693642) (.leaf 1717912859)) (.branch 44 (.leaf 1677293318) (.leaf 1637794863))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1599379070) (.branch 47 (.leaf 1562009160) (.leaf 1525649912))) (.branch 50 (.branch 49 (.leaf 1490267586) (.leaf 1455829848)) (.branch 51 (.leaf 1422305700) (.leaf 1389665414)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1357880471) (.leaf 1326923498)) (.branch 55 (.leaf 1296768219) (.leaf 1267389395))) (.branch 58 (.branch 57 (.leaf 1238762782) (.leaf 1210865076)) (.branch 59 (.leaf 1183673877) (.leaf 1157167640))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1131325639) (.branch 62 (.leaf 1106127930) (.leaf 1081555313))) (.branch 65 (.branch 64 (.leaf 1057589299) (.leaf 1034212077)) (.branch 66 (.leaf 1011406487) (.leaf 989155989)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 967444635) (.leaf 946257043)) (.branch 70 (.leaf 925578376) (.leaf 905394313))) (.branch 73 (.branch 72 (.leaf 885691032) (.leaf 866455186)) (.branch 74 (.leaf 847673882) (.leaf 829334666))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 811425501) (.branch 77 (.leaf 793934753) (.leaf 776851169))) (.branch 80 (.branch 79 (.leaf 760163868) (.leaf 743862324)) (.branch 81 (.leaf 727936349) (.leaf 712376082)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 697171975) (.leaf 682314784)) (.branch 85 (.leaf 667795552) (.leaf 653605601))) (.branch 88 (.branch 87 (.leaf 639736522) (.leaf 626180163)) (.branch 89 (.leaf 612928618) (.leaf 599974224)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 587309544) (.branch 92 (.leaf 574927363) (.leaf 562820680))) (.branch 95 (.branch 94 (.leaf 550982700) (.leaf 539406824)) (.branch 96 (.leaf 528086647) (.leaf 517015944)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 506188673) (.leaf 495598958)) (.branch 100 (.leaf 485241092) (.leaf 475109528))) (.branch 103 (.branch 102 (.leaf 465198871) (.leaf 455503877)) (.branch 104 (.leaf 446019445) (.leaf 436740615))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 427662559) (.leaf 418780582)) (.branch 108 (.leaf 410090112) (.leaf 401586702))) (.branch 111 (.branch 110 (.leaf 393266021) (.leaf 385123853)) (.branch 112 (.leaf 377156091) (.leaf 369358736)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 361727895) (.leaf 354259771)) (.branch 116 (.leaf 346950669) (.leaf 339796984))) (.branch 119 (.branch 118 (.leaf 332795205) (.leaf 325941911)) (.branch 120 (.leaf 319233764) (.leaf 312667511)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1001).prefactor = (234923108055817/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1001).cutoff/(generalMeanRows 1001).c)).2 =
    (92617567826953/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1001).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1001).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1001).q*(generalMeanRows 1001).cutoff/2-2 = (3388/1643:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable326.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1001).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1001

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1001).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1001).criticalRate j.val*(generalMeanRows 1001).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1001).c*(generalMeanRows 1001).criticalPoint j.val)).2-
      (generalMeanRows 1001).J/2-(generalMeanRows 1001).error (generalMeanGrid j.val)+
      (generalMeanRows 1001).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1001).c)).2-
      (generalMeanRows 1001).J/2-(generalMeanRows 1001).error 4 := by
  have he : (generalMeanRows 1001).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1001) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1001)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1001

/-! Kernel-checked entropy margins for general spectral rectangle 1002. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1002
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5490548737) (.branch 2 (.leaf 5314990377) (.leaf 5146786312))) (.branch 5 (.branch 4 (.leaf 4985533395) (.leaf 4830856635)) (.branch 6 (.leaf 4682406731) (.leaf 4539857867)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4402905747) (.leaf 4271265826)) (.branch 10 (.leaf 4144671731) (.leaf 4022873820))) (.branch 13 (.branch 12 (.leaf 3905637901) (.leaf 3792744053)) (.branch 14 (.leaf 3683985569) (.leaf 3579167985))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3478108203) (.branch 17 (.leaf 3380633683) (.leaf 3286581713))) (.branch 20 (.branch 19 (.leaf 3195798726) (.leaf 3108139688)) (.branch 21 (.leaf 3023467529) (.leaf 2941652612)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2862572261) (.leaf 2786110305)) (.branch 25 (.leaf 2712156672) (.leaf 2640607008))) (.branch 28 (.branch 27 (.leaf 2571362319) (.leaf 2504328648)) (.branch 29 (.leaf 2439416770) (.leaf 2376541906)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2315623464) (.branch 32 (.leaf 2256584792) (.leaf 2199352950))) (.branch 35 (.branch 34 (.leaf 2143858498) (.leaf 2090035294)) (.branch 36 (.leaf 2037820314) (.leaf 1987153472)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1937977461) (.leaf 1890237601)) (.branch 40 (.leaf 1843881694) (.leaf 1798859893))) (.branch 43 (.branch 42 (.leaf 1755124575) (.leaf 1712630225)) (.branch 44 (.leaf 1671333321) (.leaf 1631192235))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1592167133) (.branch 47 (.leaf 1554219883) (.leaf 1517313970))) (.branch 50 (.branch 49 (.leaf 1481414412) (.leaf 1446487683)) (.branch 51 (.leaf 1412501645) (.leaf 1379425473)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1347229597) (.leaf 1315885638)) (.branch 55 (.leaf 1285366348) (.leaf 1255645561))) (.branch 58 (.branch 57 (.leaf 1226698139) (.leaf 1198499922)) (.branch 59 (.leaf 1171027686) (.leaf 1144259095))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1118172664) (.branch 62 (.leaf 1092747717) (.leaf 1067964352))) (.branch 65 (.branch 64 (.leaf 1043803404) (.leaf 1020246415)) (.branch 66 (.leaf 997275601) (.leaf 974873821)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 953024548) (.leaf 931711849)) (.branch 70 (.leaf 910920348) (.leaf 890635214))) (.branch 73 (.branch 72 (.leaf 870842128) (.leaf 851527268)) (.branch 74 (.leaf 832677284) (.leaf 814279279))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 796320794) (.branch 77 (.leaf 778789784) (.leaf 761674606))) (.branch 80 (.branch 79 (.leaf 744963999) (.leaf 728647072)) (.branch 81 (.leaf 712713286) (.leaf 697152443)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 681954671) (.leaf 667110410)) (.branch 85 (.leaf 652610403) (.leaf 638445682))) (.branch 88 (.branch 87 (.leaf 624607557) (.leaf 611087608)) (.branch 89 (.leaf 597877669) (.leaf 584969827)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 572356405) (.branch 92 (.leaf 560029956) (.leaf 547983257))) (.branch 95 (.branch 94 (.leaf 536209297) (.leaf 524701272)) (.branch 96 (.leaf 513452575) (.leaf 502456793)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 491707696) (.leaf 481199232)) (.branch 100 (.leaf 470925524) (.leaf 460880859))) (.branch 103 (.branch 102 (.leaf 451059683) (.leaf 441456601)) (.branch 104 (.leaf 432066366) (.leaf 422883874))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 413904163) (.leaf 405122407)) (.branch 108 (.leaf 396533909) (.leaf 388134100))) (.branch 111 (.branch 110 (.leaf 379918534) (.leaf 371882881)) (.branch 112 (.leaf 364022928) (.leaf 356334574)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 348813824) (.leaf 341456789)) (.branch 116 (.leaf 334259678) (.leaf 327218801))) (.branch 119 (.branch 118 (.leaf 320330563) (.leaf 313591459)) (.branch 120 (.leaf 306998076) (.leaf 300547084)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1002).prefactor = (1212102989455877/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1002).cutoff/(generalMeanRows 1002).c)).2 =
    (91040275528637/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1002).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1002).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1002).q*(generalMeanRows 1002).cutoff/2-2 = (3388/1643:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable326.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1002).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1002

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1002).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1002).criticalRate j.val*(generalMeanRows 1002).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1002).c*(generalMeanRows 1002).criticalPoint j.val)).2-
      (generalMeanRows 1002).J/2-(generalMeanRows 1002).error (generalMeanGrid j.val)+
      (generalMeanRows 1002).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1002).c)).2-
      (generalMeanRows 1002).J/2-(generalMeanRows 1002).error 4 := by
  have he : (generalMeanRows 1002).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1002) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1002)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1002

/-! Kernel-checked entropy margins for general spectral rectangle 1003. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1003
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5498236656) (.branch 2 (.leaf 5317974253) (.leaf 5145327330))) (.branch 5 (.branch 4 (.leaf 4979878841) (.leaf 4821240800)) (.branch 6 (.leaf 4669051736) (.leaf 4522974422)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4382693846) (.leaf 4247915394)) (.branch 10 (.leaf 4118363209) (.leaf 3993778721))) (.branch 13 (.branch 12 (.leaf 3873919314) (.leaf 3758557115)) (.branch 14 (.leaf 3647477903) (.leaf 3540480110))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3437373913) (.branch 17 (.leaf 3337980404) (.leaf 3242130830))) (.branch 20 (.branch 19 (.leaf 3149665901) (.leaf 3060435146)) (.branch 21 (.leaf 2974296332) (.leaf 2891114919)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2810763562) (.leaf 2733121656)) (.branch 25 (.leaf 2658074905) (.leaf 2585514930))) (.branch 28 (.branch 27 (.leaf 2515338906) (.leaf 2447449224)) (.branch 29 (.leaf 2381753175) (.leaf 2318162658)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2256593910) (.branch 32 (.leaf 2196967253) (.leaf 2139206856))) (.branch 35 (.branch 34 (.leaf 2083240517) (.leaf 2028999458)) (.branch 36 (.leaf 1976418131) (.leaf 1925434039)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1875987571) (.leaf 1828021840)) (.branch 40 (.leaf 1781482539) (.leaf 1736317801))) (.branch 43 (.branch 42 (.leaf 1692478069) (.leaf 1649915977)) (.branch 44 (.leaf 1608586233) (.leaf 1568445510))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1529452348) (.branch 47 (.leaf 1491567060) (.leaf 1454751636))) (.branch 50 (.branch 49 (.leaf 1418969665) (.leaf 1384186251)) (.branch 51 (.leaf 1350367941) (.leaf 1317482653)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1285499610) (.leaf 1254389273)) (.branch 55 (.leaf 1224123287) (.leaf 1194674422))) (.branch 58 (.branch 57 (.leaf 1166016520) (.leaf 1138124443)) (.branch 59 (.leaf 1110974028) (.leaf 1084542041))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1058806134) (.branch 62 (.leaf 1033744804) (.leaf 1009337355))) (.branch 65 (.branch 64 (.leaf 985563864) (.leaf 962405142)) (.branch 66 (.leaf 939842706) (.leaf 917858744)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 896436090) (.leaf 875558190)) (.branch 70 (.leaf 855209082) (.leaf 835373366))) (.branch 73 (.branch 72 (.leaf 816036181) (.leaf 797183187)) (.branch 74 (.leaf 778800534) (.leaf 760874850))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 743393217) (.branch 77 (.leaf 726343154) (.leaf 709712598))) (.branch 80 (.branch 79 (.leaf 693489888) (.leaf 677663748)) (.branch 81 (.leaf 662223272) (.leaf 647157911)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 632457456) (.leaf 618112027)) (.branch 85 (.leaf 604112059) (.leaf 590448289))) (.branch 88 (.branch 87 (.leaf 577111749) (.leaf 564093749)) (.branch 89 (.leaf 551385870) (.leaf 538979952)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 526868086) (.branch 92 (.leaf 515042605) (.leaf 503496072))) (.branch 95 (.branch 94 (.leaf 492221276) (.leaf 481211220)) (.branch 96 (.leaf 470459116) (.leaf 459958375)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 449702605) (.leaf 439685596)) (.branch 100 (.leaf 429901321) (.leaf 420343927))) (.branch 103 (.branch 102 (.leaf 411007727) (.leaf 401887199)) (.branch 104 (.leaf 392976974) (.leaf 384271838))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 375766721) (.leaf 367456695)) (.branch 108 (.leaf 359336969) (.leaf 351402885))) (.branch 111 (.branch 110 (.leaf 343649912) (.leaf 336073642)) (.branch 112 (.leaf 328669790) (.leaf 321434183)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 314362763) (.leaf 307451580)) (.branch 116 (.leaf 300696791) (.leaf 294094651))) (.branch 119 (.branch 118 (.leaf 287641519) (.leaf 281333846)) (.branch 120 (.leaf 275168178) (.leaf 269141151)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1003).prefactor = (2501573675244919/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1003).cutoff/(generalMeanRows 1003).c)).2 =
    (87915234837579/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1003).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1003).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1003).q*(generalMeanRows 1003).c/2-2 = (3431/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable327.value]
    have hcontinuation : (generalMeanRows 1003).q*(generalMeanRows 1003).cutoff/2-2 = (3388/1643:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable326.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1003).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1003

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1003).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1003).criticalRate j.val*(generalMeanRows 1003).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1003).c*(generalMeanRows 1003).criticalPoint j.val)).2-
      (generalMeanRows 1003).J/2-(generalMeanRows 1003).error (generalMeanGrid j.val)+
      (generalMeanRows 1003).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1003).c)).2-
      (generalMeanRows 1003).J/2-(generalMeanRows 1003).error 4 := by
  have he : (generalMeanRows 1003).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1003) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1003)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1003

/-! Kernel-checked entropy margins for general spectral rectangle 1004. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1004
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5589652629) (.branch 2 (.leaf 5404141596) (.leaf 5226501928))) (.branch 5 (.branch 4 (.leaf 5056302709) (.leaf 4893143017)) (.branch 6 (.leaf 4736649296) (.leaf 4586473014)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4442288572) (.leaf 4303791425)) (.branch 10 (.leaf 4170696397) (.leaf 4042736155))) (.branch 13 (.branch 12 (.leaf 3919659840) (.leaf 3801231821)) (.branch 14 (.leaf 3687230558) (.leaf 3577447583))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3471686557) (.branch 17 (.leaf 3369762413) (.leaf 3271500579))) (.branch 20 (.branch 19 (.leaf 3176736253) (.leaf 3085313748)) (.branch 21 (.leaf 2997085887) (.leaf 2911913444)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2829664628) (.leaf 2750214612)) (.branch 25 (.leaf 2673445093) (.leaf 2599243882))) (.branch 28 (.branch 27 (.leaf 2527504533) (.leaf 2458125993)) (.branch 29 (.leaf 2391012275) (.leaf 2326072156)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2263218904) (.branch 32 (.leaf 2202370005) (.leaf 2143446932))) (.branch 35 (.branch 34 (.leaf 2086374908) (.leaf 2031082699)) (.branch 36 (.leaf 1977502414) (.leaf 1925569320)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1875221669) (.leaf 1826400534)) (.branch 40 (.leaf 1779049660) (.leaf 1733115316))) (.branch 43 (.branch 42 (.leaf 1688546164) (.leaf 1645293136)) (.branch 44 (.leaf 1603309308) (.leaf 1562549797))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1522971651) (.branch 47 (.leaf 1484533752) (.leaf 1447196726))) (.branch 50 (.branch 49 (.leaf 1410922850) (.leaf 1375675977)) (.branch 51 (.leaf 1341421450) (.leaf 1308126036)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1275757854) (.leaf 1244286308)) (.branch 55 (.leaf 1213682029) (.leaf 1183916814))) (.branch 58 (.branch 57 (.leaf 1154963570) (.leaf 1126796268)) (.branch 59 (.leaf 1099389885) (.leaf 1072720362))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1046764562) (.branch 62 (.leaf 1021500224) (.leaf 996905924))) (.branch 65 (.branch 64 (.leaf 972961038) (.leaf 949645709)) (.branch 66 (.leaf 926940807) (.leaf 904827904)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 883289236) (.leaf 862307683)) (.branch 70 (.leaf 841866731) (.leaf 821950456))) (.branch 73 (.branch 72 (.leaf 802543492) (.leaf 783631010)) (.branch 74 (.leaf 765198695) (.leaf 747232728))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 729719758) (.branch 77 (.leaf 712646891) (.leaf 696001666))) (.branch 80 (.branch 79 (.leaf 679772040) (.leaf 663946369)) (.branch 81 (.leaf 648513395) (.leaf 633462229)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 618782337) (.leaf 604463525)) (.branch 85 (.leaf 590495927) (.leaf 576869992))) (.branch 88 (.branch 87 (.leaf 563576473) (.leaf 550606413)) (.branch 89 (.leaf 537951136) (.leaf 525602237)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 513551570) (.branch 92 (.leaf 501791239) (.leaf 490313590))) (.branch 95 (.branch 94 (.leaf 479111201) (.leaf 468176875)) (.branch 96 (.leaf 457503628) (.leaf 447084687)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 436913479) (.leaf 426983626)) (.branch 100 (.leaf 417288934) (.leaf 407823392))) (.branch 103 (.branch 102 (.leaf 398581163) (.leaf 389556577)) (.branch 104 (.leaf 380744128) (.leaf 372138466))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 363734393) (.leaf 355526859)) (.branch 108 (.leaf 347510953) (.leaf 339681905))) (.branch 111 (.branch 110 (.leaf 332035074) (.leaf 324565950)) (.branch 112 (.leaf 317270146) (.leaf 310143395)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 303181547) (.leaf 296380566)) (.branch 116 (.leaf 289736522) (.leaf 283245593))) (.branch 119 (.branch 118 (.leaf 276904058) (.leaf 270708298)) (.branch 120 (.leaf 264654788) (.leaf 258740096)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1004).prefactor = (5162821069757109/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1004).cutoff/(generalMeanRows 1004).c)).2 =
    (69093793820479/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1004).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1004).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1004).q*(generalMeanRows 1004).c/2-2 = (1751/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable267.value]
    have hcontinuation : (generalMeanRows 1004).q*(generalMeanRows 1004).cutoff/2-2 = (3388/1643:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable326.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1004).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1004

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1004).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1004).criticalRate j.val*(generalMeanRows 1004).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1004).c*(generalMeanRows 1004).criticalPoint j.val)).2-
      (generalMeanRows 1004).J/2-(generalMeanRows 1004).error (generalMeanGrid j.val)+
      (generalMeanRows 1004).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1004).c)).2-
      (generalMeanRows 1004).J/2-(generalMeanRows 1004).error 4 := by
  have he : (generalMeanRows 1004).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1004) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1004)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1004

/-! Kernel-checked entropy margins for general spectral rectangle 1005. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1005
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5768044462) (.branch 2 (.leaf 5576612908) (.leaf 5393303931))) (.branch 5 (.branch 4 (.leaf 5217672863) (.leaf 5049305986)) (.branch 6 (.leaf 4887817822) (.leaf 4732848716)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4584062677) (.leaf 4441145442)) (.branch 10 (.leaf 4303802731) (.leaf 4171758682))) (.branch 13 (.branch 12 (.leaf 4044754430) (.leaf 3922546821)) (.branch 14 (.leaf 3804907248) (.leaf 3691620587))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3582484234) (.branch 17 (.leaf 3477307217) (.leaf 3375909390))) (.branch 20 (.branch 19 (.leaf 3278120693) (.leaf 3183780470)) (.branch 21 (.leaf 3092736848) (.leaf 3004846156)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2919972397) (.leaf 2837986762)) (.branch 25 (.leaf 2758767169) (.leaf 2682197852))) (.branch 28 (.branch 27 (.leaf 2608168967) (.leaf 2536576235)) (.branch 29 (.leaf 2467320605) (.leaf 2400307946)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2335448753) (.branch 32 (.leaf 2272657883) (.leaf 2211854301))) (.branch 35 (.branch 34 (.leaf 2152960843) (.leaf 2095904002)) (.branch 36 (.leaf 2040613720) (.leaf 1987023199)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1935068720) (.leaf 1884689476)) (.branch 40 (.leaf 1835827415) (.leaf 1788427092))) (.branch 43 (.branch 42 (.leaf 1742435532) (.leaf 1697802098)) (.branch 44 (.leaf 1654478371) (.leaf 1612418034))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1571576765) (.branch 47 (.leaf 1531912134) (.leaf 1493383509))) (.branch 50 (.branch 49 (.leaf 1455951966) (.leaf 1419580200)) (.branch 51 (.leaf 1384232452) (.leaf 1349874427)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1316473225) (.leaf 1283997276)) (.branch 55 (.leaf 1252416272) (.leaf 1221701110))) (.branch 58 (.branch 57 (.leaf 1191823834) (.leaf 1162757582)) (.branch 59 (.leaf 1134476533) (.leaf 1106955862))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1080171692) (.branch 62 (.leaf 1054101051) (.leaf 1028721832))) (.branch 65 (.branch 64 (.leaf 1004012754) (.leaf 979953324)) (.branch 66 (.leaf 956523803) (.leaf 933705173)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 911479107) (.leaf 889827934)) (.branch 70 (.leaf 868734617) (.leaf 848182721))) (.branch 73 (.branch 72 (.leaf 828156390) (.leaf 808640322)) (.branch 74 (.leaf 789619747) (.leaf 771080402))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 753008512) (.branch 77 (.leaf 735390770) (.leaf 718214319))) (.branch 80 (.branch 79 (.leaf 701466729) (.leaf 685135988)) (.branch 81 (.leaf 669210476) (.leaf 653678957)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 638530562) (.leaf 623754770)) (.branch 85 (.leaf 609341400) (.leaf 595280599))) (.branch 88 (.branch 87 (.leaf 581562821) (.leaf 568178826)) (.branch 89 (.leaf 555119661) (.leaf 542376651)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 529941391) (.branch 92 (.leaf 517805733) (.leaf 505961779))) (.branch 95 (.branch 94 (.leaf 494401870) (.leaf 483118578)) (.branch 96 (.leaf 472104698) (.leaf 461353240)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 450857422) (.leaf 440610661)) (.branch 100 (.leaf 430606566) (.leaf 420838935))) (.branch 103 (.branch 102 (.leaf 411301743) (.leaf 401989141)) (.branch 104 (.leaf 392895445) (.leaf 384015137))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 375342851) (.leaf 366873376)) (.branch 108 (.leaf 358601645) (.leaf 350522735))) (.branch 111 (.branch 110 (.leaf 342631859) (.leaf 334924360)) (.branch 112 (.leaf 327395713) (.leaf 320041514)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 312857482) (.leaf 305839449)) (.branch 116 (.leaf 298983363) (.leaf 292285278))) (.branch 119 (.branch 118 (.leaf 285741356) (.leaf 279347860)) (.branch 120 (.leaf 273101154) (.leaf 266997696)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1005).prefactor = (1065518144122549/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1005).cutoff/(generalMeanRows 1005).c)).2 =
    (69093793820479/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1005).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1005).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1005).q*(generalMeanRows 1005).c/2-2 = (1751/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable267.value]
    have hcontinuation : (generalMeanRows 1005).q*(generalMeanRows 1005).cutoff/2-2 = (3388/1643:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable326.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1005).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1005

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1005).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1005).criticalRate j.val*(generalMeanRows 1005).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1005).c*(generalMeanRows 1005).criticalPoint j.val)).2-
      (generalMeanRows 1005).J/2-(generalMeanRows 1005).error (generalMeanGrid j.val)+
      (generalMeanRows 1005).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1005).c)).2-
      (generalMeanRows 1005).J/2-(generalMeanRows 1005).error 4 := by
  have he : (generalMeanRows 1005).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1005) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1005)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1005

/-! Kernel-checked entropy margins for general spectral rectangle 1006. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1006
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6041638962) (.branch 2 (.leaf 5843560846) (.leaf 5653850864))) (.branch 5 (.branch 4 (.leaf 5472050752) (.leaf 5297734180)) (.branch 6 (.leaf 5130503950) (.leaf 4969989507)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4815844707) (.leaf 4667745817)) (.branch 10 (.leaf 4525389717) (.leaf 4388492282))) (.branch 13 (.branch 12 (.leaf 4256786917) (.leaf 4130023228)) (.branch 14 (.leaf 4007965824) (.leaf 3890393214))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3777096815) (.branch 17 (.leaf 3667880036) (.leaf 3562557447))) (.branch 20 (.branch 19 (.leaf 3460954014) (.leaf 3362904396)) (.branch 21 (.leaf 3268252302) (.leaf 3176849894)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3088557244) (.leaf 3003241824)) (.branch 25 (.leaf 2920778044) (.leaf 2841046814))) (.branch 28 (.branch 27 (.leaf 2763935146) (.leaf 2689335784)) (.branch 29 (.leaf 2617146856) (.leaf 2547271555)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2479617838) (.branch 32 (.leaf 2414098152) (.leaf 2350629174))) (.branch 35 (.branch 34 (.leaf 2289131564) (.leaf 2229529747)) (.branch 36 (.leaf 2171751696) (.leaf 2115728740)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2061395373) (.leaf 2008689088)) (.branch 40 (.leaf 1957550210) (.leaf 1907921745))) (.branch 43 (.branch 42 (.leaf 1859749240) (.leaf 1812980647)) (.branch 44 (.leaf 1767566197) (.leaf 1723458282))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1680611344) (.branch 47 (.leaf 1638981773) (.leaf 1598527803))) (.branch 50 (.branch 49 (.leaf 1559209424) (.leaf 1520988292)) (.branch 51 (.leaf 1483827648) (.leaf 1447692238)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1412548243) (.leaf 1378363206)) (.branch 55 (.leaf 1345105969) (.leaf 1312746611))) (.branch 58 (.branch 57 (.leaf 1281256388) (.leaf 1250607678)) (.branch 59 (.leaf 1220773931) (.leaf 1191729615))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1163450174) (.branch 62 (.leaf 1135911979) (.leaf 1109092291))) (.branch 65 (.branch 64 (.leaf 1082969215) (.leaf 1057521668)) (.branch 66 (.leaf 1032729339) (.leaf 1008572657)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 985032756) (.leaf 962091450)) (.branch 70 (.leaf 939731196) (.leaf 917935074))) (.branch 73 (.branch 72 (.leaf 896686755) (.leaf 875970480)) (.branch 74 (.leaf 855771030) (.leaf 836073713))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 816864334) (.branch 77 (.leaf 798129177) (.leaf 779854988))) (.branch 80 (.branch 79 (.leaf 762028954) (.leaf 744638683)) (.branch 81 (.leaf 727672192) (.leaf 711117890)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 694964558) (.leaf 679201340)) (.branch 85 (.leaf 663817725) (.leaf 648803537))) (.branch 88 (.branch 87 (.leaf 634148919) (.leaf 619844322)) (.branch 89 (.leaf 605880497) (.leaf 592248476)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 578939569) (.branch 92 (.leaf 565945350) (.leaf 553257649))) (.branch 95 (.branch 94 (.leaf 540868541) (.leaf 528770338)) (.branch 96 (.leaf 516955581) (.leaf 505417030)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 494147660) (.leaf 483140649)) (.branch 100 (.leaf 472389374) (.leaf 461887402))) (.branch 103 (.branch 102 (.leaf 451628486) (.leaf 441606557)) (.branch 104 (.leaf 431815716) (.leaf 422250233))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 412904537) (.leaf 403773214)) (.branch 108 (.leaf 394850998) (.leaf 386132772))) (.branch 111 (.branch 110 (.leaf 377613556) (.leaf 369288508)) (.branch 112 (.leaf 361152917) (.leaf 353202200)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 345431897) (.leaf 337837668)) (.branch 116 (.leaf 330415288) (.leaf 323160645))) (.branch 119 (.branch 118 (.leaf 316069736) (.leaf 309138663)) (.branch 120 (.leaf 302363629) (.leaf 295740938)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1006).prefactor = (1374404734488229/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1006).cutoff/(generalMeanRows 1006).c)).2 =
    (87915234837579/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1006).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1006).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1006).q*(generalMeanRows 1006).c/2-2 = (3431/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable327.value]
    have hcontinuation : (generalMeanRows 1006).q*(generalMeanRows 1006).cutoff/2-2 = (3388/1643:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable326.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1006).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1006

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1006).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1006).criticalRate j.val*(generalMeanRows 1006).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1006).c*(generalMeanRows 1006).criticalPoint j.val)).2-
      (generalMeanRows 1006).J/2-(generalMeanRows 1006).error (generalMeanGrid j.val)+
      (generalMeanRows 1006).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1006).c)).2-
      (generalMeanRows 1006).J/2-(generalMeanRows 1006).error 4 := by
  have he : (generalMeanRows 1006).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1006) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1006)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1006

/-! Kernel-checked entropy margins for general spectral rectangle 1007. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1007
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6518435782) (.branch 2 (.leaf 6315340874) (.leaf 6120685225))) (.branch 5 (.branch 4 (.leaf 5934005536) (.leaf 5754870942)) (.branch 6 (.leaf 5582880170) (.leaf 5417658994)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5258857974) (.leaf 5106150411)) (.branch 10 (.leaf 4959230527) (.leaf 4817811812))) (.branch 13 (.branch 12 (.leaf 4681625531) (.leaf 4550419381)) (.branch 14 (.leaf 4423956263) (.leaf 4302013165))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4184380152) (.branch 17 (.leaf 4070859436) (.leaf 3961264527))) (.branch 20 (.branch 19 (.leaf 3855419456) (.leaf 3753158065)) (.branch 21 (.leaf 3654323345) (.leaf 3558766841)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3466348087) (.leaf 3376934098)) (.branch 25 (.leaf 3290398892) (.leaf 3206623054))) (.branch 28 (.branch 27 (.leaf 3125493328) (.leaf 3046902235)) (.branch 29 (.leaf 2970747732) (.leaf 2896932877)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2825365533) (.branch 32 (.leaf 2755958080) (.leaf 2688627158))) (.branch 35 (.branch 34 (.leaf 2623293419) (.leaf 2559881296)) (.branch 36 (.leaf 2498318794) (.leaf 2438537286)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2380471330) (.leaf 2324058488)) (.branch 40 (.leaf 2269239169) (.leaf 2215956470))) (.branch 43 (.branch 42 (.leaf 2164156035) (.leaf 2113785916)) (.branch 44 (.leaf 2064796449) (.leaf 2017140136))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1970771527) (.branch 47 (.leaf 1925647118) (.leaf 1881725255))) (.branch 50 (.branch 49 (.leaf 1838966031) (.leaf 1797331206)) (.branch 51 (.leaf 1756784123) (.leaf 1717289625)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1678813984) (.leaf 1641324832)) (.branch 55 (.leaf 1604791094) (.leaf 1569182925))) (.branch 58 (.branch 57 (.leaf 1534471653) (.leaf 1500629722)) (.branch 59 (.leaf 1467630640) (.leaf 1435448928))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1404060075) (.branch 62 (.leaf 1373440491) (.leaf 1343567469))) (.branch 65 (.branch 64 (.leaf 1314419140) (.leaf 1285974438)) (.branch 66 (.leaf 1258213062) (.leaf 1231115445)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1204662720) (.leaf 1178836687)) (.branch 70 (.leaf 1153619790) (.leaf 1128995082))) (.branch 73 (.branch 72 (.leaf 1104946204) (.leaf 1081457357)) (.branch 74 (.leaf 1058513282) (.leaf 1036099234))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1014200959) (.branch 77 (.leaf 992804680) (.leaf 971897071))) (.branch 80 (.branch 79 (.leaf 951465244) (.leaf 931496726)) (.branch 81 (.leaf 911979448) (.leaf 892901722)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 874252233) (.leaf 856020020)) (.branch 85 (.leaf 838194464) (.leaf 820765274))) (.branch 88 (.branch 87 (.leaf 803722475) (.leaf 787056395)) (.branch 89 (.leaf 770757655) (.leaf 754817156)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 739226070) (.branch 92 (.leaf 723975833) (.leaf 709058127))) (.branch 95 (.branch 94 (.leaf 694464881) (.leaf 680188254)) (.branch 96 (.leaf 666220631) (.leaf 652554615)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 639183017) (.leaf 626098852)) (.branch 100 (.leaf 613295327) (.leaf 600765841))) (.branch 103 (.branch 102 (.leaf 588503973) (.leaf 576503477)) (.branch 104 (.leaf 564758278) (.leaf 553262465))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 542010286) (.leaf 530996141)) (.branch 108 (.leaf 520214581) (.leaf 509660299))) (.branch 111 (.branch 110 (.leaf 499328127) (.leaf 489213032)) (.branch 112 (.leaf 479310112) (.leaf 469614590)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 460121812) (.leaf 450827244)) (.branch 116 (.leaf 441726463) (.leaf 432815162))) (.branch 119 (.branch 118 (.leaf 424089139) (.leaf 415544297)) (.branch 120 (.leaf 407176642) (.leaf 398982278)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1007).prefactor = (139616431180649/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1007).cutoff/(generalMeanRows 1007).c)).2 =
    (37681949898647/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1007).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1007).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1007).q*(generalMeanRows 1007).c/2-2 = (3147/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable328.value]
    have hcontinuation : (generalMeanRows 1007).q*(generalMeanRows 1007).cutoff/2-2 = (3388/1643:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable326.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1007).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1007

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1007).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1007).criticalRate j.val*(generalMeanRows 1007).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1007).c*(generalMeanRows 1007).criticalPoint j.val)).2-
      (generalMeanRows 1007).J/2-(generalMeanRows 1007).error (generalMeanGrid j.val)+
      (generalMeanRows 1007).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1007).c)).2-
      (generalMeanRows 1007).J/2-(generalMeanRows 1007).error 4 := by
  have he : (generalMeanRows 1007).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1007) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1007)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1007

/-! Kernel-checked entropy margins for general spectral rectangle 1008. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1008
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7432281980) (.branch 2 (.leaf 7224949421) (.leaf 7025531600))) (.branch 5 (.branch 4 (.leaf 6833620465) (.leaf 6648835952)) (.branch 6 (.leaf 6470823470) (.leaf 6299251672)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6133810470) (.leaf 5974209269)) (.branch 10 (.leaf 5820175379) (.leaf 5671452598))) (.branch 13 (.branch 12 (.leaf 5527799926) (.leaf 5388990417)) (.branch 14 (.leaf 5254810131) (.leaf 5125057185))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4999540899) (.branch 17 (.leaf 4878081003) (.leaf 4760506930))) (.branch 20 (.branch 19 (.leaf 4646657158) (.leaf 4536378609)) (.branch 21 (.leaf 4429526105) (.leaf 4325961854)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4225554994) (.leaf 4128181155)) (.branch 25 (.leaf 4033722068) (.leaf 3942065195))) (.branch 28 (.branch 27 (.leaf 3853103393) (.leaf 3766734594)) (.branch 29 (.leaf 3682861515) (.leaf 3601391385)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3522235694) (.branch 32 (.leaf 3445309952) (.leaf 3370533472))) (.branch 35 (.branch 34 (.leaf 3297829167) (.leaf 3227123348)) (.branch 36 (.leaf 3158345556) (.leaf 3091428383)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3026307321) (.leaf 2962920610)) (.branch 40 (.leaf 2901209097) (.leaf 2841116112))) (.branch 43 (.branch 42 (.leaf 2782587337) (.leaf 2725570693)) (.branch 44 (.leaf 2670016233) (.leaf 2615876034))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2563104105) (.branch 47 (.leaf 2511656293) (.leaf 2461490194))) (.branch 50 (.branch 49 (.leaf 2412565076) (.leaf 2364841799)) (.branch 51 (.leaf 2318282740) (.leaf 2272851726)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2228513970) (.leaf 2185236003)) (.branch 55 (.leaf 2142985622) (.leaf 2101731829))) (.branch 58 (.branch 57 (.leaf 2061444779) (.leaf 2022095731)) (.branch 59 (.leaf 1983656999) (.leaf 1946101907))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1909404745) (.branch 62 (.leaf 1873540728) (.leaf 1838485958))) (.branch 65 (.branch 64 (.leaf 1804217386) (.leaf 1770712775)) (.branch 66 (.leaf 1737950669) (.leaf 1705910358)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1674571852) (.leaf 1643915846)) (.branch 70 (.leaf 1613923695) (.leaf 1584577386))) (.branch 73 (.branch 72 (.leaf 1555859518) (.leaf 1527753268)) (.branch 74 (.leaf 1500242378) (.leaf 1473311126))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1446944308) (.branch 77 (.leaf 1421127216) (.leaf 1395845622))) (.branch 80 (.branch 79 (.leaf 1371085754) (.leaf 1346834286)) (.branch 81 (.leaf 1323078313) (.leaf 1299805341)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1277003270) (.leaf 1254660376)) (.branch 85 (.leaf 1232765302) (.leaf 1211307041))) (.branch 88 (.branch 87 (.leaf 1190274923) (.leaf 1169658605)) (.branch 89 (.leaf 1149448058) (.leaf 1129633553)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1110205654) (.branch 92 (.leaf 1091155207) (.leaf 1072473325))) (.branch 95 (.branch 94 (.leaf 1054151386) (.leaf 1036181018)) (.branch 96 (.leaf 1018554092) (.leaf 1001262713)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 984299215) (.leaf 967656147)) (.branch 100 (.leaf 951326270) (.leaf 935302550))) (.branch 103 (.branch 102 (.leaf 919578149) (.leaf 904146418)) (.branch 104 (.leaf 889000892) (.leaf 874135284))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 859543479) (.leaf 845219526)) (.branch 108 (.leaf 831157636) (.leaf 817352173))) (.branch 111 (.branch 110 (.leaf 803797653) (.leaf 790488737)) (.branch 112 (.leaf 777420225) (.leaf 764587053)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 751984289) (.leaf 739607129)) (.branch 116 (.leaf 727450890) (.leaf 715511012))) (.branch 119 (.branch 118 (.leaf 703783046) (.leaf 692262658)) (.branch 120 (.leaf 680945623) (.leaf 669827820)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1008).prefactor = (1002043591626283/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1008).cutoff/(generalMeanRows 1008).c)).2 =
    (78233604032619/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1008).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1008).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1008).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1008

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1008).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1008).criticalRate j.val*(generalMeanRows 1008).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1008).c*(generalMeanRows 1008).criticalPoint j.val)).2-
      (generalMeanRows 1008).J/2-(generalMeanRows 1008).error (generalMeanGrid j.val)+
      (generalMeanRows 1008).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1008).c)).2-
      (generalMeanRows 1008).J/2-(generalMeanRows 1008).error 4 := by
  have he : (generalMeanRows 1008).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1008) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1008)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1008

/-! Kernel-checked entropy margins for general spectral rectangle 1009. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1009
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7171948488) (.branch 2 (.leaf 6968466646) (.leaf 6772834218))) (.branch 5 (.branch 4 (.leaf 6584644217) (.leaf 6403517575)) (.branch 6 (.leaf 6229100644) (.leaf 6061062974)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5899095351) (.leaf 5742908025)) (.branch 10 (.leaf 5592229142) (.leaf 5446803319))) (.branch 13 (.branch 12 (.leaf 5306390377) (.leaf 5170764183)) (.branch 14 (.leaf 5039711609) (.leaf 4913031588))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4790534254) (.branch 17 (.leaf 4672040158) (.leaf 4557379553))) (.branch 20 (.branch 19 (.leaf 4446391739) (.leaf 4338924467)) (.branch 21 (.leaf 4234833383) (.leaf 4133981527)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4036238866) (.leaf 3941481860)) (.branch 25 (.leaf 3849593070) (.leaf 3760460786))) (.branch 28 (.branch 27 (.leaf 3673978690) (.leaf 3590045538)) (.branch 29 (.leaf 3508564867) (.leaf 3429444719)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3352597396) (.branch 32 (.leaf 3277939210) (.leaf 3205390275))) (.branch 35 (.branch 34 (.leaf 3134874290) (.leaf 3066318353)) (.branch 36 (.leaf 2999652778) (.leaf 2934810924)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2871729039) (.leaf 2810346112)) (.branch 40 (.leaf 2750603728) (.leaf 2692445944))) (.branch 43 (.branch 42 (.leaf 2635819157) (.leaf 2580671997)) (.branch 44 (.leaf 2526955209) (.leaf 2474621557))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2423625720) (.branch 47 (.leaf 2373924205) (.leaf 2325475259))) (.branch 50 (.branch 49 (.leaf 2278238786) (.leaf 2232176269)) (.branch 51 (.leaf 2187250700) (.leaf 2143426506)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2100669489) (.leaf 2058946758)) (.branch 55 (.leaf 2018226672) (.leaf 1978478789))) (.branch 58 (.branch 57 (.leaf 1939673802) (.leaf 1901783502)) (.branch 59 (.leaf 1864780719) (.leaf 1828639282))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1793333976) (.branch 62 (.leaf 1758840499) (.leaf 1725135424))) (.branch 65 (.branch 64 (.leaf 1692196162) (.leaf 1660000926)) (.branch 66 (.leaf 1628528699) (.leaf 1597759198)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1567672851) (.leaf 1538250758)) (.branch 70 (.leaf 1509474672) (.leaf 1481326969))) (.branch 73 (.branch 72 (.leaf 1453790621) (.leaf 1426849175)) (.branch 74 (.leaf 1400486730) (.leaf 1374687912))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1349437858) (.branch 77 (.leaf 1324722189) (.leaf 1300526999))) (.branch 80 (.branch 79 (.leaf 1276838831) (.leaf 1253644661)) (.branch 81 (.leaf 1230931884) (.leaf 1208688294)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1186902071) (.leaf 1165561766)) (.branch 85 (.leaf 1144656287) (.leaf 1124174886))) (.branch 88 (.branch 87 (.leaf 1104107146) (.leaf 1084442968)) (.branch 89 (.leaf 1065172560) (.leaf 1046286427)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1027775358) (.branch 92 (.leaf 1009630417) (.leaf 991842932))) (.branch 95 (.branch 94 (.leaf 974404486) (.leaf 957306910)) (.branch 96 (.leaf 940542271) (.leaf 924102865)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 907981210) (.leaf 892170037)) (.branch 100 (.leaf 876662282) (.leaf 861451081))) (.branch 103 (.branch 102 (.leaf 846529762) (.leaf 831891837)) (.branch 104 (.leaf 817530999) (.leaf 803441114))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 789616214) (.leaf 776050493)) (.branch 108 (.leaf 762738303) (.leaf 749674145))) (.branch 111 (.branch 110 (.leaf 736852669) (.leaf 724268663)) (.branch 112 (.leaf 711917056) (.leaf 699792905)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 687891399) (.leaf 676207849)) (.branch 116 (.leaf 664737688) (.leaf 653476463))) (.branch 119 (.branch 118 (.leaf 642419835) (.leaf 631563576)) (.branch 120 (.leaf 620903561) (.leaf 610435769)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1009).prefactor = (2493056194342993/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1009).cutoff/(generalMeanRows 1009).c)).2 =
    (12698461493417/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1009).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1009).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1009).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1009

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1009).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1009).criticalRate j.val*(generalMeanRows 1009).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1009).c*(generalMeanRows 1009).criticalPoint j.val)).2-
      (generalMeanRows 1009).J/2-(generalMeanRows 1009).error (generalMeanGrid j.val)+
      (generalMeanRows 1009).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1009).c)).2-
      (generalMeanRows 1009).J/2-(generalMeanRows 1009).error 4 := by
  have he : (generalMeanRows 1009).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1009) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1009)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1009

/-! Kernel-checked entropy margins for general spectral rectangle 1010. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1010
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6965171118) (.branch 2 (.leaf 6765911617) (.leaf 6574406924))) (.branch 5 (.branch 4 (.leaf 6390252176) (.leaf 6213070315)) (.branch 6 (.leaf 6042509608) (.leaf 5878241450)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5719958402) (.leaf 5567372441)) (.branch 10 (.leaf 5420213389) (.leaf 5278227506))) (.branch 13 (.branch 12 (.leaf 5141176219) (.leaf 5008834971)) (.branch 14 (.leaf 4880992189) (.leaf 4757448333))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4638015046) (.branch 17 (.leaf 4522514366) (.leaf 4410778014))) (.branch 20 (.branch 19 (.leaf 4302646743) (.leaf 4197969735)) (.branch 21 (.leaf 4096604056) (.leaf 3998414143)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3903271345) (.leaf 3811053489)) (.branch 25 (.leaf 3721644482) (.leaf 3634933946))) (.branch 28 (.branch 27 (.leaf 3550816873) (.leaf 3469193316)) (.branch 29 (.leaf 3389968085) (.leaf 3313050482)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3238354046) (.branch 32 (.leaf 3165796309) (.leaf 3095298584))) (.branch 35 (.branch 34 (.leaf 3026785751) (.leaf 2960186067)) (.branch 36 (.leaf 2895430988) (.leaf 2832454992)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2771195428) (.leaf 2711592362)) (.branch 40 (.leaf 2653588440) (.leaf 2597128756))) (.branch 43 (.branch 42 (.leaf 2542160727) (.leaf 2488633979)) (.branch 44 (.leaf 2436500235) (.leaf 2385713214))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2336228534) (.branch 47 (.leaf 2288003616) (.leaf 2240997603))) (.branch 50 (.branch 49 (.leaf 2195171276) (.leaf 2150486974)) (.branch 51 (.leaf 2106908526) (.leaf 2064401178)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2022931527) (.leaf 1982467463)) (.branch 55 (.leaf 1942978107) (.leaf 1904433755))) (.branch 58 (.branch 57 (.leaf 1866805829) (.leaf 1830066821)) (.branch 59 (.leaf 1794190253) (.leaf 1759150622))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1724923369) (.branch 62 (.leaf 1691484827) (.leaf 1658812190))) (.branch 65 (.branch 64 (.leaf 1626883473) (.leaf 1595677478)) (.branch 66 (.leaf 1565173758) (.leaf 1535352590)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1506194941) (.leaf 1477682441)) (.branch 70 (.leaf 1449797355) (.leaf 1422522558))) (.branch 73 (.branch 72 (.leaf 1395841507) (.leaf 1369738221)) (.branch 74 (.leaf 1344197256) (.leaf 1319203686))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1294743077) (.branch 77 (.leaf 1270801474) (.leaf 1247365379))) (.branch 80 (.branch 79 (.leaf 1224421731) (.leaf 1201957892)) (.branch 81 (.leaf 1179961632) (.leaf 1158421106)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1137324850) (.leaf 1116661755)) (.branch 85 (.leaf 1096421064) (.leaf 1076592350))) (.branch 88 (.branch 87 (.leaf 1057165509) (.leaf 1038130747)) (.branch 89 (.leaf 1019478568) (.leaf 1001199761)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 983285393) (.branch 92 (.leaf 965726798) (.leaf 948515565))) (.branch 95 (.branch 94 (.leaf 931643532) (.leaf 915102773)) (.branch 96 (.leaf 898885595) (.leaf 882984526)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 867392307) (.leaf 852101887)) (.branch 100 (.leaf 837106413) (.leaf 822399225))) (.branch 103 (.branch 102 (.leaf 807973849) (.leaf 793823992)) (.branch 104 (.leaf 779943530) (.leaf 766326512))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 752967144) (.leaf 739859792)) (.branch 108 (.leaf 726998971) (.leaf 714379343))) (.branch 111 (.branch 110 (.leaf 701995712) (.leaf 689843018)) (.branch 112 (.leaf 677916334) (.leaf 666210859)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 654721920) (.leaf 643444961)) (.branch 116 (.leaf 632375542) (.leaf 621509337))) (.branch 119 (.branch 118 (.leaf 610842129) (.leaf 600369805)) (.branch 120 (.leaf 590088357) (.leaf 579993873)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1010).prefactor = (495185347257101/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1010).cutoff/(generalMeanRows 1010).c)).2 =
    (81694209022561/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1010).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1010).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1010).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1010

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1010).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1010).criticalRate j.val*(generalMeanRows 1010).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1010).c*(generalMeanRows 1010).criticalPoint j.val)).2-
      (generalMeanRows 1010).J/2-(generalMeanRows 1010).error (generalMeanGrid j.val)+
      (generalMeanRows 1010).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1010).c)).2-
      (generalMeanRows 1010).J/2-(generalMeanRows 1010).error 4 := by
  have he : (generalMeanRows 1010).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1010) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1010)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1010

/-! Kernel-checked entropy margins for general spectral rectangle 1011. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1011
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6657735518) (.branch 2 (.leaf 6463286615) (.leaf 6276493822))) (.branch 5 (.branch 4 (.leaf 6096954928) (.leaf 5924295370)) (.branch 6 (.leaf 5758165774) (.leaf 5598239780)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5444212092) (.leaf 5295796744)) (.branch 10 (.leaf 5152725540) (.leaf 5014746654))) (.branch 13 (.branch 12 (.leaf 4881623367) (.leaf 4753132924)) (.branch 14 (.leaf 4629065503) (.leaf 4509223274))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4393419547) (.branch 17 (.leaf 4281477988) (.leaf 4173231912))) (.branch 20 (.branch 19 (.leaf 4068523633) (.leaf 3967203859)) (.branch 21 (.leaf 3869131151) (.leaf 3774171414)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3682197432) (.leaf 3593088442)) (.branch 25 (.leaf 3506729731) (.leaf 3423012274))) (.branch 28 (.branch 27 (.leaf 3341832390) (.leaf 3263091429)) (.branch 29 (.leaf 3186695477) (.leaf 3112555084)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3040585006) (.branch 32 (.leaf 2970703974) (.leaf 2902834471))) (.branch 35 (.branch 34 (.leaf 2836902523) (.leaf 2772837507)) (.branch 36 (.leaf 2710571973) (.leaf 2650041473)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2591184403) (.leaf 2533941851)) (.branch 40 (.leaf 2478257464) (.leaf 2424077312))) (.branch 43 (.branch 42 (.leaf 2371349764) (.leaf 2320025377)) (.branch 44 (.leaf 2270056782) (.leaf 2221398584))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2174007261) (.branch 47 (.leaf 2127841081) (.leaf 2082860004))) (.branch 50 (.branch 49 (.leaf 2039025612) (.leaf 1996301024)) (.branch 51 (.leaf 1954650827) (.leaf 1914041004)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1874438875) (.leaf 1835813029)) (.branch 55 (.leaf 1798133267) (.leaf 1761370551))) (.branch 58 (.branch 57 (.leaf 1725496947) (.leaf 1690485574)) (.branch 59 (.leaf 1656310564) (.leaf 1622947010))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1590370927) (.branch 62 (.leaf 1558559210) (.leaf 1527489599))) (.branch 65 (.branch 64 (.leaf 1497140637) (.leaf 1467491642)) (.branch 66 (.leaf 1438522666) (.leaf 1410214473)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1382548502) (.leaf 1355506840)) (.branch 70 (.leaf 1329072198) (.leaf 1303227883))) (.branch 73 (.branch 72 (.leaf 1277957772) (.leaf 1253246291)) (.branch 74 (.leaf 1229078393) (.leaf 1205439535))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1182315657) (.branch 77 (.leaf 1159693167) (.leaf 1137558916))) (.branch 80 (.branch 79 (.leaf 1115900186) (.leaf 1094704672)) (.branch 81 (.leaf 1073960462) (.leaf 1053656028)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1033780205) (.leaf 1014322182)) (.branch 85 (.leaf 995271486) (.leaf 976617968))) (.branch 88 (.branch 87 (.leaf 958351795) (.leaf 940463433)) (.branch 89 (.leaf 922943641) (.leaf 905783456)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 888974184) (.branch 92 (.leaf 872507392) (.leaf 856374897))) (.branch 95 (.branch 94 (.leaf 840568755) (.leaf 825081255)) (.branch 96 (.leaf 809904913) (.leaf 795032457)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 780456827) (.leaf 766171160)) (.branch 100 (.leaf 752168792) (.leaf 738443242))) (.branch 103 (.branch 102 (.leaf 724988214) (.leaf 711797582)) (.branch 104 (.leaf 698865394) (.leaf 686185857))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 673753338) (.leaf 661562355)) (.branch 108 (.leaf 649607573) (.leaf 637883801))) (.branch 111 (.branch 110 (.leaf 626385985) (.leaf 615109204)) (.branch 112 (.leaf 604048665) (.leaf 593199702)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 582557768) (.leaf 572118434)) (.branch 116 (.leaf 561877382) (.leaf 551830407))) (.branch 119 (.branch 118 (.leaf 541973408) (.leaf 532302387)) (.branch 120 (.leaf 522813448) (.leaf 513502788)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1011).prefactor = (4908606852629231/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1011).cutoff/(generalMeanRows 1011).c)).2 =
    (82541921014613/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1011).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1011).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1011).q*(generalMeanRows 1011).cutoff/2-2 = (109/63:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable112.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1011).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1011

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1011).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1011).criticalRate j.val*(generalMeanRows 1011).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1011).c*(generalMeanRows 1011).criticalPoint j.val)).2-
      (generalMeanRows 1011).J/2-(generalMeanRows 1011).error (generalMeanGrid j.val)+
      (generalMeanRows 1011).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1011).c)).2-
      (generalMeanRows 1011).J/2-(generalMeanRows 1011).error 4 := by
  have he : (generalMeanRows 1011).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1011) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1011)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1011

/-! Kernel-checked entropy margins for general spectral rectangle 1012. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1012
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6456527597) (.branch 2 (.leaf 6266986464) (.leaf 6084969143))) (.branch 5 (.branch 4 (.leaf 5910077201) (.leaf 5741939668)) (.branch 6 (.leaf 5580210603) (.leaf 5424566933)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5274706529) (.leaf 5130346474)) (.branch 10 (.leaf 4991221525) (.leaf 4857082713))) (.branch 13 (.branch 12 (.leaf 4727696094) (.leaf 4602841614)) (.branch 14 (.leaf 4482312076) (.leaf 4365912209))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4253457819) (.branch 17 (.leaf 4144775009) (.leaf 4039699474))) (.branch 20 (.branch 19 (.leaf 3938075848) (.leaf 3839757115)) (.branch 21 (.leaf 3744604052) (.leaf 3652484736)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3563274073) (.leaf 3476853371)) (.branch 25 (.leaf 3393109948) (.leaf 3311936759))) (.branch 28 (.branch 27 (.leaf 3233232061) (.leaf 3156899097)) (.branch 29 (.leaf 3082845804) (.leaf 3010984537)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2941231821) (.branch 32 (.leaf 2873508109) (.leaf 2807737567))) (.branch 35 (.branch 34 (.leaf 2743847864) (.leaf 2681769982)) (.branch 36 (.leaf 2621438034) (.leaf 2562789098)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2505763057) (.leaf 2450302451)) (.branch 40 (.leaf 2396352341) (.leaf 2343860173))) (.branch 43 (.branch 42 (.leaf 2292775660) (.leaf 2243050665)) (.branch 44 (.leaf 2194639093) (.leaf 2147496787))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2101581433) (.branch 47 (.leaf 2056852470) (.leaf 2013271002))) (.branch 50 (.branch 49 (.leaf 1970799720) (.leaf 1929402822)) (.branch 51 (.leaf 1889045946) (.leaf 1849696097)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1811321584) (.leaf 1773891959)) (.branch 55 (.leaf 1737377962) (.leaf 1701751462))) (.branch 58 (.branch 57 (.leaf 1666985406) (.leaf 1633053773)) (.branch 59 (.leaf 1599931526) (.leaf 1567594564))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1536019687) (.branch 62 (.leaf 1505184550) (.leaf 1475067629))) (.branch 65 (.branch 64 (.leaf 1445648183) (.leaf 1416906223)) (.branch 66 (.leaf 1388822476) (.leaf 1361378355)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1334555931) (.leaf 1308337906)) (.branch 70 (.leaf 1282707583) (.leaf 1257648844))) (.branch 73 (.branch 72 (.leaf 1233146124) (.leaf 1209184389)) (.branch 74 (.leaf 1185749115) (.leaf 1162826265))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1140402270) (.branch 77 (.leaf 1118464013) (.leaf 1096998805))) (.branch 80 (.branch 79 (.leaf 1075994375) (.leaf 1055438846)) (.branch 81 (.leaf 1035320726) (.leaf 1015628889)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 996352563) (.leaf 977481315)) (.branch 85 (.leaf 959005037) (.leaf 940913935))) (.branch 88 (.branch 87 (.leaf 923198519) (.leaf 905849588)) (.branch 89 (.leaf 888858221) (.leaf 872215765)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 855913828) (.branch 92 (.leaf 839944267) (.leaf 824299180))) (.branch 95 (.branch 94 (.leaf 808970895) (.leaf 793951966)) (.branch 96 (.leaf 779235160) (.leaf 764813455)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 750680027) (.leaf 736828245)) (.branch 100 (.leaf 723251666) (.leaf 709944026))) (.branch 103 (.branch 102 (.leaf 696899237) (.leaf 684111376)) (.branch 104 (.leaf 671574684) (.leaf 659283559))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 647232549) (.leaf 635416349)) (.branch 108 (.leaf 623829796) (.leaf 612467863))) (.branch 111 (.branch 110 (.leaf 601325657) (.leaf 590398411)) (.branch 112 (.leaf 579681483) (.leaf 569170351)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 558860608) (.leaf 548747961)) (.branch 116 (.leaf 538828225) (.leaf 529097320))) (.branch 119 (.branch 118 (.leaf 519551270) (.leaf 510186195)) (.branch 120 (.leaf 500998314) (.leaf 491983938)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1012).prefactor = (607181431029591/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1012).cutoff/(generalMeanRows 1012).c)).2 =
    (170911882290033/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1012).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1012).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1012).q*(generalMeanRows 1012).c/2-2 = (2767/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable329.value]
    have hcontinuation : (generalMeanRows 1012).q*(generalMeanRows 1012).cutoff/2-2 = (821/459:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable330.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1012).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1012

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1012).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1012).criticalRate j.val*(generalMeanRows 1012).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1012).c*(generalMeanRows 1012).criticalPoint j.val)).2-
      (generalMeanRows 1012).J/2-(generalMeanRows 1012).error (generalMeanGrid j.val)+
      (generalMeanRows 1012).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1012).c)).2-
      (generalMeanRows 1012).J/2-(generalMeanRows 1012).error 4 := by
  have he : (generalMeanRows 1012).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1012) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1012)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1012

/-! Kernel-checked entropy margins for general spectral rectangle 1013. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1013
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5975493530) (.branch 2 (.leaf 5781134305) (.leaf 5594727562))) (.branch 5 (.branch 4 (.leaf 5415854497) (.leaf 5244124918)) (.branch 6 (.leaf 5079174719) (.leaf 4920663638)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4768273255) (.leaf 4621705199)) (.branch 10 (.leaf 4480679546) (.leaf 4344933373))) (.branch 13 (.branch 12 (.leaf 4214219450) (.leaf 4088305065)) (.branch 14 (.leaf 3966970955) (.leaf 3850010334))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3737228007) (.branch 17 (.leaf 3628439568) (.leaf 3523470659))) (.branch 20 (.branch 19 (.leaf 3422156297) (.leaf 3324340253)) (.branch 21 (.leaf 3229874483) (.leaf 3138618605)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3050439416) (.leaf 2965210445)) (.branch 25 (.leaf 2882811539) (.leaf 2803128488))) (.branch 28 (.branch 27 (.leaf 2726052661) (.leaf 2651480687)) (.branch 29 (.leaf 2579314144) (.leaf 2509459277)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2441826732) (.branch 32 (.leaf 2376331312) (.leaf 2312891745))) (.branch 35 (.branch 34 (.leaf 2251430470) (.leaf 2191873434)) (.branch 36 (.leaf 2134149905) (.leaf 2078192299)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2023936007) (.leaf 1971319248)) (.branch 40 (.leaf 1920282920) (.leaf 1870770461))) (.branch 43 (.branch 42 (.leaf 1822727725) (.leaf 1776102858)) (.branch 44 (.leaf 1730846184) (.leaf 1686910100))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1644248970) (.branch 47 (.leaf 1602819036) (.leaf 1562578323))) (.branch 50 (.branch 49 (.leaf 1523486556) (.leaf 1485505078)) (.branch 51 (.leaf 1448596775) (.leaf 1412726006)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1377858530) (.leaf 1343961446)) (.branch 55 (.leaf 1311003131) (.leaf 1278953182))) (.branch 58 (.branch 57 (.leaf 1247782358) (.leaf 1217462533)) (.branch 59 (.leaf 1187966645) (.leaf 1159268647))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1131343464) (.branch 62 (.leaf 1104166952) (.leaf 1077715855))) (.branch 65 (.branch 64 (.leaf 1051967771) (.leaf 1026901110)) (.branch 66 (.leaf 1002495065) (.leaf 978729575)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 955585296) (.leaf 933043572)) (.branch 70 (.leaf 911086402) (.leaf 889696419))) (.branch 73 (.branch 72 (.leaf 868856861) (.leaf 848551545)) (.branch 74 (.leaf 828764846) (.leaf 809481675))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 790687457) (.branch 77 (.leaf 772368107) (.leaf 754510017))) (.branch 80 (.branch 79 (.leaf 737100032) (.leaf 720125437)) (.branch 81 (.leaf 703573935) (.leaf 687433635)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 671693033) (.leaf 656341000)) (.branch 85 (.leaf 641366767) (.leaf 626759910))) (.branch 88 (.branch 87 (.leaf 612510341) (.leaf 598608289)) (.branch 89 (.leaf 585044295) (.leaf 571809196)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 558894117) (.branch 92 (.leaf 546290456) (.leaf 533989881))) (.branch 95 (.branch 94 (.leaf 521984315) (.leaf 510265927)) (.branch 96 (.leaf 498827127) (.leaf 487660554)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 476759068) (.leaf 466115745)) (.branch 100 (.leaf 455723867) (.leaf 445576914))) (.branch 103 (.branch 102 (.leaf 435668561) (.leaf 425992667)) (.branch 104 (.leaf 416543272) (.leaf 407314590))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 398301002) (.leaf 389497049)) (.branch 108 (.leaf 380897433) (.leaf 372497004))) (.branch 111 (.branch 110 (.leaf 364290758) (.leaf 356273837)) (.branch 112 (.leaf 348441515) (.leaf 340789200)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 333312431) (.leaf 326006867)) (.branch 116 (.leaf 318868290) (.leaf 311892596))) (.branch 119 (.branch 118 (.leaf 305075795) (.leaf 298414007)) (.branch 120 (.leaf 291903455) (.leaf 285540466)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1013).prefactor = (1265148067922739/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1013).cutoff/(generalMeanRows 1013).c)).2 =
    (288299284164359/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1013).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1013).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1013).q*(generalMeanRows 1013).c/2-2 = (3359/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable311.value]
    have hcontinuation : (generalMeanRows 1013).q*(generalMeanRows 1013).cutoff/2-2 = (821/459:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable330.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1013).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1013

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1013).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1013).criticalRate j.val*(generalMeanRows 1013).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1013).c*(generalMeanRows 1013).criticalPoint j.val)).2-
      (generalMeanRows 1013).J/2-(generalMeanRows 1013).error (generalMeanGrid j.val)+
      (generalMeanRows 1013).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1013).c)).2-
      (generalMeanRows 1013).J/2-(generalMeanRows 1013).error 4 := by
  have he : (generalMeanRows 1013).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1013) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1013)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1013

/-! Kernel-checked entropy margins for general spectral rectangle 1014. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1014
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5861841795) (.branch 2 (.leaf 5672755403) (.leaf 5491435061))) (.branch 5 (.branch 4 (.leaf 5317468221) (.leaf 5150470641)) (.branch 6 (.leaf 4990083897) (.leaf 4835973166)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4687825246) (.leaf 4545346783)) (.branch 10 (.leaf 4408262687) (.leaf 4276314693))) (.branch 13 (.branch 12 (.leaf 4149260074) (.leaf 4026870475)) (.branch 14 (.leaf 3908930845) (.leaf 3795238481))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3685602151) (.branch 17 (.leaf 3579841288) (.leaf 3477785262))) (.branch 20 (.branch 19 (.leaf 3379272712) (.leaf 3284150924)) (.branch 21 (.leaf 3192275272) (.leaf 3103508696)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3017721218) (.leaf 2934789507)) (.branch 25 (.leaf 2854596459) (.leaf 2777030829))) (.branch 28 (.branch 27 (.leaf 2701986870) (.leaf 2629364012)) (.branch 29 (.leaf 2559066558) (.leaf 2491003400)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2425087759) (.branch 32 (.leaf 2361236939) (.leaf 2299372097))) (.branch 35 (.branch 34 (.leaf 2239418034) (.leaf 2181302990)) (.branch 36 (.leaf 2124958463) (.leaf 2070319030)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2017322185) (.leaf 1965908187)) (.branch 40 (.leaf 1916019911) (.leaf 1867602720))) (.branch 43 (.branch 42 (.leaf 1820604329) (.leaf 1774974695)) (.branch 44 (.leaf 1730665896) (.leaf 1687632028))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1645829109) (.branch 47 (.leaf 1605214977) (.leaf 1565749209))) (.branch 50 (.branch 49 (.leaf 1527393031) (.leaf 1490109242)) (.branch 51 (.leaf 1453862138) (.leaf 1418617443)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1384342239) (.leaf 1351004907)) (.branch 55 (.leaf 1318575061) (.leaf 1287023498))) (.branch 58 (.branch 57 (.leaf 1256322139) (.leaf 1226443981)) (.branch 59 (.leaf 1197363047) (.leaf 1169054341))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1141493805) (.branch 62 (.leaf 1114658277) (.leaf 1088525450))) (.branch 65 (.branch 64 (.leaf 1063073839) (.leaf 1038282742)) (.branch 66 (.leaf 1014132207) (.leaf 990603003)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 967676583) (.leaf 945335063)) (.branch 70 (.leaf 923561188) (.leaf 902338309))) (.branch 73 (.branch 72 (.leaf 881650357) (.leaf 861481821)) (.branch 74 (.leaf 841817722) (.leaf 822643593))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 803945458) (.branch 77 (.leaf 785709815) (.leaf 767923614))) (.branch 80 (.branch 79 (.leaf 750574238) (.leaf 733649490)) (.branch 81 (.leaf 717137574) (.leaf 701027080)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 685306969) (.leaf 669966559)) (.branch 85 (.leaf 654995510) (.leaf 640383814))) (.branch 88 (.branch 87 (.leaf 626121779) (.leaf 612200019)) (.branch 89 (.leaf 598609444) (.leaf 585341247)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 572386891) (.branch 92 (.leaf 559738106) (.leaf 547386874))) (.branch 95 (.branch 94 (.leaf 535325421) (.leaf 523546207)) (.branch 96 (.leaf 512041924) (.leaf 500805477)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 489829986) (.leaf 479108774)) (.branch 100 (.leaf 468635361) (.leaf 458403455))) (.branch 103 (.branch 102 (.leaf 448406951) (.leaf 438639918)) (.branch 104 (.leaf 429096597) (.leaf 419771395))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 410658876) (.leaf 401753762)) (.branch 108 (.leaf 393050921) (.leaf 384545368))) (.branch 111 (.branch 110 (.leaf 376232254) (.leaf 368106869)) (.branch 112 (.leaf 360164631) (.leaf 352401083)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 344811894) (.leaf 337392848)) (.branch 116 (.leaf 330139844) (.leaf 323048894))) (.branch 119 (.branch 118 (.leaf 316116116) (.leaf 309337731)) (.branch 120 (.leaf 302710063) (.leaf 296229532)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1014).prefactor = (1247049331142919/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1014).cutoff/(generalMeanRows 1014).c)).2 =
    (154213848711023/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1014).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1014).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1014).q*(generalMeanRows 1014).c/2-2 = (663/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable325.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1014).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1014

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1014).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1014).criticalRate j.val*(generalMeanRows 1014).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1014).c*(generalMeanRows 1014).criticalPoint j.val)).2-
      (generalMeanRows 1014).J/2-(generalMeanRows 1014).error (generalMeanGrid j.val)+
      (generalMeanRows 1014).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1014).c)).2-
      (generalMeanRows 1014).J/2-(generalMeanRows 1014).error 4 := by
  have he : (generalMeanRows 1014).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1014) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1014)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1014

/-! Kernel-checked entropy margins for general spectral rectangle 1015. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1015
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5838160963) (.branch 2 (.leaf 5654101422) (.leaf 5477594338))) (.branch 5 (.branch 4 (.leaf 5308234541) (.leaf 5145644844)) (.branch 6 (.leaf 4989473588) (.leaf 4839392443)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4695094459) (.leaf 4556292306)) (.branch 10 (.leaf 4422716707) (.leaf 4294115017))) (.branch 13 (.branch 12 (.leaf 4170249943) (.leaf 4050898388)) (.branch 14 (.leaf 3935850400) (.leaf 3824908216))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3717885392) (.branch 17 (.leaf 3614606011) (.leaf 3514903956))) (.branch 20 (.branch 19 (.leaf 3418622241) (.leaf 3325612406)) (.branch 21 (.leaf 3235733954) (.leaf 3148853834)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3064845962) (.leaf 2983590789)) (.branch 25 (.leaf 2904974884) (.leaf 2828890569))) (.branch 28 (.branch 27 (.leaf 2755235559) (.leaf 2683912649)) (.branch 29 (.leaf 2614829406) (.leaf 2547897891)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2483034401) (.branch 32 (.leaf 2420159224) (.leaf 2359196416))) (.branch 35 (.branch 34 (.leaf 2300073586) (.leaf 2242721700)) (.branch 36 (.leaf 2187074898) (.leaf 2133070320)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2080647945) (.leaf 2029750436)) (.branch 40 (.leaf 1980323005) (.leaf 1932313271))) (.branch 43 (.branch 42 (.leaf 1885671141) (.leaf 1840348690)) (.branch 44 (.leaf 1796300048) (.leaf 1753481300))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1711850383) (.branch 47 (.leaf 1671366998) (.leaf 1631992518))) (.branch 50 (.branch 49 (.leaf 1593689912) (.leaf 1556423660)) (.branch 51 (.leaf 1520159685) (.leaf 1484865283)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1450509056) (.leaf 1417060849)) (.branch 55 (.leaf 1384491696) (.leaf 1352773762))) (.branch 58 (.branch 57 (.leaf 1321880287) (.leaf 1291785545)) (.branch 59 (.leaf 1262464789) (.leaf 1233894210))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1206050894) (.branch 62 (.leaf 1178912782) (.leaf 1152458632))) (.branch 65 (.branch 64 (.leaf 1126667985) (.leaf 1101521126)) (.branch 66 (.leaf 1076999056) (.leaf 1053083459)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1029756671) (.leaf 1007001658)) (.branch 70 (.leaf 984801983) (.leaf 963141782))) (.branch 73 (.branch 72 (.leaf 942005744) (.leaf 921379084)) (.branch 74 (.leaf 901247522) (.leaf 881597263))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 862414978) (.branch 77 (.leaf 843687783) (.leaf 825403223))) (.branch 80 (.branch 79 (.leaf 807549253) (.leaf 790114224)) (.branch 81 (.leaf 773086866) (.leaf 756456272)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 740211886) (.leaf 724343489)) (.branch 85 (.leaf 708841185) (.leaf 693695391))) (.branch 88 (.branch 87 (.leaf 678896819) (.leaf 664436475)) (.branch 89 (.leaf 650305638) (.leaf 636495856)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 622998933) (.branch 92 (.leaf 609806922) (.leaf 596912115))) (.branch 95 (.branch 94 (.leaf 584307032) (.leaf 571984417)) (.branch 96 (.leaf 559937226) (.leaf 548158622)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 536641968) (.leaf 525380818)) (.branch 100 (.leaf 514368911) (.leaf 503600165))) (.branch 103 (.branch 102 (.leaf 493068672) (.leaf 482768688)) (.branch 104 (.leaf 472694634) (.leaf 462841084))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 453202763) (.leaf 443774542)) (.branch 108 (.leaf 434551432) (.leaf 425528582))) (.branch 111 (.branch 110 (.leaf 416701270) (.leaf 408064904)) (.branch 112 (.leaf 399615012) (.leaf 391347245)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 383257367) (.leaf 375341254)) (.branch 116 (.leaf 367594892) (.leaf 360014371))) (.branch 119 (.branch 118 (.leaf 352595882) (.leaf 345335716)) (.branch 120 (.leaf 338230259) (.leaf 331275989)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1015).prefactor = (306925679684923/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1015).cutoff/(generalMeanRows 1015).c)).2 =
    (83994685347189/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1015).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1015).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1015).q*(generalMeanRows 1015).c/2-2 = (799/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable320.value]
    have hcontinuation : (generalMeanRows 1015).q*(generalMeanRows 1015).cutoff/2-2 = (23/12:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable028.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1015).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1015

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1015).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1015).criticalRate j.val*(generalMeanRows 1015).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1015).c*(generalMeanRows 1015).criticalPoint j.val)).2-
      (generalMeanRows 1015).J/2-(generalMeanRows 1015).error (generalMeanGrid j.val)+
      (generalMeanRows 1015).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1015).c)).2-
      (generalMeanRows 1015).J/2-(generalMeanRows 1015).error 4 := by
  have he : (generalMeanRows 1015).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1015) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1015)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1015

/-! Kernel-checked entropy margins for general spectral rectangle 1016. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1016
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5732874279) (.branch 2 (.leaf 5554435239) (.leaf 5383335457))) (.branch 5 (.branch 4 (.leaf 5219177232) (.leaf 5061590508)) (.branch 6 (.leaf 4910230450) (.leaf 4764775275)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4624924317) (.leaf 4490396299)) (.branch 10 (.leaf 4360927773) (.leaf 4236271717))) (.branch 13 (.branch 12 (.leaf 4116196267) (.leaf 4000483577)) (.branch 14 (.leaf 3888928766) (.leaf 3781338985))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3677532543) (.branch 17 (.leaf 3577338129) (.leaf 3480594086))) (.branch 20 (.branch 19 (.leaf 3387147754) (.leaf 3296854862)) (.branch 21 (.leaf 3209578977) (.leaf 3125190986)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3043568626) (.leaf 2964596048)) (.branch 25 (.leaf 2888163414) (.leaf 2814166525))) (.branch 28 (.branch 27 (.leaf 2742506474) (.leaf 2673089325)) (.branch 29 (.leaf 2605825817) (.leaf 2540631086)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2477424407) (.branch 32 (.leaf 2416128956) (.leaf 2356671585))) (.branch 35 (.branch 34 (.leaf 2298982612) (.leaf 2242995628)) (.branch 36 (.leaf 2188647314) (.leaf 2135877270)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2084627858) (.leaf 2034844049)) (.branch 40 (.leaf 1986473283) (.leaf 1939465341))) (.branch 43 (.branch 42 (.leaf 1893772218) (.leaf 1849348009)) (.branch 44 (.leaf 1806148799) (.leaf 1764132563))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1723259065) (.branch 47 (.leaf 1683489770) (.leaf 1644787761))) (.branch 50 (.branch 49 (.leaf 1607117652) (.leaf 1570445518)) (.branch 51 (.leaf 1534738821) (.leaf 1499966343)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1466098119) (.leaf 1433105382)) (.branch 55 (.leaf 1400960501) (.leaf 1369636932))) (.branch 58 (.branch 57 (.leaf 1339109162) (.leaf 1309352664)) (.branch 59 (.leaf 1280343850) (.leaf 1252060030))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1224479366) (.branch 62 (.leaf 1197580838) (.leaf 1171344208))) (.branch 65 (.branch 64 (.leaf 1145749979) (.leaf 1120779368)) (.branch 66 (.leaf 1096414271) (.leaf 1072637235)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1049431430) (.leaf 1026780619)) (.branch 70 (.leaf 1004669138) (.leaf 983081865))) (.branch 73 (.branch 72 (.leaf 962004202) (.leaf 941422052)) (.branch 74 (.leaf 921321797) (.leaf 901690278))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 882514776) (.branch 77 (.leaf 863782998) (.leaf 845483053))) (.branch 80 (.branch 79 (.leaf 827603440) (.leaf 810133034)) (.branch 81 (.leaf 793061065) (.leaf 776377111)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 760071080) (.leaf 744133196)) (.branch 85 (.leaf 728553993) (.leaf 713324295))) (.branch 88 (.branch 87 (.leaf 698435213) (.leaf 683878127)) (.branch 89 (.leaf 669644680) (.leaf 655726769)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 642116532) (.branch 92 (.leaf 628806341) (.leaf 615788795))) (.branch 95 (.branch 94 (.leaf 603056709) (.leaf 590603108)) (.branch 96 (.leaf 578421219) (.leaf 566504463)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 554846451) (.leaf 543440974)) (.branch 100 (.leaf 532281997) (.leaf 521363656))) (.branch 103 (.branch 102 (.leaf 510680251) (.leaf 500226236)) (.branch 104 (.leaf 489996222) (.leaf 479984963))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 470187360) (.leaf 460598448)) (.branch 108 (.leaf 451213397) (.leaf 442027505))) (.branch 111 (.branch 110 (.leaf 433036195) (.leaf 424235012)) (.branch 112 (.leaf 415619615) (.leaf 407185780)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 398929388) (.leaf 390846431)) (.branch 116 (.leaf 382933000) (.leaf 375185289))) (.branch 119 (.branch 118 (.leaf 367599585) (.leaf 360172272)) (.branch 120 (.leaf 352899824) (.leaf 345778801)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1016).prefactor = (2414593085524973/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1016).cutoff/(generalMeanRows 1016).c)).2 =
    (358127365974317/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1016).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1016).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1016).q*(generalMeanRows 1016).c/2-2 = (3147/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable328.value]
    have hcontinuation : (generalMeanRows 1016).q*(generalMeanRows 1016).cutoff/2-2 = (1663/837:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable331.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1016).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1016

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1016).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1016).criticalRate j.val*(generalMeanRows 1016).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1016).c*(generalMeanRows 1016).criticalPoint j.val)).2-
      (generalMeanRows 1016).J/2-(generalMeanRows 1016).error (generalMeanGrid j.val)+
      (generalMeanRows 1016).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1016).c)).2-
      (generalMeanRows 1016).J/2-(generalMeanRows 1016).error 4 := by
  have he : (generalMeanRows 1016).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1016) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1016)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1016

/-! Kernel-checked entropy margins for general spectral rectangle 1017. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1017
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5349948241) (.branch 2 (.leaf 5168558393) (.leaf 4994854671))) (.branch 5 (.branch 4 (.leaf 4828421681) (.leaf 4668872674)) (.branch 6 (.leaf 4515847043) (.leaf 4369008084)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4228041002) (.leaf 4092651123)) (.branch 10 (.leaf 3962562285) (.leaf 3837515387))) (.branch 13 (.branch 12 (.leaf 3717267086) (.leaf 3601588605)) (.branch 14 (.leaf 3490264662) (.leaf 3383092493))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3279880956) (.branch 17 (.leaf 3180449718) (.leaf 3084628515))) (.branch 20 (.branch 19 (.leaf 2992256463) (.leaf 2903181436)) (.branch 21 (.leaf 2817259489) (.leaf 2734354327)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2654336816) (.leaf 2577084530)) (.branch 25 (.leaf 2502481340) (.leaf 2430417016))) (.branch 28 (.branch 27 (.leaf 2360786879) (.leaf 2293491465)) (.branch 29 (.leaf 2228436212) (.leaf 2165531179)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2104690775) (.branch 32 (.leaf 2045833510) (.leaf 1988881761))) (.branch 35 (.branch 34 (.leaf 1933761561) (.leaf 1880402386)) (.branch 36 (.leaf 1828736977) (.leaf 1778701152)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1730233647) (.leaf 1683275956)) (.branch 40 (.leaf 1637772187) (.leaf 1593668922))) (.branch 43 (.branch 42 (.leaf 1550915094) (.leaf 1509461858)) (.branch 44 (.leaf 1469262482) (.leaf 1430272241))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1392448311) (.branch 47 (.leaf 1355749678) (.leaf 1320137048))) (.branch 50 (.branch 49 (.leaf 1285572759) (.leaf 1252020707)) (.branch 51 (.leaf 1219446266) (.leaf 1187816218)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1157098687) (.leaf 1127263074)) (.branch 55 (.leaf 1098280000) (.leaf 1070121244))) (.branch 58 (.branch 57 (.leaf 1042759692) (.leaf 1016169290)) (.branch 59 (.leaf 990324987) (.leaf 965202697))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 940779252) (.branch 62 (.leaf 917032361) (.leaf 893940572))) (.branch 65 (.branch 64 (.leaf 871483236) (.leaf 849640469)) (.branch 66 (.leaf 828393118) (.leaf 807722736)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 787611543) (.leaf 768042404)) (.branch 70 (.leaf 748998797) (.leaf 730464791))) (.branch 73 (.branch 72 (.leaf 712425019) (.leaf 694864655)) (.branch 74 (.leaf 677769392) (.leaf 661125420))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 644919406) (.branch 77 (.leaf 629138476) (.leaf 613770192))) (.branch 80 (.branch 79 (.leaf 598802543) (.leaf 584223918)) (.branch 81 (.leaf 570023096) (.leaf 556189233)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 542711839) (.leaf 529580773)) (.branch 85 (.leaf 516786224) (.leaf 504318700))) (.branch 88 (.branch 87 (.leaf 492169017) (.leaf 480328284)) (.branch 89 (.leaf 468787898) (.leaf 457539526)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 446575101) (.branch 92 (.leaf 435886807) (.leaf 425467075))) (.branch 95 (.branch 94 (.leaf 415308570) (.leaf 405404184)) (.branch 96 (.leaf 395747028) (.leaf 386330424)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 377147897) (.leaf 368193170)) (.branch 100 (.leaf 359460152) (.leaf 350942937))) (.branch 103 (.branch 102 (.leaf 342635794) (.leaf 334533165)) (.branch 104 (.leaf 326629653) (.leaf 318920021))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 311399186) (.leaf 304062212)) (.branch 108 (.leaf 296904308) (.leaf 289920819))) (.branch 111 (.branch 110 (.leaf 283107226) (.leaf 276459139)) (.branch 112 (.leaf 269972291) (.leaf 263642540)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 257465857) (.leaf 251438329)) (.branch 116 (.leaf 245556153) (.leaf 239815629))) (.branch 119 (.branch 118 (.leaf 234213164) (.leaf 228745263)) (.branch 120 (.leaf 223408525) (.leaf 218199646)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1017).prefactor = (4997995123910217/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1017).cutoff/(generalMeanRows 1017).c)).2 =
    (314506743498429/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1017).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1017).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1017).q*(generalMeanRows 1017).cutoff/2-2 = (1663/837:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable331.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1017).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1017

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1017).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1017).criticalRate j.val*(generalMeanRows 1017).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1017).c*(generalMeanRows 1017).criticalPoint j.val)).2-
      (generalMeanRows 1017).J/2-(generalMeanRows 1017).error (generalMeanGrid j.val)+
      (generalMeanRows 1017).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1017).c)).2-
      (generalMeanRows 1017).J/2-(generalMeanRows 1017).error 4 := by
  have he : (generalMeanRows 1017).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1017) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1017)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1017

/-! Kernel-checked entropy margins for general spectral rectangle 1018. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1018
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5481139240) (.branch 2 (.leaf 5304252030) (.leaf 5134770921))) (.branch 5 (.branch 4 (.leaf 4972291447) (.leaf 4816437337)) (.branch 6 (.leaf 4666858036) (.leaf 4523226508)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4385237261) (.leaf 4252604581)) (.branch 10 (.leaf 4125060945) (.leaf 4002355592))) (.branch 13 (.branch 12 (.leaf 3884253223) (.leaf 3770532839)) (.branch 14 (.leaf 3660986667) (.leaf 3555419202))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3453646323) (.branch 17 (.leaf 3355494486) (.leaf 3260799988))) (.branch 20 (.branch 19 (.leaf 3169408296) (.leaf 3081173426)) (.branch 21 (.leaf 2995957370) (.leaf 2913629579)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2834066475) (.leaf 2757151007)) (.branch 25 (.leaf 2682772238) (.leaf 2610824965))) (.branch 28 (.branch 27 (.leaf 2541209364) (.leaf 2473830663)) (.branch 29 (.leaf 2408598838) (.leaf 2345428331)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2284237782) (.branch 32 (.leaf 2224949793) (.leaf 2167490689))) (.branch 35 (.branch 34 (.leaf 2111790313) (.leaf 2057781824)) (.branch 36 (.leaf 2005401510) (.leaf 1954588616)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1905285180) (.leaf 1857435883)) (.branch 40 (.leaf 1810987902) (.leaf 1765890780))) (.branch 43 (.branch 42 (.leaf 1722096300) (.leaf 1679558364)) (.branch 44 (.leaf 1638232885) (.leaf 1598077682))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1559052383) (.branch 47 (.leaf 1521118331) (.leaf 1484238498))) (.branch 50 (.branch 49 (.leaf 1448377403) (.leaf 1413501037)) (.branch 51 (.leaf 1379576787) (.leaf 1346573370)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1314460767) (.leaf 1283210162)) (.branch 55 (.leaf 1252793885) (.leaf 1223185357))) (.branch 58 (.branch 57 (.leaf 1194359039) (.leaf 1166290383)) (.branch 59 (.leaf 1138955784) (.leaf 1112332541))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1086398809) (.branch 62 (.leaf 1061133567) (.leaf 1036516576))) (.branch 65 (.branch 64 (.leaf 1012528345) (.leaf 989150098)) (.branch 66 (.leaf 966363743) (.leaf 944151841)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 922497578) (.leaf 901384736)) (.branch 70 (.leaf 880797673) (.leaf 860721290))) (.branch 73 (.branch 72 (.leaf 841141017) (.leaf 822042782)) (.branch 74 (.leaf 803412997) (.leaf 785238536))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 767506714) (.branch 77 (.leaf 750205270) (.leaf 733322352))) (.branch 80 (.branch 79 (.leaf 716846497) (.leaf 700766618)) (.branch 81 (.leaf 685071988) (.leaf 669752227)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 654797285) (.leaf 640197433)) (.branch 85 (.leaf 625943251) (.leaf 612025612))) (.branch 88 (.branch 87 (.leaf 598435674) (.leaf 585164868)) (.branch 89 (.leaf 572204890) (.leaf 559547687)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 547185453) (.branch 92 (.leaf 535110614) (.leaf 523315824))) (.branch 95 (.branch 94 (.leaf 511793957) (.leaf 500538096)) (.branch 96 (.leaf 489541525) (.leaf 478797729)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 468300376) (.leaf 458043322)) (.branch 100 (.leaf 448020595) (.leaf 438226396))) (.branch 103 (.branch 102 (.leaf 428655087) (.leaf 419301191)) (.branch 104 (.leaf 410159384) (.leaf 401224491))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 392491477) (.leaf 383955450)) (.branch 108 (.leaf 375611649) (.leaf 367455443))) (.branch 111 (.branch 110 (.leaf 359482327) (.leaf 351687918)) (.branch 112 (.leaf 344067949) (.leaf 336618269)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 329334835) (.leaf 322213713)) (.branch 116 (.leaf 315251071) (.leaf 308443178))) (.branch 119 (.branch 118 (.leaf 301786399) (.leaf 295277195)) (.branch 120 (.leaf 288912118) (.leaf 282687808)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1018).prefactor = (4900586141633259/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1018).cutoff/(generalMeanRows 1018).c)).2 =
    (178242496187913/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1018).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1018).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1018).q*(generalMeanRows 1018).c/2-2 = (27/32:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable332.value]
    have hcontinuation : (generalMeanRows 1018).q*(generalMeanRows 1018).cutoff/2-2 = (167/81:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable333.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1018).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1018

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1018).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1018).criticalRate j.val*(generalMeanRows 1018).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1018).c*(generalMeanRows 1018).criticalPoint j.val)).2-
      (generalMeanRows 1018).J/2-(generalMeanRows 1018).error (generalMeanGrid j.val)+
      (generalMeanRows 1018).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1018).c)).2-
      (generalMeanRows 1018).J/2-(generalMeanRows 1018).error 4 := by
  have he : (generalMeanRows 1018).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1018) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1018)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1018

/-! Kernel-checked entropy margins for general spectral rectangle 1019. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1019
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5496554674) (.branch 2 (.leaf 5314787579) (.leaf 5140697288))) (.branch 5 (.branch 4 (.leaf 4973864862) (.leaf 4813900494)) (.branch 6 (.leaf 4660440959) (.leaf 4513147338)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4371702983) (.leaf 4235811695)) (.branch 10 (.leaf 4105196083) (.leaf 3979596087))) (.branch 13 (.branch 12 (.leaf 3858767645) (.leaf 3742481480)) (.branch 14 (.leaf 3630522004) (.leaf 3522686322))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3418783314) (.branch 17 (.leaf 3318632815) (.leaf 3222064845))) (.branch 20 (.branch 19 (.leaf 3128918918) (.leaf 3039043398)) (.branch 21 (.leaf 2952294916) (.leaf 2868537826)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2787643705) (.leaf 2709490895)) (.branch 25 (.leaf 2633964074) (.leaf 2560953866))) (.branch 28 (.branch 27 (.leaf 2490356471) (.leaf 2422073328)) (.branch 29 (.leaf 2356010803) (.leaf 2292079894)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2230195958) (.branch 32 (.leaf 2170278460) (.leaf 2112250734))) (.branch 35 (.branch 34 (.leaf 2056039765) (.leaf 2001575983)) (.branch 36 (.leaf 1948793069) (.leaf 1897627775)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1848019758) (.leaf 1799911419)) (.branch 40 (.leaf 1753247759) (.leaf 1707976237))) (.branch 43 (.branch 42 (.leaf 1664046642) (.leaf 1621410967)) (.branch 44 (.leaf 1580023302) (.leaf 1539839716))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1500818164) (.branch 47 (.leaf 1462918388) (.leaf 1426101825))) (.branch 50 (.branch 49 (.leaf 1390331525) (.leaf 1355572070)) (.branch 51 (.leaf 1321789501) (.leaf 1288951242)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1257026036) (.leaf 1225983883)) (.branch 55 (.leaf 1195795976) (.leaf 1166434648))) (.branch 58 (.branch 57 (.leaf 1137873316) (.leaf 1110086432)) (.branch 59 (.leaf 1083049435) (.leaf 1056738704))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1031131516) (.branch 62 (.leaf 1006206005) (.leaf 981941125))) (.branch 65 (.branch 64 (.leaf 958316611) (.leaf 935312946)) (.branch 66 (.leaf 912911327) (.leaf 891093634)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 869842400) (.leaf 849140785)) (.branch 70 (.leaf 828972545) (.leaf 809322011))) (.branch 73 (.branch 72 (.leaf 790174061) (.leaf 771514101)) (.branch 74 (.leaf 753328039) (.leaf 735602266))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 718323637) (.branch 77 (.leaf 701479451) (.leaf 685057434))) (.branch 80 (.branch 79 (.leaf 669045719) (.leaf 653432834)) (.branch 81 (.leaf 638207683) (.leaf 623359533)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 608877998) (.leaf 594753029)) (.branch 85 (.leaf 580974895) (.leaf 567534178))) (.branch 88 (.branch 87 (.leaf 554421756) (.leaf 541628793)) (.branch 89 (.leaf 529146730) (.leaf 516967273)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 505082383) (.branch 92 (.leaf 493484267) (.leaf 482165369))) (.branch 95 (.branch 94 (.leaf 471118364) (.leaf 460336144)) (.branch 96 (.leaf 449811816) (.leaf 439538690)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 429510275) (.leaf 419720271)) (.branch 100 (.leaf 410162562) (.leaf 400831208))) (.branch 103 (.branch 102 (.leaf 391720443) (.leaf 382824666)) (.branch 104 (.leaf 374138436) (.leaf 365656467))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 357373622) (.leaf 349284910)) (.branch 108 (.leaf 341385479) (.leaf 333670611))) (.branch 111 (.branch 110 (.leaf 326135723) (.leaf 318776354)) (.branch 112 (.leaf 311588168) (.leaf 304566948)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 297708590) (.leaf 291009103)) (.branch 116 (.leaf 284464603) (.leaf 278071311))) (.branch 119 (.branch 118 (.leaf 271825548) (.leaf 265723733)) (.branch 120 (.leaf 259762383) (.leaf 253938104)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1019).prefactor = (2531161559287533/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1019).cutoff/(generalMeanRows 1019).c)).2 =
    (344252423940191/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1019).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1019).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1019).q*(generalMeanRows 1019).c/2-2 = (703/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable334.value]
    have hcontinuation : (generalMeanRows 1019).q*(generalMeanRows 1019).cutoff/2-2 = (167/81:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable333.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1019).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1019

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1019).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1019).criticalRate j.val*(generalMeanRows 1019).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1019).c*(generalMeanRows 1019).criticalPoint j.val)).2-
      (generalMeanRows 1019).J/2-(generalMeanRows 1019).error (generalMeanGrid j.val)+
      (generalMeanRows 1019).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1019).c)).2-
      (generalMeanRows 1019).J/2-(generalMeanRows 1019).error 4 := by
  have he : (generalMeanRows 1019).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1019) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1019)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1019

/-! Kernel-checked entropy margins for general spectral rectangle 1020. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1020
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5677960757) (.branch 2 (.leaf 5490194694) (.leaf 5310358797))) (.branch 5 (.branch 4 (.leaf 5138020300) (.leaf 4972776532)) (.branch 6 (.leaf 4814252281) (.leaf 4662097440)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4515984913) (.leaf 4375608723)) (.branch 10 (.leaf 4240682326) (.leaf 4110937078))) (.branch 13 (.branch 12 (.leaf 3986120863) (.leaf 3865996836)) (.branch 14 (.leaf 3750342295) (.leaf 3638947646))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3531615466) (.branch 17 (.leaf 3428159640) (.leaf 3328404579))) (.branch 20 (.branch 19 (.leaf 3232184501) (.leaf 3139342765)) (.branch 21 (.leaf 3049731272) (.leaf 2963209896)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2879645978) (.leaf 2798913844)) (.branch 25 (.leaf 2720894367) (.leaf 2645474559))) (.branch 28 (.branch 27 (.leaf 2572547195) (.leaf 2502010463)) (.branch 29 (.leaf 2433767638) (.leaf 2367726779)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2303800450) (.branch 32 (.leaf 2241905459) (.leaf 2181962609))) (.branch 35 (.branch 34 (.leaf 2123896476) (.leaf 2067635193)) (.branch 36 (.leaf 2013110253) (.leaf 1960256320)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1909011059) (.leaf 1859314973)) (.branch 40 (.leaf 1811111244) (.leaf 1764345599))) (.branch 43 (.branch 42 (.leaf 1718966169) (.leaf 1674923364)) (.branch 44 (.leaf 1632169756) (.leaf 1590659968))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1550350564) (.branch 47 (.leaf 1511199959) (.leaf 1473168317))) (.branch 50 (.branch 49 (.leaf 1436217468) (.leaf 1400310826)) (.branch 51 (.leaf 1365413311) (.leaf 1331491271)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1298512419) (.leaf 1266445763)) (.branch 55 (.leaf 1235261546) (.leaf 1204931189))) (.branch 58 (.branch 57 (.leaf 1175427230) (.leaf 1146723279)) (.branch 59 (.leaf 1118793964) (.leaf 1091614884))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1065162566) (.branch 62 (.leaf 1039414424) (.leaf 1014348716))) (.branch 65 (.branch 64 (.leaf 989944508) (.leaf 966181639)) (.branch 66 (.leaf 943040686) (.leaf 920502930)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 898550330) (.leaf 877165486)) (.branch 70 (.leaf 856331622) (.leaf 836032549))) (.branch 73 (.branch 72 (.leaf 816252648) (.leaf 796976842)) (.branch 74 (.leaf 778190575) (.leaf 759879788))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 742030902) (.branch 77 (.leaf 724630798) (.leaf 707666795))) (.branch 80 (.branch 79 (.leaf 691126636) (.leaf 674998469)) (.branch 81 (.leaf 659270834) (.leaf 643932641)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 628973163) (.leaf 614382019)) (.branch 85 (.leaf 600149157) (.leaf 586264848))) (.branch 88 (.branch 87 (.leaf 572719669) (.leaf 559504492)) (.branch 89 (.leaf 546610477) (.leaf 534029054)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 521751919) (.branch 92 (.leaf 509771023) (.leaf 498078562))) (.branch 95 (.branch 94 (.leaf 486666965) (.leaf 475528893)) (.branch 96 (.leaf 464657224) (.leaf 454045048)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 443685660) (.leaf 433572551)) (.branch 100 (.leaf 423699402) (.leaf 414060080))) (.branch 103 (.branch 102 (.leaf 404648627) (.leaf 395459258)) (.branch 104 (.leaf 386486351) (.leaf 377724446))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 369168237) (.leaf 360812569)) (.branch 108 (.leaf 352652428) (.leaf 344682942))) (.branch 111 (.branch 110 (.leaf 336899375) (.leaf 329297121)) (.branch 112 (.leaf 321871699) (.leaf 314618753)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 307534045) (.leaf 300613451)) (.branch 116 (.leaf 293852959) (.leaf 287248665))) (.branch 119 (.branch 118 (.leaf 280796769) (.leaf 274493573)) (.branch 120 (.leaf 268335477) (.leaf 262318975)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1020).prefactor = (2614698998875119/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1020).cutoff/(generalMeanRows 1020).c)).2 =
    (344252423940191/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1020).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1020).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1020).q*(generalMeanRows 1020).c/2-2 = (703/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable334.value]
    have hcontinuation : (generalMeanRows 1020).q*(generalMeanRows 1020).cutoff/2-2 = (167/81:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable333.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1020).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1020

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1020).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1020).criticalRate j.val*(generalMeanRows 1020).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1020).c*(generalMeanRows 1020).criticalPoint j.val)).2-
      (generalMeanRows 1020).J/2-(generalMeanRows 1020).error (generalMeanGrid j.val)+
      (generalMeanRows 1020).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1020).c)).2-
      (generalMeanRows 1020).J/2-(generalMeanRows 1020).error 4 := by
  have he : (generalMeanRows 1020).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1020) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1020)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1020

/-! Kernel-checked entropy margins for general spectral rectangle 1021. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1021
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5865353893) (.branch 2 (.leaf 5671390875) (.leaf 5485619746))) (.branch 5 (.branch 4 (.leaf 5307593459) (.leaf 5136896052)) (.branch 6 (.leaf 4973139930) (.leaf 4815963432)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4665028665) (.leaf 4520019556)) (.branch 10 (.leaf 4380640102) (.leaf 4246612795))) (.branch 13 (.branch 12 (.leaf 4117677195) (.leaf 3993588643)) (.branch 14 (.leaf 3874117086) (.leaf 3759046013))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3648171484) (.branch 17 (.leaf 3541301244) (.leaf 3438253907))) (.branch 20 (.branch 19 (.leaf 3338858220) (.leaf 3242952373)) (.branch 21 (.leaf 3150383378) (.leaf 3061006485)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2974684658) (.leaf 2891288073)) (.branch 25 (.leaf 2810693672) (.leaf 2732784739))) (.branch 28 (.branch 27 (.leaf 2657450510) (.leaf 2584585812)) (.branch 29 (.leaf 2514090728) (.leaf 2445870282)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2379834155) (.branch 32 (.leaf 2315896406) (.leaf 2253975226))) (.branch 35 (.branch 34 (.leaf 2193992702) (.leaf 2135874595)) (.branch 36 (.leaf 2079550135) (.leaf 2024951832)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1972015294) (.leaf 1920679057)) (.branch 40 (.leaf 1870884432) (.leaf 1822575353))) (.branch 43 (.branch 42 (.leaf 1775698238) (.leaf 1730201862)) (.branch 44 (.leaf 1686037231) (.leaf 1643157470))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1601517712) (.branch 47 (.leaf 1561074996) (.leaf 1521788172))) (.branch 50 (.branch 49 (.leaf 1483617812) (.leaf 1446526123)) (.branch 51 (.leaf 1410476863) (.leaf 1375435274)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1341368001) (.leaf 1308243030)) (.branch 55 (.leaf 1276029622) (.leaf 1244698254))) (.branch 58 (.branch 57 (.leaf 1214220558) (.leaf 1184569274)) (.branch 59 (.leaf 1155718191) (.leaf 1127642103))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1100316764) (.branch 62 (.leaf 1073718840) (.leaf 1047825873))) (.branch 65 (.branch 64 (.leaf 1022616239) (.leaf 998069110)) (.branch 66 (.leaf 974164422) (.leaf 950882840)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 928205724) (.leaf 906115104)) (.branch 70 (.leaf 884593647) (.leaf 863624632))) (.branch 73 (.branch 72 (.leaf 843191923) (.leaf 823279946)) (.branch 74 (.leaf 803873664) (.leaf 784958555))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 766520592) (.branch 77 (.leaf 748546221) (.leaf 731022345))) (.branch 80 (.branch 79 (.leaf 713936302) (.leaf 697275848)) (.branch 81 (.leaf 681029143) (.leaf 665184735)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 649731541) (.leaf 634658836)) (.branch 85 (.leaf 619956239) (.leaf 605613697))) (.branch 88 (.branch 87 (.leaf 591621479) (.leaf 577970154)) (.branch 89 (.leaf 564650589) (.leaf 551653934)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 538971610) (.branch 92 (.leaf 526595301) (.leaf 514516946))) (.branch 95 (.branch 94 (.leaf 502728726) (.leaf 491223058)) (.branch 96 (.leaf 479992584) (.leaf 469030168)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 458328883) (.leaf 447882005)) (.branch 100 (.leaf 437683007) (.leaf 427725553))) (.branch 103 (.branch 102 (.leaf 418003488) (.leaf 408510836)) (.branch 104 (.leaf 399241791) (.leaf 390190712))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 381352118) (.leaf 372720682)) (.branch 108 (.leaf 364291227) (.leaf 356058720))) (.branch 111 (.branch 110 (.leaf 348018267) (.leaf 340165111)) (.branch 112 (.leaf 332494623) (.leaf 325002304)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 317683775) (.leaf 310534776)) (.branch 116 (.leaf 303551164) (.leaf 296728904))) (.branch 119 (.branch 118 (.leaf 290064073) (.leaf 283552848)) (.branch 120 (.leaf 277191513) (.leaf 270976445)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1021).prefactor = (5401986949140397/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1021).cutoff/(generalMeanRows 1021).c)).2 =
    (344252423940191/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1021).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1021).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1021).q*(generalMeanRows 1021).c/2-2 = (703/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable334.value]
    have hcontinuation : (generalMeanRows 1021).q*(generalMeanRows 1021).cutoff/2-2 = (167/81:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable333.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1021).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1021

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1021).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1021).criticalRate j.val*(generalMeanRows 1021).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1021).c*(generalMeanRows 1021).criticalPoint j.val)).2-
      (generalMeanRows 1021).J/2-(generalMeanRows 1021).error (generalMeanGrid j.val)+
      (generalMeanRows 1021).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1021).c)).2-
      (generalMeanRows 1021).J/2-(generalMeanRows 1021).error 4 := by
  have he : (generalMeanRows 1021).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1021) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1021)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1021

/-! Kernel-checked entropy margins for general spectral rectangle 1022. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1022
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6149300345) (.branch 2 (.leaf 5948393699) (.leaf 5755935120))) (.branch 5 (.branch 4 (.leaf 5571463434) (.leaf 5394549575)) (.branch 6 (.leaf 5224793771) (.leaf 5061823031)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4905288908) (.leaf 4754865484)) (.branch 10 (.leaf 4610247563) (.leaf 4471149047))) (.branch 13 (.branch 12 (.leaf 4337301453) (.leaf 4208452591)) (.branch 14 (.leaf 4084365347) (.leaf 3964816582))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3849596134) (.branch 17 (.leaf 3738505895) (.leaf 3631358976))) (.branch 20 (.branch 19 (.leaf 3527978942) (.leaf 3428199099)) (.branch 21 (.leaf 3331861854) (.leaf 3238818116)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3148926742) (.leaf 3062054034)) (.branch 25 (.leaf 2978073270) (.leaf 2896864263))) (.branch 28 (.branch 27 (.leaf 2818312969) (.leaf 2742311102)) (.branch 29 (.leaf 2668755798) (.leaf 2597549285)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2528598588) (.branch 32 (.leaf 2461815247) (.leaf 2397115059))) (.branch 35 (.branch 34 (.leaf 2334417832) (.leaf 2273647161)) (.branch 36 (.leaf 2214730215) (.leaf 2157597541)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2102182874) (.leaf 2048422968)) (.branch 40 (.leaf 1996257430) (.leaf 1945628570))) (.branch 43 (.branch 42 (.leaf 1896481255) (.leaf 1848762776)) (.branch 44 (.leaf 1802422723) (.leaf 1757412864))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1713687032) (.branch 47 (.leaf 1671201025) (.leaf 1629912503))) (.branch 50 (.branch 49 (.leaf 1589780894) (.leaf 1550767308)) (.branch 51 (.leaf 1512834456) (.leaf 1475946567)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1440069316) (.leaf 1405169759)) (.branch 55 (.leaf 1371216257) (.leaf 1338178426))) (.branch 58 (.branch 57 (.leaf 1306027068) (.leaf 1274734119)) (.branch 59 (.leaf 1244272600) (.leaf 1214616560))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1185741034) (.branch 62 (.leaf 1157621997) (.leaf 1130236321))) (.branch 65 (.branch 64 (.leaf 1103561735) (.leaf 1077576788)) (.branch 66 (.leaf 1052260810) (.leaf 1027593880)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1003556794) (.leaf 980131033)) (.branch 70 (.leaf 957298733) (.leaf 935042656))) (.branch 73 (.branch 72 (.leaf 913346168) (.leaf 892193210)) (.branch 74 (.leaf 871568274) (.leaf 851456382))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 831843061) (.branch 77 (.leaf 812714328) (.leaf 794056665))) (.branch 80 (.branch 79 (.leaf 775857001) (.leaf 758102697)) (.branch 81 (.leaf 740781526) (.leaf 723881658)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 707391645) (.leaf 691300403)) (.branch 85 (.leaf 675597204) (.leaf 660271656))) (.branch 88 (.branch 87 (.leaf 645313693) (.leaf 630713565)) (.branch 89 (.leaf 616461822) (.leaf 602549304)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 588967133) (.branch 92 (.leaf 575706699) (.leaf 562759652))) (.branch 95 (.branch 94 (.leaf 550117893) (.leaf 537773564)) (.branch 96 (.leaf 525719041) (.leaf 513946922)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 502450024) (.leaf 491221371)) (.branch 100 (.leaf 480254191) (.leaf 469541906))) (.branch 103 (.branch 102 (.leaf 459078125) (.leaf 448856641)) (.branch 104 (.leaf 438871420) (.leaf 429116601))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 419586484) (.leaf 410275529)) (.branch 108 (.leaf 401178351) (.leaf 392289709))) (.branch 111 (.branch 110 (.leaf 383604512) (.leaf 375117802)) (.branch 112 (.leaf 366824759) (.leaf 358720692)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 350801037) (.leaf 343061352)) (.branch 116 (.leaf 335497313) (.leaf 328104710))) (.branch 119 (.branch 118 (.leaf 320879445) (.leaf 313817529)) (.branch 120 (.leaf 306915076) (.leaf 300168301)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1022).prefactor = (1395067989242617/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1022).cutoff/(generalMeanRows 1022).c)).2 =
    (35035000380831/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1022).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1022).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1022).q*(generalMeanRows 1022).cutoff/2-2 = (167/81:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable333.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1022).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1022

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1022).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1022).criticalRate j.val*(generalMeanRows 1022).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1022).c*(generalMeanRows 1022).criticalPoint j.val)).2-
      (generalMeanRows 1022).J/2-(generalMeanRows 1022).error (generalMeanGrid j.val)+
      (generalMeanRows 1022).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1022).c)).2-
      (generalMeanRows 1022).J/2-(generalMeanRows 1022).error 4 := by
  have he : (generalMeanRows 1022).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1022) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1022)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1022

/-! Kernel-checked entropy margins for general spectral rectangle 1023. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1023
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6447331587) (.branch 2 (.leaf 6239263438) (.leaf 6039906906))) (.branch 5 (.branch 4 (.leaf 5848786229) (.leaf 5665458807)) (.branch 6 (.leaf 5489512291) (.leaf 5320561997)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5158248581) (.leaf 5002235966)) (.branch 10 (.leaf 4852209471) (.leaf 4707874130))) (.branch 13 (.branch 12 (.leaf 4568953169) (.leaf 4435186629)) (.branch 14 (.leaf 4306330115) (.leaf 4182153659))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4062440682) (.branch 17 (.leaf 3946987048) (.leaf 3835600199))) (.branch 20 (.branch 19 (.leaf 3728098362) (.leaf 3624309816)) (.branch 21 (.leaf 3524072230) (.leaf 3427232040)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3333643884) (.leaf 3243170078)) (.branch 25 (.leaf 3155680130) (.leaf 3071050292))) (.branch 28 (.branch 27 (.leaf 2989163143) (.leaf 2909907206)) (.branch 29 (.leaf 2833176588) (.leaf 2758870647)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2686893684) (.branch 32 (.leaf 2617154655) (.leaf 2549566901))) (.branch 35 (.branch 34 (.leaf 2484047895) (.leaf 2420519015)) (.branch 36 (.leaf 2358905318) (.leaf 2299135339)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2241140899) (.leaf 2184856927)) (.branch 40 (.leaf 2130221290) (.leaf 2077174636))) (.branch 43 (.branch 42 (.leaf 2025660248) (.leaf 1975623902)) (.branch 44 (.leaf 1927013740) (.leaf 1879780145))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1833875630) (.branch 47 (.leaf 1789254721) (.leaf 1745873865))) (.branch 50 (.branch 49 (.leaf 1703691326) (.leaf 1662667100)) (.branch 51 (.leaf 1622762825) (.leaf 1583941703)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1546168424) (.leaf 1509409093)) (.branch 55 (.leaf 1473631162) (.leaf 1438803366))) (.branch 58 (.branch 57 (.leaf 1404895665) (.leaf 1371879183)) (.branch 59 (.leaf 1339726156) (.leaf 1308409878))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1277904657) (.branch 62 (.leaf 1248185763) (.leaf 1219229392))) (.branch 65 (.branch 64 (.leaf 1191012615) (.leaf 1163513349)) (.branch 66 (.leaf 1136710310) (.leaf 1110582987)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1085111600) (.leaf 1060277075)) (.branch 70 (.leaf 1036061010) (.leaf 1012445647))) (.branch 73 (.branch 72 (.leaf 989413844) (.leaf 966949052)) (.branch 74 (.leaf 945035287) (.leaf 923657108))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 902799594) (.branch 77 (.leaf 882448324) (.leaf 862589355))) (.branch 80 (.branch 79 (.leaf 843209205) (.leaf 824294833)) (.branch 81 (.leaf 805833619) (.leaf 787813354)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 770222217) (.leaf 753048765)) (.branch 85 (.leaf 736281915) (.leaf 719910932))) (.branch 88 (.branch 87 (.leaf 703925416) (.leaf 688315289)) (.branch 89 (.leaf 673070779) (.leaf 658182418)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 643641020) (.branch 92 (.leaf 629437679) (.leaf 615563754))) (.branch 95 (.branch 94 (.leaf 602010860) (.leaf 588770862)) (.branch 96 (.leaf 575835862) (.leaf 563198194)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 550850412) (.leaf 538785287)) (.branch 100 (.leaf 526995796) (.leaf 515475115))) (.branch 103 (.branch 102 (.leaf 504216616) (.leaf 493213855)) (.branch 104 (.leaf 482460569) (.leaf 471950669))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 461678237) (.leaf 451637514)) (.branch 108 (.leaf 441822902) (.leaf 432228954))) (.branch 111 (.branch 110 (.leaf 422850371) (.leaf 413681996)) (.branch 112 (.leaf 404718811) (.leaf 395955932)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 387388605) (.leaf 379012202)) (.branch 116 (.leaf 370822214) (.leaf 362814253))) (.branch 119 (.branch 118 (.leaf 354984045) (.leaf 347327426)) (.branch 120 (.leaf 339840340) (.leaf 332518835)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1023).prefactor = (5764441011599659/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1023).cutoff/(generalMeanRows 1023).c)).2 =
    (178242496187913/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1023).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1023).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1023).q*(generalMeanRows 1023).c/2-2 = (27/32:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable332.value]
    have hcontinuation : (generalMeanRows 1023).q*(generalMeanRows 1023).cutoff/2-2 = (167/81:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable333.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1023).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1023

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1023).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1023).criticalRate j.val*(generalMeanRows 1023).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1023).c*(generalMeanRows 1023).criticalPoint j.val)).2-
      (generalMeanRows 1023).J/2-(generalMeanRows 1023).error (generalMeanGrid j.val)+
      (generalMeanRows 1023).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1023).c)).2-
      (generalMeanRows 1023).J/2-(generalMeanRows 1023).error 4 := by
  have he : (generalMeanRows 1023).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1023) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1023)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1023

/-! Kernel-checked entropy margins for general spectral rectangle 1024. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1024
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7200177256) (.branch 2 (.leaf 6989703488) (.leaf 6787357616))) (.branch 5 (.branch 4 (.leaf 6592721246) (.leaf 6405404588)) (.branch 6 (.leaf 6225043903) (.leaf 6051299223)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5883852334) (.leaf 5722404970)) (.branch 10 (.leaf 5566677194) (.leaf 5416405950))) (.branch 13 (.branch 12 (.leaf 5271343754) (.leaf 5131257518)) (.branch 14 (.leaf 4995927476) (.leaf 4865146222))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4738717829) (.branch 17 (.leaf 4616457043) (.leaf 4498188556))) (.branch 20 (.branch 19 (.leaf 4383746336) (.leaf 4272973010)) (.branch 21 (.leaf 4165719305) (.leaf 4061843529)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3961211093) (.leaf 3863694074)) (.branch 25 (.leaf 3769170805) (.leaf 3677525502))) (.branch 28 (.branch 27 (.leaf 3588647916) (.leaf 3502433007)) (.branch 29 (.leaf 3418780646) (.leaf 3337595338)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3258785957) (.branch 32 (.leaf 3182265509) (.leaf 3107950902))) (.branch 35 (.branch 34 (.leaf 3035762739) (.leaf 2965625118)) (.branch 36 (.leaf 2897465446) (.leaf 2831214270)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2766805111) (.leaf 2704174316)) (.branch 40 (.leaf 2643260910) (.leaf 2584006464))) (.branch 43 (.branch 42 (.leaf 2526354971) (.leaf 2470252722)) (.branch 44 (.leaf 2415648200) (.leaf 2362491967))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2310736572) (.branch 47 (.leaf 2260336450) (.leaf 2211247840))) (.branch 50 (.branch 49 (.leaf 2163428694) (.leaf 2116838604)) (.branch 51 (.leaf 2071438720) (.leaf 2027191688)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1984061574) (.leaf 1942013803)) (.branch 55 (.leaf 1901015102) (.leaf 1861033437))) (.branch 58 (.branch 57 (.leaf 1822037963) (.leaf 1783998970)) (.branch 59 (.leaf 1746887835) (.leaf 1710676972))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1675339795) (.branch 62 (.leaf 1640850666) (.leaf 1607184864))) (.branch 65 (.branch 64 (.leaf 1574318541) (.leaf 1542228688)) (.branch 66 (.leaf 1510893099) (.leaf 1480290340)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1450399716) (.leaf 1421201239)) (.branch 70 (.leaf 1392675606) (.leaf 1364804165))) (.branch 73 (.branch 72 (.leaf 1337568890) (.leaf 1310952361)) (.branch 74 (.leaf 1284937735) (.leaf 1259508724))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1234649577) (.branch 77 (.leaf 1210345055) (.leaf 1186580414))) (.branch 80 (.branch 79 (.leaf 1163341385) (.leaf 1140614155)) (.branch 81 (.leaf 1118385354) (.leaf 1096642031)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1075371645) (.leaf 1054562046)) (.branch 85 (.leaf 1034201463) (.leaf 1014278488))) (.branch 88 (.branch 87 (.leaf 994782063) (.leaf 975701468)) (.branch 89 (.leaf 957026310) (.leaf 938746506)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 920852280) (.branch 92 (.leaf 903334144) (.leaf 886182894))) (.branch 95 (.branch 94 (.leaf 869389595) (.leaf 852945576)) (.branch 96 (.leaf 836842417) (.leaf 821071944)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 805626216) (.leaf 790497522)) (.branch 100 (.leaf 775678369) (.leaf 761161477))) (.branch 103 (.branch 102 (.leaf 746939770) (.leaf 733006371)) (.branch 104 (.leaf 719354595) (.leaf 705977941))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 692870087) (.leaf 680024886)) (.branch 108 (.leaf 667436357) (.leaf 655098679))) (.branch 111 (.branch 110 (.leaf 643006192) (.leaf 631153384)) (.branch 112 (.leaf 619534892) (.leaf 608145495)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 596980107) (.leaf 586033779)) (.branch 116 (.leaf 575301689) (.leaf 564779141))) (.branch 119 (.branch 118 (.leaf 554461558) (.leaf 544344483)) (.branch 120 (.leaf 534423572) (.leaf 524694592)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1024).prefactor = (516911606153881/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1024).cutoff/(generalMeanRows 1024).c)).2 =
    (294192581600173/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1024).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1024).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1024).q*(generalMeanRows 1024).c/2-2 = (1377/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable318.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1024).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1024

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1024).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1024).criticalRate j.val*(generalMeanRows 1024).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1024).c*(generalMeanRows 1024).criticalPoint j.val)).2-
      (generalMeanRows 1024).J/2-(generalMeanRows 1024).error (generalMeanGrid j.val)+
      (generalMeanRows 1024).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1024).c)).2-
      (generalMeanRows 1024).J/2-(generalMeanRows 1024).error 4 := by
  have he : (generalMeanRows 1024).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1024) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1024)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1024

/-! Kernel-checked entropy margins for general spectral rectangle 1025. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1025
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6960001344) (.branch 2 (.leaf 6754990104) (.leaf 6557969092))) (.branch 5 (.branch 4 (.leaf 6368524039) (.leaf 6186269032)) (.branch 6 (.leaf 6010843990) (.leaf 5841912413)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5679159387) (.leaf 5522289798)) (.branch 10 (.leaf 5371026730) (.leaf 5225110029))) (.branch 13 (.branch 12 (.leaf 5084295007) (.leaf 4948351274)) (.branch 14 (.leaf 4817061680) (.leaf 4690221349))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4567636812) (.branch 17 (.leaf 4449125205) (.leaf 4334513545))) (.branch 20 (.branch 19 (.leaf 4223638064) (.leaf 4116343598)) (.branch 21 (.leaf 4012483028) (.leaf 3911916765)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3814512272) (.leaf 3720143634)) (.branch 25 (.leaf 3628691144) (.leaf 3540040936))) (.branch 28 (.branch 27 (.leaf 3454084633) (.leaf 3370719030)) (.branch 29 (.leaf 3289845790) (.leaf 3211371168)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3135205756) (.branch 32 (.leaf 3061264233) (.leaf 2989465149))) (.branch 35 (.branch 34 (.leaf 2919730709) (.leaf 2851986577)) (.branch 36 (.leaf 2786161695) (.leaf 2722188107)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2660000799) (.leaf 2599537546)) (.branch 40 (.leaf 2540738774) (.leaf 2483547420))) (.branch 43 (.branch 42 (.leaf 2427908809) (.leaf 2373770539)) (.branch 44 (.leaf 2321082362) (.leaf 2269796085))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2219865469) (.branch 47 (.leaf 2171246133) (.leaf 2123895471))) (.branch 50 (.branch 49 (.leaf 2077772563) (.leaf 2032838100)) (.branch 51 (.leaf 1989054305) (.leaf 1946384869)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1904794878) (.leaf 1864250753)) (.branch 55 (.leaf 1824720188) (.leaf 1786172094))) (.branch 58 (.branch 57 (.leaf 1748576547) (.leaf 1711904733)) (.branch 59 (.leaf 1676128902) (.leaf 1641222321))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1607159228) (.branch 62 (.leaf 1573914797) (.leaf 1541465089))) (.branch 65 (.branch 64 (.leaf 1509787021) (.leaf 1478858329)) (.branch 66 (.leaf 1448657532) (.leaf 1419163899)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1390357420) (.leaf 1362218778)) (.branch 70 (.leaf 1334729316) (.leaf 1307871013))) (.branch 73 (.branch 72 (.leaf 1281626458) (.leaf 1255978828)) (.branch 74 (.leaf 1230911860) (.leaf 1206409831))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1182457539) (.branch 77 (.leaf 1159040277) (.leaf 1136143821))) (.branch 80 (.branch 79 (.leaf 1113754405) (.leaf 1091858707)) (.branch 81 (.leaf 1070443831) (.leaf 1049497291)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1029006993) (.leaf 1008961226)) (.branch 85 (.leaf 989348642) (.leaf 970158244))) (.branch 88 (.branch 87 (.leaf 951379377) (.leaf 933001708)) (.branch 89 (.leaf 915015223) (.leaf 897410205)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 880177235) (.branch 92 (.leaf 863307171) (.leaf 846791146))) (.branch 95 (.branch 94 (.leaf 830620550) (.leaf 814787031)) (.branch 96 (.leaf 799282475) (.leaf 784099009)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 769228982) (.leaf 754664964)) (.branch 100 (.leaf 740399736) (.leaf 726426285))) (.branch 103 (.branch 102 (.leaf 712737793) (.leaf 699327634)) (.branch 104 (.leaf 686189367) (.leaf 673316726))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 660703621) (.leaf 648344125)) (.branch 108 (.leaf 636232476) (.leaf 624363063))) (.branch 111 (.branch 110 (.leaf 612730430) (.leaf 601329264)) (.branch 112 (.leaf 590154395) (.leaf 579200787)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 568463540) (.leaf 557937877)) (.branch 116 (.leaf 547619151) (.leaf 537502831))) (.branch 119 (.branch 118 (.leaf 527584503) (.leaf 517859867)) (.branch 120 (.leaf 508324732) (.leaf 498975013)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1025).prefactor = (638490242709709/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1025).cutoff/(generalMeanRows 1025).c)).2 =
    (304849876074161/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1025).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1025).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1025).q*(generalMeanRows 1025).c/2-2 = (7/10:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable043.value]
    have hcontinuation : (generalMeanRows 1025).q*(generalMeanRows 1025).cutoff/2-2 = (128/77:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable182.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1025).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1025

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1025).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1025).criticalRate j.val*(generalMeanRows 1025).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1025).c*(generalMeanRows 1025).criticalPoint j.val)).2-
      (generalMeanRows 1025).J/2-(generalMeanRows 1025).error (generalMeanGrid j.val)+
      (generalMeanRows 1025).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1025).c)).2-
      (generalMeanRows 1025).J/2-(generalMeanRows 1025).error 4 := by
  have he : (generalMeanRows 1025).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1025) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1025)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1025

/-! Kernel-checked entropy margins for general spectral rectangle 1026. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1026
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6827052053) (.branch 2 (.leaf 6627434806) (.leaf 6435639757))) (.branch 5 (.branch 4 (.leaf 6251257774) (.leaf 6073907813)) (.branch 6 (.leaf 5903234429) (.leaf 5738905549)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5580610501) (.leaf 5428058243)) (.branch 10 (.leaf 5280975784) (.leaf 5139106757))) (.branch 13 (.branch 12 (.leaf 5002210136) (.leaf 4870059078)) (.branch 14 (.leaf 4742439870) (.leaf 4619150978))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4500002180) (.branch 17 (.leaf 4384813772) (.leaf 4273415847))) (.branch 20 (.branch 19 (.leaf 4165647634) (.leaf 4061356893)) (.branch 21 (.leaf 3960399355) (.leaf 3862638210)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3767943639) (.leaf 3676192373)) (.branch 25 (.leaf 3587267294) (.leaf 3501057059))) (.branch 28 (.branch 27 (.leaf 3417455759) (.leaf 3336362596)) (.branch 29 (.leaf 3257681584) (.leaf 3181321276)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3107194504) (.branch 32 (.leaf 3035218137) (.leaf 2965312861))) (.branch 35 (.branch 34 (.leaf 2897402967) (.leaf 2831416154)) (.branch 36 (.leaf 2767283351) (.leaf 2704938540)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2644318597) (.leaf 2585363144)) (.branch 40 (.leaf 2528014401) (.leaf 2472217062))) (.branch 43 (.branch 42 (.leaf 2417918162) (.leaf 2365066963)) (.branch 44 (.leaf 2313614843) (.leaf 2263515191))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2214723308) (.branch 47 (.leaf 2167196317) (.leaf 2120893073))) (.branch 50 (.branch 49 (.leaf 2075774079) (.leaf 2031801412)) (.branch 51 (.leaf 1988938645) (.leaf 1947150781)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1906404183) (.leaf 1866666514)) (.branch 55 (.leaf 1827906678) (.leaf 1790094759))) (.branch 58 (.branch 57 (.leaf 1753201976) (.leaf 1717200626)) (.branch 59 (.leaf 1682064038) (.leaf 1647766526))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1614283351) (.branch 62 (.leaf 1581590673) (.leaf 1549665517))) (.branch 65 (.branch 64 (.leaf 1518485733) (.leaf 1488029962)) (.branch 66 (.leaf 1458277605) (.leaf 1429208784)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1400804320) (.leaf 1373045699)) (.branch 70 (.leaf 1345915043) (.leaf 1319395091))) (.branch 73 (.branch 72 (.leaf 1293469165) (.leaf 1268121154)) (.branch 74 (.leaf 1243335484) (.leaf 1219097104))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1195391459) (.branch 77 (.leaf 1172204472) (.leaf 1149522527))) (.branch 80 (.branch 79 (.leaf 1127332449) (.leaf 1105621488)) (.branch 81 (.leaf 1084377302) (.leaf 1063587940)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1043241830) (.leaf 1023327762)) (.branch 85 (.leaf 1003834876) (.leaf 984752647))) (.branch 88 (.branch 87 (.leaf 966070873) (.leaf 947779666)) (.branch 89 (.leaf 929869436) (.leaf 912330882)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 895154981) (.branch 92 (.leaf 878332981) (.leaf 861856386))) (.branch 95 (.branch 94 (.leaf 845716949) (.leaf 829906666)) (.branch 96 (.leaf 814417763) (.leaf 799242689)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 784374110) (.leaf 769804903)) (.branch 100 (.leaf 755528140) (.leaf 741537094))) (.branch 103 (.branch 102 (.leaf 727825220) (.leaf 714386158)) (.branch 104 (.leaf 701213722) (.leaf 688301894))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 675644821) (.leaf 663236807)) (.branch 108 (.leaf 651072311) (.leaf 639145937))) (.branch 111 (.branch 110 (.leaf 627452435) (.leaf 615986690)) (.branch 112 (.leaf 604743725) (.leaf 593718690)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 582906860) (.leaf 572303635)) (.branch 116 (.leaf 561904529) (.leaf 551705172))) (.branch 119 (.branch 118 (.leaf 541701305) (.leaf 531888774)) (.branch 120 (.leaf 522263532) (.leaf 512821629)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1026).prefactor = (315065567525113/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1026).cutoff/(generalMeanRows 1026).c)).2 =
    (161737312955933/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1026).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1026).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1026).q*(generalMeanRows 1026).c/2-2 = (2767/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable329.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1026).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1026

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1026).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1026).criticalRate j.val*(generalMeanRows 1026).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1026).c*(generalMeanRows 1026).criticalPoint j.val)).2-
      (generalMeanRows 1026).J/2-(generalMeanRows 1026).error (generalMeanGrid j.val)+
      (generalMeanRows 1026).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1026).c)).2-
      (generalMeanRows 1026).J/2-(generalMeanRows 1026).error 4 := by
  have he : (generalMeanRows 1026).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1026) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1026)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1026

/-! Kernel-checked entropy margins for general spectral rectangle 1027. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1027
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6598247025) (.branch 2 (.leaf 6404471173) (.leaf 6218351547))) (.branch 5 (.branch 4 (.leaf 6039484354) (.leaf 5867493601)) (.branch 6 (.leaf 5702028636) (.leaf 5542761952)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5389387237) (.leaf 5241617629)) (.branch 10 (.leaf 5099184147) (.leaf 4961834283))) (.branch 13 (.branch 12 (.leaf 4829330730) (.leaf 4701450236)) (.branch 14 (.leaf 4577982563) (.leaf 4458729537))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4343504194) (.branch 17 (.leaf 4232129989) (.leaf 4124440083))) (.branch 20 (.branch 19 (.leaf 4020276685) (.leaf 3919490450)) (.branch 21 (.leaf 3821939925) (.leaf 3727491042)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3636016643) (.leaf 3547396057)) (.branch 25 (.leaf 3461514689) (.leaf 3378263658))) (.branch 28 (.branch 27 (.leaf 3297539447) (.leaf 3219243590)) (.branch 29 (.leaf 3143282374) (.leaf 3069566560)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2998011135) (.branch 32 (.leaf 2928535065) (.leaf 2861061077))) (.branch 35 (.branch 34 (.leaf 2795515450) (.leaf 2731827820)) (.branch 36 (.leaf 2669930998) (.leaf 2609760800)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2551255887) (.leaf 2494357617)) (.branch 40 (.leaf 2439009901) (.leaf 2385159076))) (.branch 43 (.branch 42 (.leaf 2332753775) (.leaf 2281744816)) (.branch 44 (.leaf 2232085089) (.leaf 2183729452))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2136634638) (.branch 47 (.leaf 2090759156) (.leaf 2046063212))) (.branch 50 (.branch 49 (.leaf 2002508622) (.leaf 1960058737)) (.branch 51 (.leaf 1918678368) (.leaf 1878333720)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1838992324) (.leaf 1800622978)) (.branch 55 (.leaf 1763195685) (.leaf 1726681600))) (.branch 58 (.branch 57 (.leaf 1691052979) (.leaf 1656283124)) (.branch 59 (.leaf 1622346342) (.leaf 1589217895))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1556873963) (.branch 62 (.leaf 1525291599) (.leaf 1494448692))) (.branch 65 (.branch 64 (.leaf 1464323931) (.leaf 1434896772)) (.branch 66 (.leaf 1406147403) (.leaf 1378056711)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1350606259) (.leaf 1323778251)) (.branch 70 (.leaf 1297555506) (.leaf 1271921436))) (.branch 73 (.branch 72 (.leaf 1246860020) (.leaf 1222355777)) (.branch 74 (.leaf 1198393751) (.leaf 1174959483))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1152038993) (.branch 77 (.leaf 1129618765) (.leaf 1107685722))) (.branch 80 (.branch 79 (.leaf 1086227213) (.leaf 1065230995)) (.branch 81 (.leaf 1044685216) (.leaf 1024578402)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1004899439) (.leaf 985637565)) (.branch 85 (.leaf 966782350) (.leaf 948323687))) (.branch 88 (.branch 87 (.leaf 930251780) (.leaf 912557131)) (.branch 89 (.leaf 895230528) (.leaf 878263040)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 861645997) (.branch 92 (.leaf 845370991) (.leaf 829429859))) (.branch 95 (.branch 94 (.leaf 813814677) (.leaf 798517750)) (.branch 96 (.leaf 783531608) (.leaf 768848993)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 754462852) (.leaf 740366335)) (.branch 100 (.leaf 726552782) (.leaf 713015719))) (.branch 103 (.branch 102 (.leaf 699748851) (.leaf 686746058)) (.branch 104 (.leaf 674001386) (.leaf 661509042))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 649263392) (.leaf 637258950)) (.branch 108 (.leaf 625490379) (.leaf 613952482))) (.branch 111 (.branch 110 (.leaf 602640198) (.leaf 591548600)) (.branch 112 (.leaf 580672889) (.leaf 570008389)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 559550544) (.leaf 549294915)) (.branch 116 (.leaf 539237176) (.leaf 529373110))) (.branch 119 (.branch 118 (.leaf 519698604) (.leaf 510209649)) (.branch 120 (.leaf 500902337) (.leaf 491772852)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1027).prefactor = (1242246232322387/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1027).cutoff/(generalMeanRows 1027).c)).2 =
    (336291401908981/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1027).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1027).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1027).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1027

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1027).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1027).criticalRate j.val*(generalMeanRows 1027).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1027).c*(generalMeanRows 1027).criticalPoint j.val)).2-
      (generalMeanRows 1027).J/2-(generalMeanRows 1027).error (generalMeanGrid j.val)+
      (generalMeanRows 1027).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1027).c)).2-
      (generalMeanRows 1027).J/2-(generalMeanRows 1027).error 4 := by
  have he : (generalMeanRows 1027).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1027) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1027)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1027

/-! Kernel-checked entropy margins for general spectral rectangle 1028. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1028
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6378123945) (.branch 2 (.leaf 6190323276) (.leaf 6009999741))) (.branch 5 (.branch 4 (.leaf 5836755481) (.leaf 5670220133)) (.branch 6 (.leaf 5510048394) (.leaf 5355917866)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5207527121) (.leaf 5064593982)) (.branch 10 (.leaf 4926853966) (.leaf 4794058897))) (.branch 13 (.branch 12 (.leaf 4665975644) (.leaf 4542384987)) (.branch 14 (.leaf 4423080582) (.leaf 4307868026))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4196564004) (.branch 17 (.leaf 4088995510) (.leaf 3984999134))) (.branch 20 (.branch 19 (.leaf 3884420415) (.leaf 3787113238)) (.branch 21 (.leaf 3692939288) (.leaf 3601767542)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3513473808) (.leaf 3427940288)) (.branch 25 (.leaf 3345055185) (.leaf 3264712336))) (.branch 28 (.branch 27 (.leaf 3186810868) (.leaf 3111254881)) (.branch 29 (.leaf 3037953159) (.leaf 2966818893)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2897769427) (.branch 32 (.leaf 2830726020) (.leaf 2765613628))) (.branch 35 (.branch 34 (.leaf 2702360697) (.leaf 2640898965)) (.branch 36 (.leaf 2581163290) (.leaf 2523091474)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2466624108) (.leaf 2411704423)) (.branch 40 (.leaf 2358278152) (.leaf 2306293398))) (.branch 43 (.branch 42 (.leaf 2255700510) (.leaf 2206451972)) (.branch 44 (.leaf 2158502290) (.leaf 2111807892))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2066327031) (.branch 47 (.leaf 2022019695) (.leaf 1978847522))) (.branch 50 (.branch 49 (.leaf 1936773717) (.leaf 1895762978)) (.branch 51 (.leaf 1855781423) (.leaf 1816796525)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1778777041) (.leaf 1741692959)) (.branch 55 (.leaf 1705515437) (.leaf 1670216746))) (.branch 58 (.branch 57 (.leaf 1635770224) (.leaf 1602150223)) (.branch 59 (.leaf 1569332066) (.leaf 1537292000))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1506007156) (.branch 62 (.leaf 1475455509) (.leaf 1445615843))) (.branch 65 (.branch 64 (.leaf 1416467711) (.leaf 1387991406)) (.branch 66 (.leaf 1360167926) (.leaf 1332978944)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1306406779) (.leaf 1280434369)) (.branch 70 (.leaf 1255045246) (.leaf 1230223507))) (.branch 73 (.branch 72 (.leaf 1205953796) (.leaf 1182221276)) (.branch 74 (.leaf 1159011611) (.leaf 1136310945))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1114105880) (.branch 77 (.leaf 1092383460) (.leaf 1071131154))) (.branch 80 (.branch 79 (.leaf 1050336837) (.leaf 1029988772)) (.branch 81 (.leaf 1010075601) (.leaf 990586323)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 971510287) (.leaf 952837170)) (.branch 85 (.leaf 934556975) (.leaf 916660007))) (.branch 88 (.branch 87 (.leaf 899136873) (.leaf 881978462)) (.branch 89 (.leaf 865175937) (.leaf 848720726)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 832604513) (.branch 92 (.leaf 816819225) (.leaf 801357027))) (.branch 95 (.branch 94 (.leaf 786210310) (.leaf 771371686)) (.branch 96 (.leaf 756833977) (.leaf 742590212)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 728633613) (.leaf 714957596)) (.branch 100 (.leaf 701555757) (.leaf 688421872))) (.branch 103 (.branch 102 (.leaf 675549886) (.leaf 662933911)) (.branch 104 (.leaf 650568217) (.leaf 638447229))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 626565522) (.leaf 614917812)) (.branch 108 (.leaf 603498959) (.leaf 592303955))) (.branch 111 (.branch 110 (.leaf 581327922) (.leaf 570566111)) (.branch 112 (.leaf 560013892) (.leaf 549666755)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 539520306) (.leaf 529570259)) (.branch 116 (.leaf 519812438) (.leaf 510242771))) (.branch 119 (.branch 118 (.leaf 500857285) (.leaf 491652107)) (.branch 120 (.leaf 482623458) (.leaf 473767652)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1028).prefactor = (1223074607996291/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1028).cutoff/(generalMeanRows 1028).c)).2 =
    (8757806253773/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1028).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1028).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1028).q*(generalMeanRows 1028).cutoff/2-2 = (203/110:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable183.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1028).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1028

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1028).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1028).criticalRate j.val*(generalMeanRows 1028).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1028).c*(generalMeanRows 1028).criticalPoint j.val)).2-
      (generalMeanRows 1028).J/2-(generalMeanRows 1028).error (generalMeanGrid j.val)+
      (generalMeanRows 1028).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1028).c)).2-
      (generalMeanRows 1028).J/2-(generalMeanRows 1028).error 4 := by
  have he : (generalMeanRows 1028).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1028) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1028)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1028

/-! Kernel-checked entropy margins for general spectral rectangle 1029. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1029
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5989842909) (.branch 2 (.leaf 5796934605) (.leaf 5611916718))) (.branch 5 (.branch 4 (.leaf 5434371533) (.leaf 5263909968)) (.branch 6 (.leaf 5100169049) (.leaf 4942809670)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4791514590) (.leaf 4645986640)) (.branch 10 (.leaf 4505947117) (.leaf 4371134333))) (.branch 13 (.branch 12 (.leaf 4241302311) (.leaf 4116219604)) (.branch 14 (.leaf 3995668222) (.leaf 3879442658))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3767349004) (.branch 17 (.leaf 3659204139) (.leaf 3554834989))) (.branch 20 (.branch 19 (.leaf 3454077854) (.leaf 3356777781)) (.branch 21 (.leaf 3262787994) (.leaf 3171969373)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3084189960) (.leaf 2999324521)) (.branch 25 (.leaf 2917254125) (.leaf 2837865765))) (.branch 28 (.branch 27 (.leaf 2761052000) (.leaf 2686710629)) (.branch 29 (.leaf 2614744379) (.leaf 2545060628)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2477571132) (.branch 32 (.leaf 2412191783) (.leaf 2348842376))) (.branch 35 (.branch 34 (.leaf 2287446392) (.leaf 2227930802)) (.branch 36 (.leaf 2170225872) (.leaf 2114264990)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2059984501) (.leaf 2007323550)) (.branch 40 (.leaf 1956223938) (.leaf 1906629984))) (.branch 43 (.branch 42 (.leaf 1858488396) (.leaf 1811748153)) (.branch 44 (.leaf 1766360387) (.leaf 1722278279))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1679456958) (.branch 47 (.leaf 1637853402) (.leaf 1597426353))) (.branch 50 (.branch 49 (.leaf 1558136230) (.leaf 1519945048)) (.branch 51 (.leaf 1482816342) (.leaf 1446715100)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1411607689) (.leaf 1377461796)) (.branch 55 (.leaf 1344246362) (.leaf 1311931531))) (.branch 58 (.branch 57 (.leaf 1280488592) (.leaf 1249889925)) (.branch 59 (.leaf 1220108958) (.leaf 1191120115))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1162898776) (.branch 62 (.leaf 1135421233) (.leaf 1108664650))) (.branch 65 (.branch 64 (.leaf 1082607026) (.leaf 1057227160)) (.branch 66 (.leaf 1032504616) (.leaf 1008419689)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 984953378) (.leaf 962087351)) (.branch 70 (.leaf 939803923) (.leaf 918086025))) (.branch 73 (.branch 72 (.leaf 896917182) (.leaf 876281484)) (.branch 74 (.leaf 856163570) (.leaf 836548599))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 817422233) (.branch 77 (.leaf 798770615) (.leaf 780580353))) (.branch 80 (.branch 79 (.leaf 762838498) (.leaf 745532528)) (.branch 81 (.leaf 728650333) (.leaf 712180197)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 696110784) (.leaf 680431123)) (.branch 85 (.leaf 665130595) (.leaf 650198917))) (.branch 88 (.branch 87 (.leaf 635626132) (.leaf 621402599)) (.branch 89 (.leaf 607518974) (.leaf 593966208)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 580735528) (.branch 92 (.leaf 567818432) (.leaf 555206680))) (.branch 95 (.branch 94 (.leaf 542892279) (.leaf 530867480)) (.branch 96 (.leaf 519124765) (.leaf 507656844)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 496456640) (.leaf 485517288)) (.branch 100 (.leaf 474832123) (.leaf 464394677))) (.branch 103 (.branch 102 (.leaf 454198668) (.leaf 444237998)) (.branch 104 (.leaf 434506744) (.leaf 424999152))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 415709633) (.leaf 406632756)) (.branch 108 (.leaf 397763244) (.leaf 389095967))) (.branch 111 (.branch 110 (.leaf 380625940) (.leaf 372348316)) (.branch 112 (.leaf 364258382) (.leaf 356351554)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 348623376) (.leaf 341069513)) (.branch 116 (.leaf 333685745) (.leaf 326467971))) (.branch 119 (.branch 118 (.leaf 319412197) (.leaf 312514537)) (.branch 120 (.leaf 305771209) (.leaf 299178532)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1029).prefactor = (5094252476708089/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1029).cutoff/(generalMeanRows 1029).c)).2 =
    (304849876074161/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1029).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1029).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1029).q*(generalMeanRows 1029).c/2-2 = (167/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable082.value]
    have hcontinuation : (generalMeanRows 1029).q*(generalMeanRows 1029).cutoff/2-2 = (203/110:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable183.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1029).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1029

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1029).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1029).criticalRate j.val*(generalMeanRows 1029).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1029).c*(generalMeanRows 1029).criticalPoint j.val)).2-
      (generalMeanRows 1029).J/2-(generalMeanRows 1029).error (generalMeanGrid j.val)+
      (generalMeanRows 1029).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1029).c)).2-
      (generalMeanRows 1029).J/2-(generalMeanRows 1029).error 4 := by
  have he : (generalMeanRows 1029).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1029) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1029)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1029

/-! Kernel-checked entropy margins for general spectral rectangle 1030. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1030
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6035547785) (.branch 2 (.leaf 5848051980) (.leaf 5668186210))) (.branch 5 (.branch 4 (.leaf 5495542180) (.leaf 5329739807)) (.branch 6 (.leaf 5170424734) (.leaf 5017266118)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4869954659) (.leaf 4728200829)) (.branch 10 (.leaf 4591733287) (.leaf 4460297447))) (.branch 13 (.branch 12 (.leaf 4333654190) (.leaf 4211578695)) (.branch 14 (.leaf 4093859381) (.leaf 3980296943))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3870703477) (.branch 17 (.leaf 3764901676) (.leaf 3662724103))) (.branch 20 (.branch 19 (.leaf 3564012517) (.leaf 3468617260)) (.branch 21 (.leaf 3376396692) (.leaf 3287216668)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3200950059) (.leaf 3117476314)) (.branch 25 (.leaf 3036681042) (.leaf 2958455642))) (.branch 28 (.branch 27 (.leaf 2882696945) (.leaf 2809306892)) (.branch 29 (.leaf 2738192229) (.leaf 2669264229)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2602438427) (.branch 32 (.leaf 2537634375) (.leaf 2474775417))) (.branch 35 (.branch 34 (.leaf 2413788477) (.leaf 2354603858)) (.branch 36 (.leaf 2297155055) (.leaf 2241378588)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2187213831) (.leaf 2134602864)) (.branch 40 (.leaf 2083490329) (.leaf 2033823297))) (.branch 43 (.branch 42 (.leaf 1985551138) (.leaf 1938625407)) (.branch 44 (.leaf 1892999730) (.leaf 1848629698))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1805472770) (.branch 47 (.leaf 1763488182) (.leaf 1722636852))) (.branch 50 (.branch 49 (.leaf 1682881306) (.leaf 1644185594)) (.branch 51 (.leaf 1606515219) (.leaf 1569837064)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1534119332) (.leaf 1499331477)) (.branch 55 (.leaf 1465444151) (.leaf 1432429145))) (.branch 58 (.branch 57 (.leaf 1400259337) (.leaf 1368908642)) (.branch 59 (.leaf 1338351965) (.leaf 1308565157))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1279524970) (.branch 62 (.leaf 1251209019) (.leaf 1223595742))) (.branch 65 (.branch 64 (.leaf 1196664367) (.leaf 1170394874)) (.branch 66 (.leaf 1144767963) (.leaf 1119765024)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1095368106) (.leaf 1071559892)) (.branch 70 (.leaf 1048323666) (.leaf 1025643297))) (.branch 73 (.branch 72 (.leaf 1003503204) (.leaf 981888343)) (.branch 74 (.leaf 960784177) (.leaf 940176661))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 920052217) (.branch 77 (.leaf 900397721) (.leaf 881200479))) (.branch 80 (.branch 79 (.leaf 862448214) (.leaf 844129047)) (.branch 81 (.leaf 826231483) (.leaf 808744394)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 791657008) (.leaf 774958892)) (.branch 85 (.leaf 758639941) (.leaf 742690364))) (.branch 88 (.branch 87 (.leaf 727100673) (.leaf 711861674)) (.branch 89 (.leaf 696964450) (.leaf 682400359)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 668161014) (.branch 92 (.leaf 654238283) (.leaf 640624275))) (.branch 95 (.branch 94 (.leaf 627311331) (.leaf 614292017)) (.branch 96 (.leaf 601559117) (.leaf 589105623)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 576924728) (.leaf 565009822)) (.branch 100 (.leaf 553354481) (.leaf 541952464))) (.branch 103 (.branch 102 (.leaf 530797703) (.leaf 519884302)) (.branch 104 (.leaf 509206527) (.leaf 498758803))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 488535707) (.leaf 478531966)) (.branch 108 (.leaf 468742446) (.leaf 459162156))) (.branch 111 (.branch 110 (.leaf 449786236) (.leaf 440609956)) (.branch 112 (.leaf 431628711) (.leaf 422838019)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 414233514) (.leaf 405810944)) (.branch 116 (.leaf 397566170) (.leaf 389495155))) (.branch 119 (.branch 118 (.leaf 381593970) (.leaf 373858785)) (.branch 120 (.leaf 366285867) (.leaf 358871578)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1030).prefactor = (4997811930880511/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1030).cutoff/(generalMeanRows 1030).c)).2 =
    (84944556826531/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1030).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1030).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1030).q*(generalMeanRows 1030).c/2-2 = (3147/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable328.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1030).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1030

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1030).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1030).criticalRate j.val*(generalMeanRows 1030).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1030).c*(generalMeanRows 1030).criticalPoint j.val)).2-
      (generalMeanRows 1030).J/2-(generalMeanRows 1030).error (generalMeanGrid j.val)+
      (generalMeanRows 1030).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1030).c)).2-
      (generalMeanRows 1030).J/2-(generalMeanRows 1030).error 4 := by
  have he : (generalMeanRows 1030).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1030) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1030)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1030

/-! Kernel-checked entropy margins for general spectral rectangle 1031. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1031
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5912331204) (.branch 2 (.leaf 5731203594) (.leaf 5557463712))) (.branch 5 (.branch 4 (.leaf 5390712044) (.leaf 5230576870)) (.branch 6 (.leaf 5076711816) (.leaf 4928793674)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4786520461) (.leaf 4649609671)) (.branch 10 (.leaf 4517796714) (.leaf 4390833498))) (.branch 13 (.branch 12 (.leaf 4268487162) (.leaf 4150538918)) (.branch 14 (.leaf 4036783007) (.leaf 3927025746))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3821084663) (.branch 17 (.leaf 3718787701) (.leaf 3619972502))) (.branch 20 (.branch 19 (.leaf 3524485737) (.leaf 3432182502)) (.branch 21 (.leaf 3342925755) (.leaf 3256585806)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3173039840) (.leaf 3092171478)) (.branch 25 (.leaf 3013870375) (.leaf 2938031843))) (.branch 28 (.branch 27 (.leaf 2864556505) (.leaf 2793349973)) (.branch 29 (.leaf 2724322550) (.leaf 2657388949)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2592468040) (.branch 32 (.leaf 2529482601) (.leaf 2468359102))) (.branch 35 (.branch 34 (.leaf 2409027490) (.leaf 2351420994)) (.branch 36 (.leaf 2295475944) (.leaf 2241131600)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2188329988) (.leaf 2137015755)) (.branch 40 (.leaf 2087136025) (.leaf 2038640270))) (.branch 43 (.branch 42 (.leaf 1991480180) (.leaf 1945609557)) (.branch 44 (.leaf 1900984194) (.leaf 1857561783))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1815301810) (.branch 47 (.leaf 1774165468) (.leaf 1734115572))) (.branch 50 (.branch 49 (.leaf 1695116473) (.leaf 1657133991)) (.branch 51 (.leaf 1620135332) (.leaf 1584089029)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1548964875) (.leaf 1514733861)) (.branch 55 (.leaf 1481368121) (.leaf 1448840875))) (.branch 58 (.branch 57 (.leaf 1417126384) (.leaf 1386199893)) (.branch 59 (.leaf 1356037592) (.leaf 1326616573))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1297914781) (.branch 62 (.leaf 1269910985) (.leaf 1242584735))) (.branch 65 (.branch 64 (.leaf 1215916329) (.leaf 1189886779)) (.branch 66 (.leaf 1164477780) (.leaf 1139671682)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1115451456) (.leaf 1091800675)) (.branch 70 (.leaf 1068703483) (.leaf 1046144569))) (.branch 73 (.branch 72 (.leaf 1024109151) (.leaf 1002582947)) (.branch 74 (.leaf 981552158) (.leaf 961003447))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 940923919) (.branch 77 (.leaf 921301105) (.leaf 902122943))) (.branch 80 (.branch 79 (.leaf 883377763) (.leaf 865054269)) (.branch 81 (.leaf 847141528) (.leaf 829628953)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 812506290) (.leaf 795763604)) (.branch 85 (.leaf 779391269) (.leaf 763379956))) (.branch 88 (.branch 87 (.leaf 747720620) (.leaf 732404490)) (.branch 89 (.leaf 717423058) (.leaf 702768071)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 688431523) (.branch 92 (.leaf 674405639) (.leaf 660682876))) (.branch 95 (.branch 94 (.leaf 647255906) (.leaf 634117616)) (.branch 96 (.leaf 621261093) (.leaf 608679624)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 596366682) (.leaf 584315927)) (.branch 100 (.leaf 572521193) (.leaf 560976486))) (.branch 103 (.branch 102 (.leaf 549675975) (.leaf 538613990)) (.branch 104 (.leaf 527785015) (.leaf 517183683))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 506804769) (.leaf 496643190)) (.branch 108 (.leaf 486693996) (.leaf 476952367))) (.branch 111 (.branch 110 (.leaf 467413610) (.leaf 458073154)) (.branch 112 (.leaf 448926547) (.leaf 439969450)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 431197636) (.leaf 422606986)) (.branch 116 (.leaf 414193484) (.leaf 405953215))) (.branch 119 (.branch 118 (.leaf 397882364) (.leaf 389977210)) (.branch 120 (.leaf 382234123) (.leaf 374649564)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1031).prefactor = (979854774001817/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1031).cutoff/(generalMeanRows 1031).c)).2 =
    (72611852432017/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1031).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1031).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1031).q*(generalMeanRows 1031).cutoff/2-2 = (328/165:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable000.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1031).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1031

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1031).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1031).criticalRate j.val*(generalMeanRows 1031).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1031).c*(generalMeanRows 1031).criticalPoint j.val)).2-
      (generalMeanRows 1031).J/2-(generalMeanRows 1031).error (generalMeanGrid j.val)+
      (generalMeanRows 1031).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1031).c)).2-
      (generalMeanRows 1031).J/2-(generalMeanRows 1031).error 4 := by
  have he : (generalMeanRows 1031).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1031) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1031)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1031

/-! Kernel-checked entropy margins for general spectral rectangle 1032. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1032
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5608268285) (.branch 2 (.leaf 5423162798) (.leaf 5245798633))) (.branch 5 (.branch 4 (.leaf 5075758476) (.leaf 4912653840)) (.branch 6 (.leaf 4756122531) (.leaf 4605826398)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4461449325) (.leaf 4322695423)) (.branch 10 (.leaf 4189287416) (.leaf 4060965176))) (.branch 13 (.branch 12 (.leaf 3937484410) (.leaf 3818615464)) (.branch 14 (.leaf 3704142242) (.leaf 3593861218))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3487580544) (.branch 17 (.leaf 3385119224) (.leaf 3286306371))) (.branch 20 (.branch 19 (.leaf 3190980518) (.leaf 3098988986)) (.branch 21 (.leaf 3010187308) (.leaf 2924438693)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2841613534) (.leaf 2761588959)) (.branch 25 (.leaf 2684248404) (.leaf 2609481230))) (.branch 28 (.branch 27 (.leaf 2537182359) (.leaf 2467251943)) (.branch 29 (.leaf 2399595050) (.leaf 2334121382)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2270744997) (.branch 32 (.leaf 2209384066) (.leaf 2149960637))) (.branch 35 (.branch 34 (.leaf 2092400416) (.leaf 2036632566)) (.branch 36 (.leaf 1982589513) (.leaf 1930206773)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1879422779) (.leaf 1830178729)) (.branch 40 (.leaf 1782418439) (.leaf 1736088203))) (.branch 43 (.branch 42 (.leaf 1691136667) (.leaf 1647514703)) (.branch 44 (.leaf 1605175301) (.leaf 1564073455))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1524166067) (.branch 47 (.leaf 1485411848) (.leaf 1447771233))) (.branch 50 (.branch 49 (.leaf 1411206288) (.leaf 1375680641)) (.branch 51 (.leaf 1341159398) (.leaf 1307609073)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1274997527) (.leaf 1243293896)) (.branch 55 (.leaf 1212468536) (.leaf 1182492966))) (.branch 58 (.branch 57 (.leaf 1153339811) (.leaf 1124982754)) (.branch 59 (.leaf 1097396488) (.leaf 1070556667))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1044439865) (.branch 62 (.leaf 1019023536) (.leaf 994285973))) (.branch 65 (.branch 64 (.leaf 970206269) (.leaf 946764288)) (.branch 66 (.leaf 923940625) (.leaf 901716580)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 880074123) (.leaf 858995868)) (.branch 70 (.leaf 838465046) (.leaf 818465477))) (.branch 73 (.branch 72 (.leaf 798981547) (.leaf 779998186)) (.branch 74 (.leaf 761500841) (.leaf 743475460))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 725908468) (.branch 77 (.leaf 708786748) (.leaf 692097627))) (.branch 80 (.branch 79 (.leaf 675828851) (.leaf 659968575)) (.branch 81 (.leaf 644505343) (.leaf 629428074)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 614726048) (.leaf 600388892)) (.branch 85 (.leaf 586406564) (.leaf 572769346))) (.branch 88 (.branch 87 (.leaf 559467826) (.leaf 546492888)) (.branch 89 (.leaf 533835705) (.leaf 521487723)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 509440652) (.branch 92 (.leaf 497686461) (.leaf 486217361))) (.branch 95 (.branch 94 (.leaf 475025803) (.leaf 464104465)) (.branch 96 (.leaf 453446246) (.leaf 443044258)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 432891818) (.leaf 422982439)) (.branch 100 (.leaf 413309829) (.leaf 403867877))) (.branch 103 (.branch 102 (.leaf 394650651) (.leaf 385652393)) (.branch 104 (.leaf 376867508) (.leaf 368290565))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 359916285) (.leaf 351739540)) (.branch 108 (.leaf 343755349) (.leaf 335958870))) (.branch 111 (.branch 110 (.leaf 328345395) (.leaf 320910349)) (.branch 112 (.leaf 313649285) (.leaf 306557877)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 299631918) (.leaf 292867319)) (.branch 116 (.leaf 286260099) (.leaf 279806388))) (.branch 119 (.branch 118 (.leaf 273502418) (.leaf 267344525)) (.branch 120 (.leaf 261329141) (.leaf 255452797)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1032).prefactor = (5077359558728903/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1032).cutoff/(generalMeanRows 1032).c)).2 =
    (65180657054399/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1032).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1032).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1032).q*(generalMeanRows 1032).c/2-2 = (703/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable334.value]
    have hcontinuation : (generalMeanRows 1032).q*(generalMeanRows 1032).cutoff/2-2 = (328/165:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable000.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1032).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1032

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1032).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1032).criticalRate j.val*(generalMeanRows 1032).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1032).c*(generalMeanRows 1032).criticalPoint j.val)).2-
      (generalMeanRows 1032).J/2-(generalMeanRows 1032).error (generalMeanGrid j.val)+
      (generalMeanRows 1032).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1032).c)).2-
      (generalMeanRows 1032).J/2-(generalMeanRows 1032).error 4 := by
  have he : (generalMeanRows 1032).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1032) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1032)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1032

/-! Kernel-checked entropy margins for general spectral rectangle 1033. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1033
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5649095839) (.branch 2 (.leaf 5469805657) (.leaf 5297956648))) (.branch 5 (.branch 4 (.leaf 5133143202) (.leaf 4974988010)) (.branch 6 (.leaf 4823139574) (.leaf 4677269996)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4537072996) (.leaf 4402262139)) (.branch 10 (.leaf 4272569240) (.leaf 4147742922))) (.branch 13 (.branch 12 (.leaf 4027547325) (.leaf 3911760920)) (.branch 14 (.leaf 3800175448) (.leaf 3692594949))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3588834874) (.branch 17 (.leaf 3488721276) (.leaf 3392090079))) (.branch 20 (.branch 19 (.leaf 3298786390) (.leaf 3208663885)) (.branch 21 (.leaf 3121584238) (.leaf 3037416590)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2956037071) (.leaf 2877328345)) (.branch 25 (.leaf 2801179206) (.leaf 2727484188))) (.branch 28 (.branch 27 (.leaf 2656143212) (.leaf 2587061262)) (.branch 29 (.leaf 2520148072) (.leaf 2455317851)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2392489013) (.branch 32 (.leaf 2331583934) (.leaf 2272528721))) (.branch 35 (.branch 34 (.leaf 2215253002) (.leaf 2159689723)) (.branch 36 (.leaf 2105774965) (.leaf 2053447766)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2002649961) (.leaf 1953326029)) (.branch 40 (.leaf 1905422949) (.leaf 1858890067))) (.branch 43 (.branch 42 (.leaf 1813678969) (.leaf 1769743364)) (.branch 44 (.leaf 1727038971) (.leaf 1685523420))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1645156146) (.branch 47 (.leaf 1605898304) (.leaf 1567712679))) (.branch 50 (.branch 49 (.leaf 1530563602) (.leaf 1494416877)) (.branch 51 (.leaf 1459239707) (.leaf 1425000625)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1391669426) (.leaf 1359217114)) (.branch 55 (.leaf 1327615837) (.leaf 1296838834))) (.branch 58 (.branch 57 (.leaf 1266860385) (.leaf 1237655764)) (.branch 59 (.leaf 1209201187) (.leaf 1181473775))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1154451506) (.branch 62 (.leaf 1128113183) (.leaf 1102438392))) (.branch 65 (.branch 64 (.leaf 1077407466) (.leaf 1053001458)) (.branch 66 (.leaf 1029202102) (.leaf 1005991787)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 983353528) (.leaf 961270939)) (.branch 70 (.leaf 939728207) (.leaf 918710067))) (.branch 73 (.branch 72 (.leaf 898201781) (.leaf 878189111)) (.branch 74 (.leaf 858658306) (.leaf 839596075))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 820989569) (.branch 77 (.leaf 802826368) (.leaf 785094459))) (.branch 80 (.branch 79 (.leaf 767782219) (.leaf 750878403)) (.branch 81 (.leaf 734372128) (.leaf 718252857)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 702510387) (.leaf 687134835)) (.branch 85 (.leaf 672116629) (.leaf 657446490))) (.branch 88 (.branch 87 (.leaf 643115428) (.leaf 629114725)) (.branch 89 (.leaf 615435929) (.leaf 602070844)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 589011516) (.branch 92 (.leaf 576250231) (.leaf 563779499))) (.branch 95 (.branch 94 (.leaf 551592054) (.leaf 539680839)) (.branch 96 (.leaf 528039002) (.leaf 516659888)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 505537034) (.leaf 494664159)) (.branch 100 (.leaf 484035159) (.leaf 473644103))) (.branch 103 (.branch 102 (.leaf 463485224) (.leaf 453552917)) (.branch 104 (.leaf 443841730) (.leaf 434346361))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 425061652) (.leaf 415982587)) (.branch 108 (.leaf 407104282) (.leaf 398421987))) (.branch 111 (.branch 110 (.leaf 389931077) (.leaf 381627051)) (.branch 112 (.leaf 373505527) (.leaf 365562235)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 357793022) (.leaf 350193838)) (.branch 116 (.leaf 342760741) (.leaf 335489889))) (.branch 119 (.branch 118 (.leaf 328377540) (.leaf 321420047)) (.branch 120 (.leaf 314613855) (.leaf 307955499)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1033).prefactor = (4963118744112289/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1033).cutoff/(generalMeanRows 1033).c)).2 =
    (362848979328901/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1033).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1033).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1033).q*(generalMeanRows 1033).c/2-2 = (829/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable068.value]
    have hcontinuation : (generalMeanRows 1033).q*(generalMeanRows 1033).cutoff/2-2 = (3296/1595:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable335.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1033).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1033

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1033).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1033).criticalRate j.val*(generalMeanRows 1033).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1033).c*(generalMeanRows 1033).criticalPoint j.val)).2-
      (generalMeanRows 1033).J/2-(generalMeanRows 1033).error (generalMeanGrid j.val)+
      (generalMeanRows 1033).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1033).c)).2-
      (generalMeanRows 1033).J/2-(generalMeanRows 1033).error 4 := by
  have he : (generalMeanRows 1033).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1033) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1033)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1033

/-! Kernel-checked entropy margins for general spectral rectangle 1034. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1034
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5508083091) (.branch 2 (.leaf 5324584273) (.leaf 5148835560))) (.branch 5 (.branch 4 (.leaf 4980415115) (.leaf 4818930392)) (.branch 6 (.leaf 4664015570) (.leaf 4515329265)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4372552486) (.leaf 4235386802)) (.branch 10 (.leaf 4103552694) (.leaf 3976788070))) (.branch 13 (.branch 12 (.leaf 3854846925) (.leaf 3737498119)) (.branch 14 (.leaf 3624524283) (.leaf 3515720809))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3410894936) (.branch 17 (.leaf 3309864917) (.leaf 3212459255))) (.branch 20 (.branch 19 (.leaf 3118515999) (.leaf 3027882107)) (.branch 21 (.leaf 2940412850) (.leaf 2855971274)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2774427690) (.leaf 2695659221)) (.branch 25 (.leaf 2619549367) (.leaf 2545987611))) (.branch 28 (.branch 27 (.leaf 2474869053) (.leaf 2406094068)) (.branch 29 (.leaf 2339567993) (.leaf 2275200827)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2212906965) (.branch 32 (.leaf 2152604938) (.leaf 2094217178))) (.branch 35 (.branch 34 (.leaf 2037669793) (.leaf 1982892366)) (.branch 36 (.leaf 1929817757) (.leaf 1878381924)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1828523753) (.leaf 1780184899)) (.branch 40 (.leaf 1733309639) (.leaf 1687844731))) (.branch 43 (.branch 42 (.leaf 1643739284) (.leaf 1600944636)) (.branch 44 (.leaf 1559414235) (.leaf 1519103536))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1479969892) (.branch 47 (.leaf 1441972464) (.leaf 1405072127))) (.branch 50 (.branch 49 (.leaf 1369231387) (.leaf 1334414298)) (.branch 51 (.leaf 1300586386) (.leaf 1267714581)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1235767145) (.leaf 1204713613)) (.branch 55 (.leaf 1174524726) (.leaf 1145172380))) (.branch 58 (.branch 57 (.leaf 1116629569) (.leaf 1088870337)) (.branch 59 (.leaf 1061869723) (.leaf 1035603724))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1010049244) (.branch 62 (.leaf 985184058) (.leaf 960986770))) (.branch 65 (.branch 64 (.leaf 937436779) (.leaf 914514240)) (.branch 66 (.leaf 892200036) (.leaf 870475740)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 849323591) (.leaf 828726461)) (.branch 70 (.leaf 808667832) (.leaf 789131767))) (.branch 73 (.branch 72 (.leaf 770102886) (.leaf 751566345)) (.branch 74 (.leaf 733507811) (.leaf 715913442))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 698769870) (.branch 77 (.leaf 682064174) (.leaf 665783872))) (.branch 80 (.branch 79 (.leaf 649916894) (.leaf 634451573)) (.branch 81 (.leaf 619376624) (.leaf 604681132)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 590354536) (.leaf 576386618)) (.branch 85 (.leaf 562767486) (.leaf 549487562))) (.branch 88 (.branch 87 (.leaf 536537575) (.leaf 523908542)) (.branch 89 (.leaf 511591765) (.leaf 499578814)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 487861520) (.branch 92 (.leaf 476431965) (.leaf 465282475))) (.branch 95 (.branch 94 (.leaf 454405608) (.leaf 443794145)) (.branch 96 (.leaf 433441086) (.leaf 423339641)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 413483219) (.leaf 403865426)) (.branch 100 (.leaf 394480055) (.leaf 385321082))) (.branch 103 (.branch 102 (.leaf 376382656) (.leaf 367659097)) (.branch 104 (.leaf 359144888) (.leaf 350834670))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 342723238) (.leaf 334805534)) (.branch 108 (.leaf 327076641) (.leaf 319531784))) (.branch 111 (.branch 110 (.leaf 312166318) (.leaf 304975730)) (.branch 112 (.leaf 297955631) (.leaf 291101754)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 284409949) (.leaf 277876178)) (.branch 116 (.leaf 271496515) (.leaf 265267141))) (.branch 119 (.branch 118 (.leaf 259184339) (.leaf 253244493)) (.branch 120 (.leaf 247444083) (.leaf 241779683)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1034).prefactor = (2566395378960549/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1034).cutoff/(generalMeanRows 1034).c)).2 =
    (169375713874921/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1034).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1034).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1034).q*(generalMeanRows 1034).c/2-2 = (449/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable336.value]
    have hcontinuation : (generalMeanRows 1034).q*(generalMeanRows 1034).cutoff/2-2 = (3296/1595:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable335.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1034).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1034

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1034).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1034).criticalRate j.val*(generalMeanRows 1034).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1034).c*(generalMeanRows 1034).criticalPoint j.val)).2-
      (generalMeanRows 1034).J/2-(generalMeanRows 1034).error (generalMeanGrid j.val)+
      (generalMeanRows 1034).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1034).c)).2-
      (generalMeanRows 1034).J/2-(generalMeanRows 1034).error 4 := by
  have he : (generalMeanRows 1034).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1034) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1034)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1034

/-! Kernel-checked entropy margins for general spectral rectangle 1035. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1035
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5696385567) (.branch 2 (.leaf 5506613554) (.leaf 5324856595))) (.branch 5 (.branch 4 (.leaf 5150678432) (.leaf 4983673100)) (.branch 6 (.leaf 4823462272) (.leaf 4669692892)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4522035064) (.leaf 4380180156)) (.branch 10 (.leaf 4243839092) (.leaf 4112740820))) (.branch 13 (.branch 12 (.leaf 3986630925) (.leaf 3865270366)) (.branch 14 (.leaf 3748434342) (.leaf 3635911250))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3527501739) (.branch 17 (.leaf 3423017851) (.leaf 3322282223))) (.branch 20 (.branch 19 (.leaf 3225127369) (.leaf 3131395015)) (.branch 21 (.leaf 3040935485) (.leaf 2953607140)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2869275861) (.leaf 2787814568)) (.branch 25 (.leaf 2709102779) (.leaf 2633026198))) (.branch 28 (.branch 27 (.leaf 2559476340) (.leaf 2488350175)) (.branch 29 (.leaf 2419549801) (.leaf 2352982143)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2288558668) (.branch 32 (.leaf 2226195121) (.leaf 2165811283))) (.branch 35 (.branch 34 (.leaf 2107330737) (.leaf 2050680658)) (.branch 36 (.leaf 1995791610) (.leaf 1942597362)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1891034711) (.leaf 1841043317)) (.branch 40 (.leaf 1792565553) (.leaf 1745546355))) (.branch 43 (.branch 42 (.leaf 1699933095) (.leaf 1655675444)) (.branch 44 (.leaf 1612725262) (.leaf 1571036477))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1530564988) (.branch 47 (.leaf 1491268558) (.leaf 1453106726))) (.branch 50 (.branch 49 (.leaf 1416040714) (.leaf 1380033347)) (.branch 51 (.leaf 1345048975) (.leaf 1311053396)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1278013787) (.leaf 1245898641)) (.branch 55 (.leaf 1214677699) (.leaf 1184321897))) (.branch 58 (.branch 57 (.leaf 1154803306) (.leaf 1126095081)) (.branch 59 (.leaf 1098171409) (.leaf 1071007465))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1044579365) (.branch 62 (.leaf 1018864123) (.leaf 993839613))) (.branch 65 (.branch 64 (.leaf 969484528) (.leaf 945778347)) (.branch 66 (.leaf 922701296) (.leaf 900234321)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 878359052) (.leaf 857057777)) (.branch 70 (.leaf 836313413) (.leaf 816109476))) (.branch 73 (.branch 72 (.leaf 796430063) (.leaf 777259821)) (.branch 74 (.leaf 758583928) (.leaf 740388068))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 722658416) (.branch 77 (.leaf 705381610) (.leaf 688544740))) (.branch 80 (.branch 79 (.leaf 672135324) (.leaf 656141297)) (.branch 81 (.leaf 640550987) (.leaf 625353106)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 610536734) (.leaf 596091301)) (.branch 85 (.leaf 582006577) (.leaf 568272658))) (.branch 88 (.branch 87 (.leaf 554879955) (.leaf 541819179)) (.branch 89 (.leaf 529081333) (.leaf 516657700)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 504539832) (.branch 92 (.leaf 492719541) (.leaf 481188888))) (.branch 95 (.branch 94 (.leaf 469940178) (.leaf 458965945)) (.branch 96 (.leaf 448258951) (.leaf 437812172)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 427618793) (.leaf 417672200)) (.branch 100 (.leaf 407965976) (.leaf 398493889))) (.branch 103 (.branch 102 (.leaf 389249889) (.leaf 380228101)) (.branch 104 (.leaf 371422820) (.leaf 362828505))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 354439771) (.leaf 346251387)) (.branch 108 (.leaf 338258270) (.leaf 330455480))) (.branch 111 (.branch 110 (.leaf 322838214) (.leaf 315401805)) (.branch 112 (.leaf 308141713) (.leaf 301053525)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 294132950) (.leaf 287375812)) (.branch 116 (.leaf 280778050) (.leaf 274335715))) (.branch 119 (.branch 118 (.leaf 268044963) (.leaf 261902054)) (.branch 120 (.leaf 255903347) (.leaf 250045302)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1035).prefactor = (5308263276161539/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1035).cutoff/(generalMeanRows 1035).c)).2 =
    (169375713874921/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1035).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1035).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1035).q*(generalMeanRows 1035).c/2-2 = (449/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable336.value]
    have hcontinuation : (generalMeanRows 1035).q*(generalMeanRows 1035).cutoff/2-2 = (3296/1595:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable335.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1035).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1035

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1035).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1035).criticalRate j.val*(generalMeanRows 1035).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1035).c*(generalMeanRows 1035).criticalPoint j.val)).2-
      (generalMeanRows 1035).J/2-(generalMeanRows 1035).error (generalMeanGrid j.val)+
      (generalMeanRows 1035).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1035).c)).2-
      (generalMeanRows 1035).J/2-(generalMeanRows 1035).error 4 := by
  have he : (generalMeanRows 1035).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1035) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1035)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1035

/-! Kernel-checked entropy margins for general spectral rectangle 1036. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1036
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5891125460) (.branch 2 (.leaf 5694865792) (.leaf 5506895186))) (.branch 5 (.branch 4 (.leaf 5326762469) (.leaf 5154047797)) (.branch 6 (.leaf 4988359909) (.leaf 4829333682)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4676627939) (.leaf 4529923498)) (.branch 10 (.leaf 4388921400) (.leaf 4253341328))) (.branch 13 (.branch 12 (.leaf 4122920168) (.leaf 3997410707)) (.branch 14 (.leaf 3876580460) (.leaf 3760210590))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3648094930) (.branch 17 (.leaf 3540039095) (.leaf 3435859661))) (.branch 20 (.branch 19 (.leaf 3335383416) (.leaf 3238446674)) (.branch 21 (.leaf 3144894643) (.leaf 3054580841)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2967366565) (.leaf 2883120390)) (.branch 25 (.leaf 2801717714) (.leaf 2723040337))) (.branch 28 (.branch 27 (.leaf 2646976061) (.leaf 2573418336)) (.branch 29 (.leaf 2502265913) (.leaf 2433422535)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2366796642) (.branch 32 (.leaf 2302301100) (.leaf 2239852945))) (.branch 35 (.branch 34 (.leaf 2179373150) (.leaf 2120786398)) (.branch 36 (.leaf 2064020882) (.leaf 2009008106)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1955682704) (.leaf 1903982276)) (.branch 40 (.leaf 1853847223) (.leaf 1805220601))) (.branch 43 (.branch 42 (.leaf 1758047979) (.leaf 1712277311)) (.branch 44 (.leaf 1667858809) (.leaf 1624744828))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1582889757) (.branch 47 (.leaf 1542249918) (.leaf 1502783463))) (.branch 50 (.branch 49 (.leaf 1464450291) (.leaf 1427211956)) (.branch 51 (.leaf 1391031588) (.leaf 1355873816)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1321704697) (.leaf 1288491644)) (.branch 55 (.leaf 1256203365) (.leaf 1224809802))) (.branch 58 (.branch 57 (.leaf 1194282072) (.leaf 1164592410)) (.branch 59 (.leaf 1135714124) (.leaf 1107621538))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1080289952) (.branch 62 (.leaf 1053695594) (.leaf 1027815582))) (.branch 65 (.branch 64 (.leaf 1002627881) (.leaf 978111266)) (.branch 66 (.leaf 954245290) (.leaf 931010246)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 908387137) (.leaf 886357644)) (.branch 70 (.leaf 864904101) (.leaf 844009461))) (.branch 73 (.branch 72 (.leaf 823657276) (.leaf 803831670)) (.branch 74 (.leaf 784517311) (.leaf 765699398))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 747363629) (.branch 77 (.leaf 729496189) (.leaf 712083724))) (.branch 80 (.branch 79 (.leaf 695113327) (.leaf 678572518)) (.branch 81 (.leaf 662449229) (.leaf 646731785)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 631408892) (.leaf 616469619)) (.branch 85 (.leaf 601903386) (.leaf 587699952))) (.branch 88 (.branch 87 (.leaf 573849398) (.leaf 560342119)) (.branch 89 (.leaf 547168810) (.leaf 534320456)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 521788319) (.branch 92 (.leaf 509563933) (.leaf 497639086))) (.branch 95 (.branch 94 (.leaf 486005821) (.leaf 474656417)) (.branch 96 (.leaf 463583388) (.leaf 452779469)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 442237613) (.leaf 431950981)) (.branch 100 (.leaf 421912934) (.leaf 412117028))) (.branch 103 (.branch 102 (.leaf 402557008) (.leaf 393226796)) (.branch 104 (.leaf 384120493) (.leaf 375232367))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 366556851) (.leaf 358088535)) (.branch 108 (.leaf 349822160) (.leaf 341752620))) (.branch 111 (.branch 110 (.leaf 333874946) (.leaf 326184311)) (.branch 112 (.leaf 318676022) (.leaf 311345513)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 304188347) (.leaf 297200205)) (.branch 116 (.leaf 290376889) (.leaf 283714313))) (.branch 119 (.branch 118 (.leaf 277208502) (.leaf 270855587)) (.branch 120 (.leaf 264651805) (.leaf 258593493)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1036).prefactor = (2744867299096547/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1036).cutoff/(generalMeanRows 1036).c)).2 =
    (169375713874921/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1036).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1036).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1036).q*(generalMeanRows 1036).c/2-2 = (449/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable336.value]
    have hcontinuation : (generalMeanRows 1036).q*(generalMeanRows 1036).cutoff/2-2 = (3296/1595:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable335.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1036).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1036

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1036).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1036).criticalRate j.val*(generalMeanRows 1036).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1036).c*(generalMeanRows 1036).criticalPoint j.val)).2-
      (generalMeanRows 1036).J/2-(generalMeanRows 1036).error (generalMeanGrid j.val)+
      (generalMeanRows 1036).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1036).c)).2-
      (generalMeanRows 1036).J/2-(generalMeanRows 1036).error 4 := by
  have he : (generalMeanRows 1036).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1036) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1036)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1036

/-! Kernel-checked entropy margins for general spectral rectangle 1037. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1037
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6182423662) (.branch 2 (.leaf 5978881658) (.leaf 5783897914))) (.branch 5 (.branch 4 (.leaf 5597006512) (.leaf 5417773925)) (.branch 6 (.leaf 5245796176) (.leaf 5080696304)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4922122110) (.leaf 4769744118)) (.branch 10 (.leaf 4623253764) (.leaf 4482361741))) (.branch 13 (.branch 12 (.leaf 4346796526) (.leaf 4216303025)) (.branch 14 (.leaf 4090641359) (.leaf 3969585752))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3852923519) (.branch 17 (.leaf 3740454141) (.leaf 3631988424))) (.branch 20 (.branch 19 (.leaf 3527347719) (.leaf 3426363217)) (.branch 21 (.leaf 3328875292) (.leaf 3234732899)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3143793023) (.leaf 3055920163)) (.branch 25 (.leaf 2970985863) (.leaf 2888868272))) (.branch 28 (.branch 27 (.leaf 2809451736) (.leaf 2732626426)) (.branch 29 (.leaf 2658287986) (.leaf 2586337208)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2516679732) (.branch 32 (.leaf 2449225762) (.leaf 2383889804))) (.branch 35 (.branch 34 (.leaf 2320590422) (.leaf 2259250009)) (.branch 36 (.leaf 2199794574) (.leaf 2142153540)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2086259561) (.leaf 2032048343)) (.branch 40 (.leaf 1979458481) (.leaf 1928431305))) (.branch 43 (.branch 42 (.leaf 1878910736) (.leaf 1830843152)) (.branch 44 (.leaf 1784177256) (.leaf 1738863960))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1694856270) (.branch 47 (.leaf 1652109182) (.leaf 1610579580))) (.branch 50 (.branch 49 (.leaf 1570226142) (.leaf 1531009254)) (.branch 51 (.leaf 1492890923) (.leaf 1455834698)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1419805597) (.leaf 1384770038)) (.branch 55 (.leaf 1350695768) (.leaf 1317551805))) (.branch 58 (.branch 57 (.leaf 1285308374) (.leaf 1253936854)) (.branch 59 (.leaf 1223409722) (.leaf 1193700508))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1164783738) (.branch 62 (.leaf 1136634898) (.leaf 1109230386))) (.branch 65 (.branch 64 (.leaf 1082547473) (.leaf 1056564262)) (.branch 66 (.leaf 1031259656) (.leaf 1006613318)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 982605643) (.leaf 959217721)) (.branch 70 (.leaf 936431313) (.leaf 914228819))) (.branch 73 (.branch 72 (.leaf 892593253) (.leaf 871508215)) (.branch 74 (.leaf 850957869) (.leaf 830926919))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 811400586) (.branch 77 (.leaf 792364590) (.leaf 773805124))) (.branch 80 (.branch 79 (.leaf 755708843) (.leaf 738062839)) (.branch 81 (.leaf 720854626) (.leaf 704072126)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 687703647) (.leaf 671737875)) (.branch 85 (.leaf 656163856) (.leaf 640970980))) (.branch 88 (.branch 87 (.leaf 626148975) (.leaf 611687885)) (.branch 89 (.leaf 597578068) (.leaf 583810175)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 570375148) (.branch 92 (.leaf 557264200) (.leaf 544468815))) (.branch 95 (.branch 94 (.leaf 531980732) (.leaf 519791935)) (.branch 96 (.leaf 507894650) (.leaf 496281330)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 484944653) (.leaf 473877510)) (.branch 100 (.leaf 463072998) (.leaf 452524415))) (.branch 103 (.branch 102 (.leaf 442225251) (.leaf 432169185)) (.branch 104 (.leaf 422350072) (.leaf 412761944))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 403399000) (.leaf 394255604)) (.branch 108 (.leaf 385326274) (.leaf 376605684))) (.branch 111 (.branch 110 (.leaf 368088651) (.leaf 359770139)) (.branch 112 (.leaf 351645247) (.leaf 343709209)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 335957388) (.leaf 328385273)) (.branch 116 (.leaf 320988473) (.leaf 313762716))) (.branch 119 (.branch 118 (.leaf 306703844) (.leaf 299807809)) (.branch 120 (.leaf 293070669) (.leaf 286488589)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1037).prefactor = (567740980255049/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1037).cutoff/(generalMeanRows 1037).c)).2 =
    (344721594736347/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1037).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1037).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1037).q*(generalMeanRows 1037).cutoff/2-2 = (3296/1595:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable335.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1037).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1037

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1037).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1037).criticalRate j.val*(generalMeanRows 1037).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1037).c*(generalMeanRows 1037).criticalPoint j.val)).2-
      (generalMeanRows 1037).J/2-(generalMeanRows 1037).error (generalMeanGrid j.val)+
      (generalMeanRows 1037).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1037).c)).2-
      (generalMeanRows 1037).J/2-(generalMeanRows 1037).error 4 := by
  have he : (generalMeanRows 1037).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1037) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1037)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1037

/-! Kernel-checked entropy margins for general spectral rectangle 1038. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1038
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6488452590) (.branch 2 (.leaf 6277387695) (.leaf 6075158341))) (.branch 5 (.branch 4 (.leaf 5881283369) (.leaf 5695315108)) (.branch 6 (.leaf 5516836436) (.leaf 5345458166)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5180816704) (.leaf 5022571948)) (.branch 10 (.leaf 4870405406) (.leaf 4724018495))) (.branch 13 (.branch 12 (.leaf 4583131007) (.leaf 4447479712)) (.branch 14 (.leaf 4316817104) (.leaf 4190910246))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4069539728) (.branch 17 (.leaf 3952498707) (.leaf 3839592039))) (.branch 20 (.branch 19 (.leaf 3730635474) (.leaf 3625454919)) (.branch 21 (.leaf 3523885770) (.leaf 3425772282)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3330967000) (.leaf 3239330230)) (.branch 25 (.leaf 3150729546) (.leaf 3065039341))) (.branch 28 (.branch 27 (.leaf 2982140408) (.leaf 2901919548)) (.branch 29 (.leaf 2824269210) (.leaf 2749087156)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2676276148) (.branch 32 (.leaf 2605743656) (.leaf 2537401590))) (.branch 35 (.branch 34 (.leaf 2471166042) (.leaf 2406957056)) (.branch 36 (.leaf 2344698403) (.leaf 2284317373)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2225744587) (.leaf 2168913814)) (.branch 40 (.leaf 2113761798) (.leaf 2060228105))) (.branch 43 (.branch 42 (.leaf 2008254969) (.leaf 1957787154)) (.branch 44 (.leaf 1908771821) (.leaf 1861158406))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1814898503) (.branch 47 (.leaf 1769945755) (.leaf 1726255747))) (.branch 50 (.branch 49 (.leaf 1683785916) (.leaf 1642495451)) (.branch 51 (.leaf 1602345214) (.leaf 1563297655)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1525316734) (.leaf 1488367851)) (.branch 55 (.leaf 1452417775) (.leaf 1417434583))) (.branch 58 (.branch 57 (.leaf 1383387592) (.leaf 1350247308)) (.branch 59 (.leaf 1317985366) (.leaf 1286574483))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1255988402) (.branch 62 (.leaf 1226201851) (.leaf 1197190499))) (.branch 65 (.branch 64 (.leaf 1168930907) (.leaf 1141400499)) (.branch 66 (.leaf 1114577515) (.leaf 1088440979)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1062970667) (.leaf 1038147070)) (.branch 70 (.leaf 1013951367) (.leaf 990365395))) (.branch 73 (.branch 72 (.leaf 967371622) (.leaf 944953117)) (.branch 74 (.leaf 923093530) (.leaf 901777064))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 880988456) (.branch 77 (.leaf 860712952) (.leaf 840936288))) (.branch 80 (.branch 79 (.leaf 821644671) (.leaf 802824759)) (.branch 81 (.leaf 784463644) (.leaf 766548834)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 749068239) (.leaf 732010152)) (.branch 85 (.leaf 715363237) (.leaf 699116516))) (.branch 88 (.branch 87 (.leaf 683259351) (.leaf 667781435)) (.branch 89 (.leaf 652672778) (.leaf 637923698)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 623524803) (.branch 92 (.leaf 609466990) (.leaf 595741425))) (.branch 95 (.branch 94 (.leaf 582339541) (.leaf 569253023)) (.branch 96 (.leaf 556473802) (.leaf 543994045)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 531806150) (.leaf 519902731)) (.branch 100 (.leaf 508276618) (.leaf 496920844))) (.branch 103 (.branch 102 (.leaf 485828644) (.leaf 474993441)) (.branch 104 (.leaf 464408846) (.leaf 454068647))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 443966807) (.leaf 434097455)) (.branch 108 (.leaf 424454884) (.leaf 415033541))) (.branch 111 (.branch 110 (.leaf 405828027) (.leaf 396833089)) (.branch 112 (.leaf 388043616) (.leaf 379454636)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 371061308) (.leaf 362858922)) (.branch 116 (.leaf 354842892) (.leaf 347008755))) (.branch 119 (.branch 118 (.leaf 339352163) (.leaf 331868885)) (.branch 120 (.leaf 324554798) (.leaf 317405888)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1038).prefactor = (2935750489350221/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1038).cutoff/(generalMeanRows 1038).c)).2 =
    (350727618796559/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1038).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1038).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1038).q*(generalMeanRows 1038).c/2-2 = (1727/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable337.value]
    have hcontinuation : (generalMeanRows 1038).q*(generalMeanRows 1038).cutoff/2-2 = (3296/1595:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable335.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1038).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1038

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1038).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1038).criticalRate j.val*(generalMeanRows 1038).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1038).c*(generalMeanRows 1038).criticalPoint j.val)).2-
      (generalMeanRows 1038).J/2-(generalMeanRows 1038).error (generalMeanGrid j.val)+
      (generalMeanRows 1038).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1038).c)).2-
      (generalMeanRows 1038).J/2-(generalMeanRows 1038).error 4 := by
  have he : (generalMeanRows 1038).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1038) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1038)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1038

/-! Kernel-checked entropy margins for general spectral rectangle 1039. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1039
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7001509788) (.branch 2 (.leaf 6784880971) (.leaf 6577169089))) (.branch 5 (.branch 4 (.leaf 6377887411) (.leaf 6186583252)) (.branch 6 (.leaf 6002834973) (.leaf 5826249322)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5656459044) (.leaf 5493120746)) (.branch 10 (.leaf 5335912976) (.leaf 5184534490))) (.branch 13 (.branch 12 (.leaf 5038702693) (.leaf 4898152215)) (.branch 14 (.leaf 4762633633) (.leaf 4631912298))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4505767270) (.branch 17 (.leaf 4383990347) (.leaf 4266385176))) (.branch 20 (.branch 19 (.leaf 4152766433) (.leaf 4042959083)) (.branch 21 (.leaf 3936797687) (.leaf 3834125770)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3734795242) (.leaf 3638665853)) (.branch 25 (.leaf 3545604703) (.leaf 3455485778))) (.branch 28 (.branch 27 (.leaf 3368189521) (.leaf 3283602443)) (.branch 29 (.leaf 3201616753) (.leaf 3122130014)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3045044833) (.branch 32 (.leaf 2970268559) (.leaf 2897713009))) (.branch 35 (.branch 34 (.leaf 2827294215) (.leaf 2758932181)) (.branch 36 (.leaf 2692550660) (.leaf 2628076945)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2565441674) (.leaf 2504578644)) (.branch 40 (.leaf 2445424644) (.leaf 2387919287))) (.branch 43 (.branch 42 (.leaf 2332004867) (.leaf 2277626212)) (.branch 44 (.leaf 2224730551) (.leaf 2173267392))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2123188402) (.branch 47 (.leaf 2074447296) (.leaf 2026999735))) (.branch 50 (.branch 49 (.leaf 1980803226) (.leaf 1935817030)) (.branch 51 (.leaf 1892002075) (.leaf 1849320874)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1807737447) (.leaf 1767217251)) (.branch 55 (.leaf 1727727104) (.leaf 1689235126))) (.branch 58 (.branch 57 (.leaf 1651710676) (.leaf 1615124292)) (.branch 59 (.leaf 1579447636) (.leaf 1544653443))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1510715473) (.branch 62 (.leaf 1477608460) (.leaf 1445308071))) (.branch 65 (.branch 64 (.leaf 1413790862) (.leaf 1383034242)) (.branch 66 (.leaf 1353016430) (.leaf 1323716422)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1295113959) (.leaf 1267189490)) (.branch 70 (.leaf 1239924145) (.leaf 1213299704))) (.branch 73 (.branch 72 (.leaf 1187298572) (.leaf 1161903750)) (.branch 74 (.leaf 1137098810) (.leaf 1112867874))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1089195588) (.branch 77 (.leaf 1066067105) (.leaf 1043468057))) (.branch 80 (.branch 79 (.leaf 1021384546) (.leaf 999803115)) (.branch 81 (.leaf 978710737) (.leaf 958094796)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 937943071) (.leaf 918243721)) (.branch 85 (.leaf 898985270) (.leaf 880156593))) (.branch 88 (.branch 87 (.leaf 861746904) (.leaf 843745740)) (.branch 89 (.leaf 826142954) (.leaf 808928698)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 792093416) (.branch 92 (.leaf 775627831) (.leaf 759522935))) (.branch 95 (.branch 94 (.leaf 743769983) (.leaf 728360477)) (.branch 96 (.leaf 713286163) (.leaf 698539021)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 684111254) (.leaf 669995285)) (.branch 100 (.leaf 656183745) (.leaf 642669470))) (.branch 103 (.branch 102 (.leaf 629445490) (.leaf 616505026)) (.branch 104 (.leaf 603841481) (.leaf 591448436))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 579319643) (.leaf 567449020)) (.branch 108 (.leaf 555830646) (.leaf 544458753))) (.branch 111 (.branch 110 (.leaf 533327726) (.leaf 522432094)) (.branch 112 (.leaf 511766528) (.leaf 501325836)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 491104956) (.leaf 481098957)) (.branch 116 (.leaf 471303033) (.leaf 461712495))) (.branch 119 (.branch 118 (.leaf 452322775) (.leaf 443129417)) (.branch 120 (.leaf 434128074) (.leaf 425314509)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1039).prefactor = (2985510405012273/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1039).cutoff/(generalMeanRows 1039).c)).2 =
    (187559535960359/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1039).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1039).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1039).q*(generalMeanRows 1039).c/2-2 = (1589/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable251.value]
    have hcontinuation : (generalMeanRows 1039).q*(generalMeanRows 1039).cutoff/2-2 = (3296/1595:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable335.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1039).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1039

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1039).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1039).criticalRate j.val*(generalMeanRows 1039).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1039).c*(generalMeanRows 1039).criticalPoint j.val)).2-
      (generalMeanRows 1039).J/2-(generalMeanRows 1039).error (generalMeanGrid j.val)+
      (generalMeanRows 1039).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1039).c)).2-
      (generalMeanRows 1039).J/2-(generalMeanRows 1039).error 4 := by
  have he : (generalMeanRows 1039).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1039) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1039)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1039

/-! Kernel-checked entropy margins for general spectral rectangle 1040. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1040
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7276148825) (.branch 2 (.leaf 7073014077) (.leaf 6877662101))) (.branch 5 (.branch 4 (.leaf 6689689098) (.leaf 6508719008)) (.branch 6 (.leaf 6334401031) (.leaf 6166407425)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6004431547) (.leaf 5848186102)) (.branch 10 (.leaf 5697401575) (.leaf 5551824824))) (.branch 13 (.branch 12 (.leaf 5411217810) (.leaf 5275356455)) (.branch 14 (.leaf 5144029600) (.leaf 5017038070))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4894193814) (.branch 17 (.leaf 4775319129) (.leaf 4660245949))) (.branch 20 (.branch 19 (.leaf 4548815190) (.leaf 4440876157)) (.branch 21 (.leaf 4336285995) (.leaf 4234909188)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4136617091) (.leaf 4041287503)) (.branch 25 (.leaf 3948804276) (.leaf 3859056943))) (.branch 28 (.branch 27 (.leaf 3771940384) (.leaf 3687354509)) (.branch 29 (.leaf 3605203967) (.leaf 3525397873)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3447849560) (.branch 32 (.leaf 3372476336) (.leaf 3299199271))) (.branch 35 (.branch 34 (.leaf 3227942989) (.leaf 3158635476)) (.branch 36 (.leaf 3091207899) (.leaf 3025594441)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2961732143) (.leaf 2899560754)) (.branch 40 (.leaf 2839022592) (.leaf 2780062417))) (.branch 43 (.branch 42 (.leaf 2722627306) (.leaf 2666666536)) (.branch 44 (.leaf 2612131479) (.leaf 2558975496))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2507153844) (.branch 47 (.leaf 2456623581) (.leaf 2407343483))) (.branch 50 (.branch 49 (.leaf 2359273963) (.leaf 2312376989)) (.branch 51 (.leaf 2266616019) (.leaf 2221955928)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2178362941) (.leaf 2135804577)) (.branch 55 (.leaf 2094249585) (.leaf 2053667894))) (.branch 58 (.branch 57 (.leaf 2014030554) (.leaf 1975309694)) (.branch 59 (.leaf 1937478467) (.leaf 1900511012))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1864382405) (.branch 62 (.leaf 1829068624) (.leaf 1794546506))) (.branch 65 (.branch 64 (.leaf 1760793714) (.leaf 1727788701)) (.branch 66 (.leaf 1695510675) (.leaf 1663939569)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1633056010) (.leaf 1602841293)) (.branch 70 (.leaf 1573277351) (.leaf 1544346729))) (.branch 73 (.branch 72 (.leaf 1516032560) (.leaf 1488318542)) (.branch 74 (.leaf 1461188913) (.leaf 1434628434))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1408622362) (.branch 77 (.leaf 1383156436) (.leaf 1358216856))) (.branch 80 (.branch 79 (.leaf 1333790263) (.leaf 1309863728)) (.branch 81 (.leaf 1286424727) (.leaf 1263461133)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1240961197) (.leaf 1218913536)) (.branch 85 (.leaf 1197307115) (.leaf 1176131239))) (.branch 88 (.branch 87 (.leaf 1155375539) (.leaf 1135029957)) (.branch 89 (.leaf 1115084738) (.leaf 1095530418)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1076357812) (.branch 92 (.leaf 1057558008) (.leaf 1039122350))) (.branch 95 (.branch 94 (.leaf 1021042437) (.leaf 1003310107)) (.branch 96 (.leaf 985917435) (.leaf 968856718)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 952120473) (.leaf 935701426)) (.branch 100 (.leaf 919592505) (.leaf 903786836))) (.branch 103 (.branch 102 (.leaf 888277732) (.leaf 873058691)) (.branch 104 (.leaf 858123384) (.leaf 843465657))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 829079517) (.leaf 814959134)) (.branch 108 (.leaf 801098829) (.leaf 787493075))) (.branch 111 (.branch 110 (.leaf 774136488) (.leaf 761023824)) (.branch 112 (.leaf 748149973) (.leaf 735509958)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 723098928) (.leaf 710912154)) (.branch 116 (.leaf 698945026) (.leaf 687193051))) (.branch 119 (.branch 118 (.leaf 675651844) (.leaf 664317131)) (.branch 120 (.leaf 653184744) (.leaf 642250612)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1040).prefactor = (5044262486406209/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1040).cutoff/(generalMeanRows 1040).c)).2 =
    (10196568978501/31250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1040).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1040).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1040).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1040

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1040).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1040).criticalRate j.val*(generalMeanRows 1040).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1040).c*(generalMeanRows 1040).criticalPoint j.val)).2-
      (generalMeanRows 1040).J/2-(generalMeanRows 1040).error (generalMeanGrid j.val)+
      (generalMeanRows 1040).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1040).c)).2-
      (generalMeanRows 1040).J/2-(generalMeanRows 1040).error 4 := by
  have he : (generalMeanRows 1040).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1040) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1040)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1040

/-! Kernel-checked entropy margins for general spectral rectangle 1041. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1041
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7019045567) (.branch 2 (.leaf 6822045391) (.leaf 6632658813))) (.branch 5 (.branch 4 (.leaf 6450487608) (.leaf 6275160964)) (.branch 6 (.leaf 6106333038) (.leaf 5943680790)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5786902051) (.leaf 5635713793)) (.branch 10 (.leaf 5489850584) (.leaf 5349063197))) (.branch 13 (.branch 12 (.leaf 5213117357) (.leaf 5081792606)) (.branch 14 (.leaf 4954881280) (.leaf 4832187578))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4713526711) (.branch 17 (.leaf 4598724136) (.leaf 4487614848))) (.branch 20 (.branch 19 (.leaf 4380042733) (.leaf 4275859981)) (.branch 21 (.leaf 4174926537) (.leaf 4077109606)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3982283191) (.leaf 3890327669)) (.branch 25 (.leaf 3801129394) (.leaf 3714580341))) (.branch 28 (.branch 27 (.leaf 3630577765) (.leaf 3549023889)) (.branch 29 (.leaf 3469825613) (.leaf 3392894250)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3318145266) (.branch 32 (.leaf 3245498056) (.leaf 3174875715))) (.branch 35 (.branch 34 (.leaf 3106204845) (.leaf 3039415355)) (.branch 36 (.leaf 2974440289) (.leaf 2911215656)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2849680276) (.leaf 2789775631)) (.branch 40 (.leaf 2731445726) (.leaf 2674636963))) (.branch 43 (.branch 42 (.leaf 2619298020) (.leaf 2565379731)) (.branch 44 (.leaf 2512834983) (.leaf 2461618614))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2411687315) (.branch 47 (.leaf 2362999543) (.leaf 2315515433))) (.branch 50 (.branch 49 (.leaf 2269196719) (.leaf 2224006658)) (.branch 51 (.leaf 2179909957) (.leaf 2136872708)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2094862320) (.leaf 2053847461)) (.branch 55 (.leaf 2013797999) (.leaf 1974684949))) (.branch 58 (.branch 57 (.leaf 1936480419) (.leaf 1899157562)) (.branch 59 (.leaf 1862690530) (.leaf 1827054428))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1792225276) (.branch 62 (.leaf 1758179965) (.leaf 1724896220))) (.branch 65 (.branch 64 (.leaf 1692352566) (.leaf 1660528292)) (.branch 66 (.leaf 1629403419) (.leaf 1598958669)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1569175437) (.leaf 1540035758)) (.branch 70 (.leaf 1511522287) (.leaf 1483618269))) (.branch 73 (.branch 72 (.leaf 1456307517) (.leaf 1429574387)) (.branch 74 (.leaf 1403403757) (.leaf 1377781007))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1352691996) (.branch 77 (.leaf 1328123047) (.leaf 1304060925))) (.branch 80 (.branch 79 (.leaf 1280492820) (.leaf 1257406335)) (.branch 81 (.leaf 1234789462) (.leaf 1212630574)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1190918408) (.leaf 1169642049)) (.branch 85 (.leaf 1148790920) (.leaf 1128354767))) (.branch 88 (.branch 87 (.leaf 1108323649) (.leaf 1088687923)) (.branch 89 (.leaf 1069438237) (.leaf 1050565518)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1032060957) (.branch 92 (.leaf 1013916009) (.leaf 996122374))) (.branch 95 (.branch 94 (.leaf 978671993) (.leaf 961557039)) (.branch 96 (.leaf 944769910) (.leaf 928303215)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 912149776) (.leaf 896302611)) (.branch 100 (.leaf 880754935) (.leaf 865500149))) (.branch 103 (.branch 102 (.leaf 850531834) (.leaf 835843746)) (.branch 104 (.leaf 821429809) (.leaf 807284111))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 793400896) (.leaf 779774561)) (.branch 108 (.leaf 766399650) (.leaf 753270850))) (.branch 111 (.branch 110 (.leaf 740382986) (.leaf 727731014)) (.branch 112 (.leaf 715310021) (.leaf 703115220)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 691141941) (.leaf 679385635)) (.branch 116 (.leaf 667841864) (.leaf 656506302))) (.branch 119 (.branch 118 (.leaf 645374728) (.leaf 634443024)) (.branch 120 (.leaf 623707172) (.leaf 613163254)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1041).prefactor = (9698242317277/1953125000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1041).cutoff/(generalMeanRows 1041).c)).2 =
    (169375713874921/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1041).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1041).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1041).q*(generalMeanRows 1041).cutoff/2-2 = (1583/924:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable338.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1041).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1041

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1041).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1041).criticalRate j.val*(generalMeanRows 1041).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1041).c*(generalMeanRows 1041).criticalPoint j.val)).2-
      (generalMeanRows 1041).J/2-(generalMeanRows 1041).error (generalMeanGrid j.val)+
      (generalMeanRows 1041).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1041).c)).2-
      (generalMeanRows 1041).J/2-(generalMeanRows 1041).error 4 := by
  have he : (generalMeanRows 1041).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1041) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1041)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1041

/-! Kernel-checked entropy margins for general spectral rectangle 1042. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1042
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6750618852) (.branch 2 (.leaf 6545304432) (.leaf 6348088852))) (.branch 5 (.branch 4 (.leaf 6158551161) (.leaf 5976299184)) (.branch 6 (.leaf 5800966967) (.leaf 5632212508)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5469715731) (.leaf 5313176677)) (.branch 10 (.leaf 5162313887) (.leaf 5016862938))) (.branch 13 (.branch 12 (.leaf 4876575136) (.leaf 4741216326)) (.branch 14 (.leaf 4610565816) (.leaf 4484415406))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4362568497) (.branch 17 (.leaf 4244839279) (.leaf 4131051997))) (.branch 20 (.branch 19 (.leaf 4021040275) (.leaf 3914646487)) (.branch 21 (.leaf 3811721199) (.leaf 3712122636)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3615716202) (.leaf 3522374035)) (.branch 25 (.leaf 3431974596) (.leaf 3344402283))) (.branch 28 (.branch 27 (.leaf 3259547084) (.leaf 3177304245)) (.branch 29 (.leaf 3097573966) (.leaf 3020261119)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2945274985) (.branch 32 (.leaf 2872529005) (.leaf 2801940554))) (.branch 35 (.branch 34 (.leaf 2733430723) (.leaf 2666924124)) (.branch 36 (.leaf 2602348695) (.leaf 2539635534)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2478718725) (.leaf 2419535188)) (.branch 40 (.leaf 2362024536) (.leaf 2306128934))) (.branch 43 (.branch 42 (.leaf 2251792973) (.leaf 2198963550)) (.branch 44 (.leaf 2147589755) (.leaf 2097622761))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2049015725) (.branch 47 (.leaf 2001723694) (.leaf 1955703512))) (.branch 50 (.branch 49 (.leaf 1910913737) (.leaf 1867314562)) (.branch 51 (.leaf 1824867736) (.leaf 1783536493)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1743285488) (.leaf 1704080726)) (.branch 55 (.leaf 1665889506) (.leaf 1628680360))) (.branch 58 (.branch 57 (.leaf 1592423001) (.leaf 1557088269)) (.branch 59 (.leaf 1522648083) (.leaf 1489075391))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1456344130) (.branch 62 (.leaf 1424429180) (.leaf 1393306324))) (.branch 65 (.branch 64 (.leaf 1362952214) (.leaf 1333344327)) (.branch 66 (.leaf 1304460937) (.leaf 1276281079)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1248784519) (.leaf 1221951720)) (.branch 70 (.leaf 1195763821) (.leaf 1170202601))) (.branch 73 (.branch 72 (.leaf 1145250460) (.leaf 1120890391)) (.branch 74 (.leaf 1097105956) (.leaf 1073881265))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1051200954) (.branch 77 (.leaf 1029050165) (.leaf 1007414523))) (.branch 80 (.branch 79 (.leaf 986280122) (.leaf 965633505)) (.branch 81 (.leaf 945461646) (.leaf 925751935)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 906492160) (.leaf 887670497)) (.branch 85 (.leaf 869275489) (.leaf 851296037))) (.branch 88 (.branch 87 (.leaf 833721385) (.leaf 816541109)) (.branch 89 (.leaf 799745102) (.leaf 783323566)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 767266998) (.branch 92 (.leaf 751566180) (.leaf 736212170))) (.branch 95 (.branch 94 (.leaf 721196293) (.leaf 706510127)) (.branch 96 (.leaf 692145500) (.leaf 678094477)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 664349355) (.leaf 650902650)) (.branch 100 (.leaf 637747098) (.leaf 624875637))) (.branch 103 (.branch 102 (.leaf 612281408) (.leaf 599957747)) (.branch 104 (.leaf 587898174) (.leaf 576096393))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 564546281) (.leaf 553241883)) (.branch 108 (.leaf 542177412) (.leaf 531347235))) (.branch 111 (.branch 110 (.leaf 520745873) (.leaf 510367997)) (.branch 112 (.leaf 500208420) (.leaf 490262094)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 480524106) (.leaf 470989673)) (.branch 116 (.leaf 461654138) (.leaf 452512966))) (.branch 119 (.branch 118 (.leaf 443561740) (.leaf 434796161)) (.branch 120 (.leaf 426212036) (.leaf 417805284)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1042).prefactor = (2608182308626923/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1042).cutoff/(generalMeanRows 1042).c)).2 =
    (74551333338873/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1042).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1042).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1042).q*(generalMeanRows 1042).cutoff/2-2 = (1583/924:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable338.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1042).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1042

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1042).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1042).criticalRate j.val*(generalMeanRows 1042).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1042).c*(generalMeanRows 1042).criticalPoint j.val)).2-
      (generalMeanRows 1042).J/2-(generalMeanRows 1042).error (generalMeanGrid j.val)+
      (generalMeanRows 1042).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1042).c)).2-
      (generalMeanRows 1042).J/2-(generalMeanRows 1042).error 4 := by
  have he : (generalMeanRows 1042).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1042) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1042)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1042

/-! Kernel-checked entropy margins for general spectral rectangle 1043. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1043
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6683476799) (.branch 2 (.leaf 6484649839) (.leaf 6293673673))) (.branch 5 (.branch 4 (.leaf 6110136037) (.leaf 5933652996)) (.branch 6 (.leaf 5763866437) (.leaf 5600441830)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5443066243) (.leaf 5291446562)) (.branch 10 (.leaf 5145307890) (.leaf 5004392119))) (.branch 13 (.branch 12 (.leaf 4868456629) (.leaf 4737273122)) (.branch 14 (.leaf 4610626560) (.leaf 4488314201))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4370144724) (.branch 17 (.leaf 4255937433) (.leaf 4145521519))) (.branch 20 (.branch 19 (.leaf 4038735399) (.leaf 3935426098)) (.branch 21 (.leaf 3835448689) (.leaf 3738665772)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3644946998) (.leaf 3554168628)) (.branch 25 (.leaf 3466213126) (.leaf 3380968781))) (.branch 28 (.branch 27 (.leaf 3298329359) (.leaf 3218193776)) (.branch 29 (.leaf 3140465800) (.leaf 3065053769)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2991870333) (.branch 32 (.leaf 2920832205) (.leaf 2851859942))) (.branch 35 (.branch 34 (.leaf 2784877727) (.leaf 2719813174)) (.branch 36 (.leaf 2656597143) (.leaf 2595163564)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2535449279) (.leaf 2477393885)) (.branch 40 (.leaf 2420939593) (.leaf 2366031095))) (.branch 43 (.branch 42 (.leaf 2312615435) (.leaf 2260641892)) (.branch 44 (.leaf 2210061867) (.leaf 2160828781))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2112897969) (.branch 47 (.leaf 2066226593) (.leaf 2020773551))) (.branch 50 (.branch 49 (.leaf 1976499394) (.leaf 1933366247)) (.branch 51 (.leaf 1891337734) (.leaf 1850378909)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1810456188) (.leaf 1771537289)) (.branch 55 (.leaf 1733591167) (.leaf 1696587964))) (.branch 58 (.branch 57 (.leaf 1660498949) (.leaf 1625296472)) (.branch 59 (.leaf 1590953914) (.leaf 1557445641))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1524746963) (.branch 62 (.leaf 1492834088) (.leaf 1461684088))) (.branch 65 (.branch 64 (.leaf 1431274858) (.leaf 1401585084)) (.branch 66 (.leaf 1372594208) (.leaf 1344282393)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1316630497) (.leaf 1289620044)) (.branch 70 (.leaf 1263233192) (.leaf 1237452711))) (.branch 73 (.branch 72 (.leaf 1212261957) (.leaf 1187644846)) (.branch 74 (.leaf 1163585834) (.leaf 1140069894))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1117082497) (.branch 77 (.leaf 1094609589) (.leaf 1072637574))) (.branch 80 (.branch 79 (.leaf 1051153298) (.leaf 1030144028)) (.branch 81 (.leaf 1009597439) (.leaf 989501595)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 969844939) (.leaf 950616273)) (.branch 85 (.leaf 931804747) (.leaf 913399848))) (.branch 88 (.branch 87 (.leaf 895391383) (.leaf 877769471)) (.branch 89 (.leaf 860524529) (.leaf 843647264)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 827128657) (.branch 92 (.leaf 810959959) (.leaf 795132680))) (.branch 95 (.branch 94 (.leaf 779638574) (.leaf 764469641)) (.branch 96 (.leaf 749618106) (.leaf 735076423)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 720837257) (.leaf 706893483)) (.branch 100 (.leaf 693238176) (.leaf 679864607))) (.branch 103 (.branch 102 (.leaf 666766231) (.leaf 653936686)) (.branch 104 (.leaf 641369785) (.leaf 629059508))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 617000003) (.leaf 605185570)) (.branch 108 (.leaf 593610666) (.leaf 582269895))) (.branch 111 (.branch 110 (.leaf 571158004) (.leaf 560269878)) (.branch 112 (.leaf 549600537) (.leaf 539145130)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 528898931) (.leaf 518857338)) (.branch 116 (.leaf 509015865) (.leaf 499370142))) (.branch 119 (.branch 118 (.leaf 489915907) (.leaf 480649009)) (.branch 120 (.leaf 471565398) (.leaf 462661127)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1043).prefactor = (2556585152110743/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1043).cutoff/(generalMeanRows 1043).c)).2 =
    (81417800971937/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1043).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1043).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1043).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1043

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1043).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1043).criticalRate j.val*(generalMeanRows 1043).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1043).c*(generalMeanRows 1043).criticalPoint j.val)).2-
      (generalMeanRows 1043).J/2-(generalMeanRows 1043).error (generalMeanGrid j.val)+
      (generalMeanRows 1043).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1043).c)).2-
      (generalMeanRows 1043).J/2-(generalMeanRows 1043).error 4 := by
  have he : (generalMeanRows 1043).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1043) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1043)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1043

/-! Kernel-checked entropy margins for general spectral rectangle 1044. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1044
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6529195143) (.branch 2 (.leaf 6337194136) (.leaf 6152805740))) (.branch 5 (.branch 4 (.leaf 5975626080) (.leaf 5805279177)) (.branch 6 (.leaf 5641414475) (.leaf 5483704654)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5331843664) (.leaf 5185544980)) (.branch 10 (.leaf 5044540028) (.leaf 4908576767))) (.branch 13 (.branch 12 (.leaf 4777418420) (.leaf 4650842311)) (.branch 14 (.leaf 4528638829) (.leaf 4410610466))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4296570963) (.branch 17 (.leaf 4186344511) (.leaf 4079765037))) (.branch 20 (.branch 19 (.leaf 3976675537) (.leaf 3876927474)) (.branch 21 (.leaf 3780380222) (.leaf 3686900547)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3596362143) (.leaf 3508645191)) (.branch 25 (.leaf 3423635957) (.leaf 3341226420))) (.branch 28 (.branch 27 (.leaf 3261313925) (.leaf 3183800864)) (.branch 29 (.leaf 3108594378) (.leaf 3035606078)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2964751791) (.branch 32 (.leaf 2895951315) (.leaf 2829128201))) (.branch 35 (.branch 34 (.leaf 2764209537) (.leaf 2701125759)) (.branch 36 (.leaf 2639810463) (.leaf 2580200238)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2522234501) (.leaf 2465855354)) (.branch 40 (.leaf 2411007434) (.leaf 2357637789))) (.branch 43 (.branch 42 (.leaf 2305695748) (.leaf 2255132805)) (.branch 44 (.leaf 2205902513) (.leaf 2157960374))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2111263748) (.branch 47 (.leaf 2065771756) (.leaf 2021445196))) (.branch 50 (.branch 49 (.leaf 1978246462) (.leaf 1936139463)) (.branch 51 (.leaf 1895089554) (.leaf 1855063466)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1816029241) (.leaf 1777956169)) (.branch 55 (.leaf 1740814730) (.leaf 1704576543))) (.branch 58 (.branch 57 (.leaf 1669214307) (.leaf 1634701756)) (.branch 59 (.leaf 1601013614) (.leaf 1568125543))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1536014109) (.branch 62 (.leaf 1504656737) (.leaf 1474031675))) (.branch 65 (.branch 64 (.leaf 1444117959) (.leaf 1414895374)) (.branch 66 (.leaf 1386344427) (.leaf 1358446315)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1331182891) (.leaf 1304536643)) (.branch 70 (.leaf 1278490661) (.leaf 1253028617))) (.branch 73 (.branch 72 (.leaf 1228134737) (.leaf 1203793780)) (.branch 74 (.leaf 1179991016) (.leaf 1156712205))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1133943576) (.branch 77 (.leaf 1111671810) (.leaf 1089884021))) (.branch 80 (.branch 79 (.leaf 1068567739) (.leaf 1047710893)) (.branch 81 (.leaf 1027301796) (.leaf 1007329131)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 987781934) (.leaf 968649583)) (.branch 85 (.leaf 949921783) (.leaf 931588556))) (.branch 88 (.branch 87 (.leaf 913640226) (.leaf 896067410)) (.branch 89 (.leaf 878861007) (.leaf 862012186)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 845512378) (.branch 92 (.leaf 829353265) (.leaf 813526771))) (.branch 95 (.branch 94 (.leaf 798025054) (.leaf 782840499)) (.branch 96 (.leaf 767965704) (.leaf 753393482)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 739116846) (.leaf 725129002)) (.branch 100 (.leaf 711423349) (.leaf 697993465))) (.branch 103 (.branch 102 (.leaf 684833104) (.leaf 671936192)) (.branch 104 (.leaf 659296817) (.leaf 646909227))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 634767824) (.leaf 622867156)) (.branch 108 (.leaf 611201916) (.leaf 599766937))) (.branch 111 (.branch 110 (.leaf 588557185) (.leaf 577567756)) (.branch 112 (.leaf 566793874) (.leaf 556230881)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 545874242) (.leaf 535719532)) (.branch 116 (.leaf 525762440) (.leaf 515998761))) (.branch 119 (.branch 118 (.leaf 506424395) (.leaf 497035343)) (.branch 120 (.leaf 487827703) (.leaf 478797668)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1044).prefactor = (5010098897659089/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1044).cutoff/(generalMeanRows 1044).c)).2 =
    (69513521151863/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1044).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1044).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1044).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1044

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1044).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1044).criticalRate j.val*(generalMeanRows 1044).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1044).c*(generalMeanRows 1044).criticalPoint j.val)).2-
      (generalMeanRows 1044).J/2-(generalMeanRows 1044).error (generalMeanGrid j.val)+
      (generalMeanRows 1044).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1044).c)).2-
      (generalMeanRows 1044).J/2-(generalMeanRows 1044).error 4 := by
  have he : (generalMeanRows 1044).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1044) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1044)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1044

/-! Kernel-checked entropy margins for general spectral rectangle 1045. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1045
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6291760320) (.branch 2 (.leaf 6106793672) (.leaf 5929211260))) (.branch 5 (.branch 4 (.leaf 5758617466) (.leaf 5594644130)) (.branch 6 (.leaf 5436948126) (.leaf 5285209205)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5139128069) (.leaf 4998424644)) (.branch 10 (.leaf 4862836536) (.leaf 4732117637))) (.branch 13 (.branch 12 (.leaf 4606036863) (.leaf 4484377019)) (.branch 14 (.leaf 4366933766) (.leaf 4253514683))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4143938411) (.branch 17 (.leaf 4038033877) (.leaf 3935639576))) (.branch 20 (.branch 19 (.leaf 3836602925) (.leaf 3740779656)) (.branch 21 (.leaf 3648033272) (.leaf 3558234537)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3471261013) (.leaf 3386996623)) (.branch 25 (.leaf 3305331259) (.leaf 3226160409))) (.branch 28 (.branch 27 (.leaf 3149384817) (.leaf 3074910169)) (.branch 29 (.leaf 3002646793) (.leaf 2932509391)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2864416779) (.branch 32 (.leaf 2798291657) (.leaf 2734060382))) (.branch 35 (.branch 34 (.leaf 2671652761) (.leaf 2611001865)) (.branch 36 (.leaf 2552043842) (.leaf 2494717751)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2438965405) (.leaf 2384731220)) (.branch 40 (.leaf 2331962079) (.leaf 2280607203))) (.branch 43 (.branch 42 (.leaf 2230618024) (.leaf 2181948073)) (.branch 44 (.leaf 2134552875) (.leaf 2088389839))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2043418172) (.branch 47 (.leaf 1999598783) (.leaf 1956894199))) (.branch 50 (.branch 49 (.leaf 1915268485) (.leaf 1874687172)) (.branch 51 (.leaf 1835117179) (.leaf 1796526752)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1758885397) (.leaf 1722163820)) (.branch 55 (.leaf 1686333874) (.leaf 1651368500))) (.branch 58 (.branch 57 (.leaf 1617241678) (.leaf 1583928381)) (.branch 59 (.leaf 1551404528) (.leaf 1519646939))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1488633298) (.branch 62 (.leaf 1458342111) (.leaf 1428752669))) (.branch 65 (.branch 64 (.leaf 1399845015) (.leaf 1371599913)) (.branch 66 (.leaf 1343998809) (.leaf 1317023809)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1290657648) (.leaf 1264883660)) (.branch 70 (.leaf 1239685756) (.leaf 1215048401))) (.branch 73 (.branch 72 (.leaf 1190956584) (.leaf 1167395804)) (.branch 74 (.leaf 1144352044) (.leaf 1121811752))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1099761822) (.branch 77 (.leaf 1078189579) (.leaf 1057082754))) (.branch 80 (.branch 79 (.leaf 1036429478) (.leaf 1016218257)) (.branch 81 (.leaf 996437962) (.leaf 977077815)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 958127370) (.leaf 939576509)) (.branch 85 (.leaf 921415421) (.leaf 903634594))) (.branch 88 (.branch 87 (.leaf 886224806) (.leaf 869177109)) (.branch 89 (.leaf 852482821) (.leaf 836133519)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 820121025) (.branch 92 (.leaf 804437399) (.leaf 789074930))) (.branch 95 (.branch 94 (.leaf 774026130) (.leaf 759283722)) (.branch 96 (.leaf 744840635) (.leaf 730689997)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 716825126) (.leaf 703239527)) (.branch 100 (.leaf 689926882) (.leaf 676881044))) (.branch 103 (.branch 102 (.leaf 664096035) (.leaf 651566035)) (.branch 104 (.leaf 639285381) (.leaf 627248561))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 615450206) (.leaf 603885090)) (.branch 108 (.leaf 592548119) (.leaf 581434336))) (.branch 111 (.branch 110 (.leaf 570538907) (.leaf 559857122)) (.branch 112 (.leaf 549384392) (.leaf 539116242)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 529048311) (.leaf 519176343)) (.branch 116 (.leaf 509496190) (.leaf 500003806))) (.branch 119 (.branch 118 (.leaf 490695243) (.leaf 481566649)) (.branch 120 (.leaf 472614266) (.leaf 463834425)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1045).prefactor = (4906759121548101/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1045).cutoff/(generalMeanRows 1045).c)).2 =
    (364149618355453/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1045).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1045).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1045).q*(generalMeanRows 1045).cutoff/2-2 = (23/12:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable028.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1045).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1045

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1045).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1045).criticalRate j.val*(generalMeanRows 1045).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1045).c*(generalMeanRows 1045).criticalPoint j.val)).2-
      (generalMeanRows 1045).J/2-(generalMeanRows 1045).error (generalMeanGrid j.val)+
      (generalMeanRows 1045).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1045).c)).2-
      (generalMeanRows 1045).J/2-(generalMeanRows 1045).error 4 := by
  have he : (generalMeanRows 1045).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1045) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1045)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1045

/-! Kernel-checked entropy margins for general spectral rectangle 1046. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1046
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6170987956) (.branch 2 (.leaf 5979818402) (.leaf 5796397297))) (.branch 5 (.branch 4 (.leaf 5620311029) (.leaf 5451174553)) (.branch 6 (.leaf 5288628873) (.leaf 5132338802)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4981990964) (.leaf 4837291999)) (.branch 10 (.leaf 4697966960) (.leaf 4563757862))) (.branch 13 (.branch 12 (.leaf 4434422376) (.leaf 4309732649)) (.branch 14 (.leaf 4189474227) (.leaf 4073445083))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3961454731) (.branch 17 (.leaf 3853323409) (.leaf 3748881349))) (.branch 20 (.branch 19 (.leaf 3647968087) (.leaf 3550431848)) (.branch 21 (.leaf 3456128973) (.leaf 3364923388)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3276686124) (.leaf 3191294866)) (.branch 25 (.leaf 3108633538) (.leaf 3028591921))) (.branch 28 (.branch 27 (.leaf 2951065300) (.leaf 2875954129)) (.branch 29 (.leaf 2803163729) (.leaf 2732604001)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2664189164) (.branch 32 (.leaf 2597837504) (.leaf 2533471148))) (.branch 35 (.branch 34 (.leaf 2471015844) (.leaf 2410400765)) (.branch 36 (.leaf 2351558319) (.leaf 2294423972)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2238936086) (.leaf 2185035763)) (.branch 40 (.leaf 2132666701) (.leaf 2081775056))) (.branch 43 (.branch 42 (.leaf 2032309318) (.leaf 1984220189)) (.branch 44 (.leaf 1937460469) (.leaf 1891984952))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1847750326) (.branch 47 (.leaf 1804715076) (.leaf 1762839400))) (.branch 50 (.branch 49 (.leaf 1722085120) (.leaf 1682415607)) (.branch 51 (.leaf 1643795705) (.leaf 1606191658)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1569571049) (.leaf 1533902733)) (.branch 55 (.leaf 1499156776) (.leaf 1465304405))) (.branch 58 (.branch 57 (.leaf 1432317948) (.leaf 1400170786)) (.branch 59 (.leaf 1368837307) (.leaf 1338292856))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1308513699) (.branch 62 (.leaf 1279476974) (.leaf 1251160658))) (.branch 65 (.branch 64 (.leaf 1223543530) (.leaf 1196605133)) (.branch 66 (.leaf 1170325742) (.leaf 1144686334)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1119668559) (.leaf 1095254706)) (.branch 70 (.leaf 1071427682) (.leaf 1048170983))) (.branch 73 (.branch 72 (.leaf 1025468671) (.leaf 1003305349)) (.branch 74 (.leaf 981666140) (.leaf 960536667))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 939903029) (.branch 77 (.leaf 919751785) (.leaf 900069937))) (.branch 80 (.branch 79 (.leaf 880844908) (.leaf 862064528)) (.branch 81 (.leaf 843717018) (.leaf 825790975)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 808275357) (.leaf 791159470)) (.branch 85 (.leaf 774432951) (.leaf 758085762))) (.branch 88 (.branch 87 (.leaf 742108173) (.leaf 726490751)) (.branch 89 (.leaf 711224351) (.leaf 696300103)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 681709403) (.branch 92 (.leaf 667443905) (.leaf 653495510))) (.branch 95 (.branch 94 (.leaf 639856354) (.leaf 626518807)) (.branch 96 (.leaf 613475459) (.leaf 600719113)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 588242779) (.leaf 576039667)) (.branch 100 (.leaf 564103178) (.leaf 552426901))) (.branch 103 (.branch 102 (.leaf 541004603) (.leaf 529830223)) (.branch 104 (.leaf 518897870) (.leaf 508201815))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 497736485) (.leaf 487496457)) (.branch 108 (.leaf 477476457) (.leaf 467671351))) (.branch 111 (.branch 110 (.leaf 458076144) (.leaf 448685973)) (.branch 112 (.leaf 439496103) (.leaf 430501925)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 421698948) (.leaf 413082802)) (.branch 116 (.leaf 404649226) (.leaf 396394072))) (.branch 119 (.branch 118 (.leaf 388313296) (.leaf 380402959)) (.branch 120 (.leaf 372659222) (.leaf 365078341)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1046).prefactor = (5105763409703809/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1046).cutoff/(generalMeanRows 1046).c)).2 =
    (169375713874921/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1046).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1046).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1046).q*(generalMeanRows 1046).cutoff/2-2 = (23/12:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable028.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1046).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1046

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1046).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1046).criticalRate j.val*(generalMeanRows 1046).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1046).c*(generalMeanRows 1046).criticalPoint j.val)).2-
      (generalMeanRows 1046).J/2-(generalMeanRows 1046).error (generalMeanGrid j.val)+
      (generalMeanRows 1046).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1046).c)).2-
      (generalMeanRows 1046).J/2-(generalMeanRows 1046).error 4 := by
  have he : (generalMeanRows 1046).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1046) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1046)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1046

/-! Kernel-checked entropy margins for general spectral rectangle 1047. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1047
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6025048241) (.branch 2 (.leaf 5841155893) (.leaf 5664732437))) (.branch 5 (.branch 4 (.leaf 5495374810) (.leaf 5332707985)) (.branch 6 (.leaf 5176382508) (.leaf 5026072290)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4881472651) (.leaf 4742298558)) (.branch 10 (.leaf 4608283043) (.leaf 4479175781))) (.branch 13 (.branch 12 (.leaf 4354741805) (.leaf 4234760337)) (.branch 14 (.leaf 4119023738) (.leaf 4007336548))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3899514605) (.branch 17 (.leaf 3795384255) (.leaf 3694781616))) (.branch 20 (.branch 19 (.leaf 3597551912) (.leaf 3503548859)) (.branch 21 (.leaf 3412634101) (.leaf 3324676691)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3239552614) (.leaf 3157144341)) (.branch 25 (.leaf 3077340429) (.leaf 3000035134))) (.branch 28 (.branch 27 (.leaf 2925128067) (.leaf 2852523870)) (.branch 29 (.leaf 2782131910) (.leaf 2713866004)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2647644154) (.branch 32 (.leaf 2583388306) (.leaf 2521024128))) (.branch 35 (.branch 34 (.leaf 2460480790) (.leaf 2401690774)) (.branch 36 (.leaf 2344589688) (.leaf 2289116091)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2235211336) (.leaf 2182819414)) (.branch 40 (.leaf 2131886818) (.leaf 2082362404))) (.branch 43 (.branch 42 (.leaf 2034197271) (.leaf 1987344643)) (.branch 44 (.leaf 1941759754) (.leaf 1897399754))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1854223601) (.branch 47 (.leaf 1812191979) (.leaf 1771267203))) (.branch 50 (.branch 49 (.leaf 1731413143) (.leaf 1692595148)) (.branch 51 (.leaf 1654779969) (.leaf 1617935693)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1582031681) (.leaf 1547038503)) (.branch 55 (.leaf 1512927881) (.leaf 1479672640))) (.branch 58 (.branch 57 (.leaf 1447246647) (.leaf 1415624772)) (.branch 59 (.leaf 1384782835) (.leaf 1354697564))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1325346558) (.branch 62 (.leaf 1296708241) (.leaf 1268761830))) (.branch 65 (.branch 64 (.leaf 1241487295) (.leaf 1214865332)) (.branch 66 (.leaf 1188877325) (.leaf 1163505322)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1138731998) (.leaf 1114540637)) (.branch 70 (.leaf 1090915101) (.leaf 1067839806))) (.branch 73 (.branch 72 (.leaf 1045299700) (.leaf 1023280238)) (.branch 74 (.leaf 1001767365) (.leaf 980747494))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 960207485) (.branch 77 (.leaf 940134631) (.leaf 920516635))) (.branch 80 (.branch 79 (.leaf 901341600) (.leaf 882598007)) (.branch 81 (.leaf 864274705) (.leaf 846360893)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 828846110) (.leaf 811720217)) (.branch 85 (.leaf 794973390) (.leaf 778596105))) (.branch 88 (.branch 87 (.leaf 762579126) (.leaf 746913496)) (.branch 89 (.leaf 731590527) (.leaf 716601789)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 701939099) (.branch 92 (.leaf 687594515) (.leaf 673560327))) (.branch 95 (.branch 94 (.leaf 659829045) (.leaf 646393396)) (.branch 96 (.leaf 633246314) (.leaf 620380932)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 607790576) (.leaf 595468760)) (.branch 100 (.leaf 583409177) (.leaf 571605692))) (.branch 103 (.branch 102 (.leaf 560052341) (.leaf 548743320)) (.branch 104 (.leaf 537672983) (.leaf 526835835))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 516226529) (.leaf 505839859)) (.branch 108 (.leaf 495670757) (.leaf 485714286))) (.branch 111 (.branch 110 (.leaf 475965641) (.leaf 466420138)) (.branch 112 (.leaf 457073217) (.leaf 447920433)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 438957455) (.leaf 430180062)) (.branch 116 (.leaf 421584139) (.leaf 413165674))) (.branch 119 (.branch 118 (.leaf 404920757) (.leaf 396845572)) (.branch 120 (.leaf 388936401) (.leaf 381189614)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1047).prefactor = (4985064449104499/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1047).cutoff/(generalMeanRows 1047).c)).2 =
    (363292536665959/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1047).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1047).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1047).q*(generalMeanRows 1047).cutoff/2-2 = (1619/812:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable339.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1047).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1047

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1047).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1047).criticalRate j.val*(generalMeanRows 1047).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1047).c*(generalMeanRows 1047).criticalPoint j.val)).2-
      (generalMeanRows 1047).J/2-(generalMeanRows 1047).error (generalMeanGrid j.val)+
      (generalMeanRows 1047).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1047).c)).2-
      (generalMeanRows 1047).J/2-(generalMeanRows 1047).error 4 := by
  have he : (generalMeanRows 1047).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1047) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1047)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1047

/-! Kernel-checked entropy margins for general spectral rectangle 1048. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1048
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5811024338) (.branch 2 (.leaf 5622285785) (.leaf 5441374319))) (.branch 5 (.branch 4 (.leaf 5267868759) (.leaf 5101377042)) (.branch 6 (.leaf 4941533669) (.leaf 4787997426)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4640449349) (.leaf 4498590905)) (.branch 10 (.leaf 4362142350) (.leaf 4230841256))) (.branch 13 (.branch 12 (.leaf 4104441178) (.leaf 3982710450)) (.branch 14 (.leaf 3865431086) (.leaf 3752397788))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3643417040) (.branch 17 (.leaf 3538306278) (.leaf 3436893132))) (.branch 20 (.branch 19 (.leaf 3339014738) (.leaf 3244517093)) (.branch 21 (.leaf 3153254477) (.leaf 3065088913)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2979889667) (.leaf 2897532792)) (.branch 25 (.leaf 2817900704) (.leaf 2740881790))) (.branch 28 (.branch 27 (.leaf 2666370045) (.leaf 2594264732)) (.branch 29 (.leaf 2524470071) (.leaf 2456894949)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2391452645) (.branch 32 (.leaf 2328060581) (.leaf 2266640084))) (.branch 35 (.branch 34 (.leaf 2207116169) (.leaf 2149417330)) (.branch 36 (.leaf 2093475352) (.leaf 2039225127)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1986604491) (.leaf 1935554061)) (.branch 40 (.leaf 1886017090) (.leaf 1837939330))) (.branch 43 (.branch 42 (.leaf 1791268897) (.leaf 1745956153)) (.branch 44 (.leaf 1701953588) (.leaf 1659215715))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1617698965) (.branch 47 (.leaf 1577361592) (.leaf 1538163581))) (.branch 50 (.branch 49 (.leaf 1500066568) (.leaf 1463033754)) (.branch 51 (.leaf 1427029831) (.leaf 1392020909)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1357974454) (.leaf 1324859215)) (.branch 55 (.leaf 1292645170) (.leaf 1261303468))) (.branch 58 (.branch 57 (.leaf 1230806372) (.leaf 1201127210)) (.branch 59 (.leaf 1172240327) (.leaf 1144121035))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1116745575) (.branch 62 (.leaf 1090091072) (.leaf 1064135496))) (.branch 65 (.branch 64 (.leaf 1038857626) (.leaf 1014237013)) (.branch 66 (.leaf 990253950) (.leaf 966889433)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 944125141) (.leaf 921943396)) (.branch 70 (.leaf 900327144) (.leaf 879259927))) (.branch 73 (.branch 72 (.leaf 858725854) (.leaf 838709583)) (.branch 74 (.leaf 819196296) (.leaf 800171677))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 781621893) (.branch 77 (.leaf 763533573) (.leaf 745893792))) (.branch 80 (.branch 79 (.leaf 728690051) (.leaf 711910261)) (.branch 81 (.leaf 695542727) (.leaf 679576132)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 663999525) (.leaf 648802302)) (.branch 85 (.leaf 633974199) (.leaf 619505272))) (.branch 88 (.branch 87 (.leaf 605385892) (.leaf 591606730)) (.branch 89 (.leaf 578158742) (.leaf 565033168)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 552221511) (.branch 92 (.leaf 539715536) (.leaf 527507254))) (.branch 95 (.branch 94 (.leaf 515588919) (.leaf 503953014)) (.branch 96 (.leaf 492592247) (.leaf 481499540)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 470668023) (.leaf 460091028)) (.branch 100 (.leaf 449762080) (.leaf 439674890))) (.branch 103 (.branch 102 (.leaf 429823352) (.leaf 420201532)) (.branch 104 (.leaf 410803667) (.leaf 401624155))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 392657553) (.leaf 383898571)) (.branch 108 (.leaf 375342064) (.leaf 366983032))) (.branch 111 (.branch 110 (.leaf 358816611) (.leaf 350838074)) (.branch 112 (.leaf 343042818) (.leaf 335426371)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 327984378) (.leaf 320712602)) (.branch 116 (.leaf 313606922) (.leaf 306663325))) (.branch 119 (.branch 118 (.leaf 299877905) (.leaf 293246861)) (.branch 120 (.leaf 286766491) (.leaf 280433190)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1048).prefactor = (5173987400135099/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1048).cutoff/(generalMeanRows 1048).c)).2 =
    (166354556646941/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1048).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1048).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1048).q*(generalMeanRows 1048).c/2-2 = (1727/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable337.value]
    have hcontinuation : (generalMeanRows 1048).q*(generalMeanRows 1048).cutoff/2-2 = (1619/812:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable339.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1048).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1048

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1048).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1048).criticalRate j.val*(generalMeanRows 1048).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1048).c*(generalMeanRows 1048).criticalPoint j.val)).2-
      (generalMeanRows 1048).J/2-(generalMeanRows 1048).error (generalMeanGrid j.val)+
      (generalMeanRows 1048).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1048).c)).2-
      (generalMeanRows 1048).J/2-(generalMeanRows 1048).error 4 := by
  have he : (generalMeanRows 1048).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1048) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1048)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1048

/-! Kernel-checked entropy margins for general spectral rectangle 1049. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1049
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5879378530) (.branch 2 (.leaf 5697215392) (.leaf 5522532444))) (.branch 5 (.branch 4 (.leaf 5354922215) (.leaf 5194005727)) (.branch 6 (.leaf 5039429987) (.leaf 4890865755)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4748005546) (.leaf 4610561843)) (.branch 10 (.leaf 4478265487) (.leaf 4350864231))) (.branch 13 (.branch 12 (.leaf 4228121425) (.leaf 4109814835)) (.branch 14 (.leaf 3995735568) (.leaf 3885687088))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3779484330) (.branch 17 (.leaf 3676952886) (.leaf 3577928255))) (.branch 20 (.branch 19 (.leaf 3482255168) (.leaf 3389786959)) (.branch 21 (.leaf 3300384988) (.leaf 3213918118)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3130262220) (.leaf 3049299727)) (.branch 25 (.leaf 2970919218) (.leaf 2895015032))) (.branch 28 (.branch 27 (.leaf 2821486911) (.leaf 2750239672)) (.branch 29 (.leaf 2681182897) (.leaf 2614230650)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2549301210) (.branch 32 (.leaf 2486316827) (.leaf 2425203489))) (.branch 35 (.branch 34 (.leaf 2365890709) (.leaf 2308311324)) (.branch 36 (.leaf 2252401308) (.leaf 2198099597)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2145347926) (.leaf 2094090676)) (.branch 40 (.leaf 2044274729) (.leaf 1995849334))) (.branch 43 (.branch 42 (.leaf 1948765982) (.leaf 1902978288)) (.branch 44 (.leaf 1858441874) (.leaf 1815114274))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1772954827) (.branch 47 (.leaf 1731924589) (.leaf 1691986246))) (.branch 50 (.branch 49 (.leaf 1653104030) (.leaf 1615243643)) (.branch 51 (.leaf 1578372185) (.leaf 1542458082)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1507471026) (.leaf 1473381911)) (.branch 55 (.leaf 1440162774) (.leaf 1407786745))) (.branch 58 (.branch 57 (.leaf 1376227989) (.leaf 1345461664)) (.branch 59 (.leaf 1315463871) (.leaf 1286211609))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1257682740) (.branch 62 (.leaf 1229855940) (.leaf 1202710674))) (.branch 65 (.branch 64 (.leaf 1176227149) (.leaf 1150386290)) (.branch 66 (.leaf 1125169703) (.leaf 1100559647)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1076539005) (.leaf 1053091260)) (.branch 70 (.leaf 1030200462) (.leaf 1007851213))) (.branch 73 (.branch 72 (.leaf 986028636) (.leaf 964718359)) (.branch 74 (.leaf 943906490) (.leaf 923579598))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 903724695) (.branch 77 (.leaf 884329220) (.leaf 865381017))) (.branch 80 (.branch 79 (.leaf 846868321) (.leaf 828779744)) (.branch 81 (.leaf 811104259) (.leaf 793831184)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 776950172) (.leaf 760451195)) (.branch 85 (.leaf 744324535) (.leaf 728560769))) (.branch 88 (.branch 87 (.leaf 713150759) (.leaf 698085644)) (.branch 89 (.leaf 683356824) (.leaf 668955957)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 654874944) (.branch 92 (.leaf 641105924) (.leaf 627641264))) (.branch 95 (.branch 94 (.leaf 614473550) (.leaf 601595580)) (.branch 96 (.leaf 589000359) (.leaf 576681086)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 564631154) (.leaf 552844137)) (.branch 100 (.leaf 541313790) (.leaf 530034038))) (.branch 103 (.branch 102 (.leaf 518998972) (.leaf 508202845)) (.branch 104 (.leaf 497640063) (.leaf 487305185))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 477192913) (.leaf 467298090)) (.branch 108 (.leaf 457615696) (.leaf 448140842))) (.branch 111 (.branch 110 (.leaf 438868767) (.leaf 429794833)) (.branch 112 (.leaf 420914523) (.leaf 412223433)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 403717275) (.leaf 395391869)) (.branch 116 (.leaf 387243138) (.leaf 379267113))) (.branch 119 (.branch 118 (.leaf 371459918) (.leaf 363817780)) (.branch 120 (.leaf 356337014) (.leaf 349014030)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1049).prefactor = (503837096431961/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1049).cutoff/(generalMeanRows 1049).c)).2 =
    (74768549512223/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1049).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1049).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1049).q*(generalMeanRows 1049).c/2-2 = (161/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable110.value]
    have hcontinuation : (generalMeanRows 1049).q*(generalMeanRows 1049).cutoff/2-2 = (407/196:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable340.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1049).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1049

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1049).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1049).criticalRate j.val*(generalMeanRows 1049).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1049).c*(generalMeanRows 1049).criticalPoint j.val)).2-
      (generalMeanRows 1049).J/2-(generalMeanRows 1049).error (generalMeanGrid j.val)+
      (generalMeanRows 1049).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1049).c)).2-
      (generalMeanRows 1049).J/2-(generalMeanRows 1049).error 4 := by
  have he : (generalMeanRows 1049).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1049) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1049)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1049

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock14 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 14 i) := by
  fin_cases i
  · exact EntropyRow0980.numerical
  · exact EntropyRow0981.numerical
  · exact EntropyRow0982.numerical
  · exact EntropyRow0983.numerical
  · exact EntropyRow0984.numerical
  · exact EntropyRow0985.numerical
  · exact EntropyRow0986.numerical
  · exact EntropyRow0987.numerical
  · exact EntropyRow0988.numerical
  · exact EntropyRow0989.numerical
  · exact EntropyRow0990.numerical
  · exact EntropyRow0991.numerical
  · exact EntropyRow0992.numerical
  · exact EntropyRow0993.numerical
  · exact EntropyRow0994.numerical
  · exact EntropyRow0995.numerical
  · exact EntropyRow0996.numerical
  · exact EntropyRow0997.numerical
  · exact EntropyRow0998.numerical
  · exact EntropyRow0999.numerical
  · exact EntropyRow1000.numerical
  · exact EntropyRow1001.numerical
  · exact EntropyRow1002.numerical
  · exact EntropyRow1003.numerical
  · exact EntropyRow1004.numerical
  · exact EntropyRow1005.numerical
  · exact EntropyRow1006.numerical
  · exact EntropyRow1007.numerical
  · exact EntropyRow1008.numerical
  · exact EntropyRow1009.numerical
  · exact EntropyRow1010.numerical
  · exact EntropyRow1011.numerical
  · exact EntropyRow1012.numerical
  · exact EntropyRow1013.numerical
  · exact EntropyRow1014.numerical
  · exact EntropyRow1015.numerical
  · exact EntropyRow1016.numerical
  · exact EntropyRow1017.numerical
  · exact EntropyRow1018.numerical
  · exact EntropyRow1019.numerical
  · exact EntropyRow1020.numerical
  · exact EntropyRow1021.numerical
  · exact EntropyRow1022.numerical
  · exact EntropyRow1023.numerical
  · exact EntropyRow1024.numerical
  · exact EntropyRow1025.numerical
  · exact EntropyRow1026.numerical
  · exact EntropyRow1027.numerical
  · exact EntropyRow1028.numerical
  · exact EntropyRow1029.numerical
  · exact EntropyRow1030.numerical
  · exact EntropyRow1031.numerical
  · exact EntropyRow1032.numerical
  · exact EntropyRow1033.numerical
  · exact EntropyRow1034.numerical
  · exact EntropyRow1035.numerical
  · exact EntropyRow1036.numerical
  · exact EntropyRow1037.numerical
  · exact EntropyRow1038.numerical
  · exact EntropyRow1039.numerical
  · exact EntropyRow1040.numerical
  · exact EntropyRow1041.numerical
  · exact EntropyRow1042.numerical
  · exact EntropyRow1043.numerical
  · exact EntropyRow1044.numerical
  · exact EntropyRow1045.numerical
  · exact EntropyRow1046.numerical
  · exact EntropyRow1047.numerical
  · exact EntropyRow1048.numerical
  · exact EntropyRow1049.numerical
end SingularValueBounds.KL.Certificates
