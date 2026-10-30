import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block00
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block01
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block02
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block03
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block04
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block05
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 70. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0070
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5773151420) (.branch 2 (.leaf 5584379588) (.leaf 5404542897))) (.branch 5 (.branch 4 (.leaf 5233098640) (.leaf 5069543620)) (.branch 6 (.leaf 4913410704) (.leaf 4764265736)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4621704773) (.leaf 4485351606)) (.branch 10 (.leaf 4354855514) (.leaf 4229889248))) (.branch 13 (.branch 12 (.leaf 4110147195) (.leaf 3995343718)) (.branch 14 (.leaf 3885211645) (.leaf 3779500893))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3677977207) (.branch 17 (.leaf 3580421018) (.leaf 3486626384))) (.branch 20 (.branch 19 (.leaf 3396400028) (.leaf 3309560452)) (.branch 21 (.leaf 3225937123) (.leaf 3145369717)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3067707433) (.leaf 2992808350)) (.branch 25 (.leaf 2920538838) (.leaf 2850773014))) (.branch 28 (.branch 27 (.leaf 2783392232) (.leaf 2718284617)) (.branch 29 (.leaf 2655344631) (.leaf 2594472666)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2535574675) (.branch 32 (.leaf 2478561816) (.leaf 2423350133))) (.branch 35 (.branch 34 (.leaf 2369860254) (.leaf 2318017105)) (.branch 36 (.leaf 2267749652) (.leaf 2218990654)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2171676437) (.leaf 2125746676)) (.branch 40 (.leaf 2081144200) (.leaf 2037814806))) (.branch 43 (.branch 42 (.leaf 1995707079) (.leaf 1954772235)) (.branch 44 (.leaf 1914963965) (.leaf 1876238294))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1838553444) (.branch 47 (.leaf 1801869710) (.leaf 1766149344))) (.branch 50 (.branch 49 (.leaf 1731356441) (.leaf 1697456838)) (.branch 51 (.leaf 1664418016) (.leaf 1632209006)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1600800308) (.leaf 1570163804)) (.branch 55 (.leaf 1540272690) (.leaf 1511101397))) (.branch 58 (.branch 57 (.leaf 1482625529) (.leaf 1454821796)) (.branch 59 (.leaf 1427667959) (.leaf 1401142769))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1375225921) (.branch 62 (.leaf 1349897997) (.leaf 1325140424))) (.branch 65 (.branch 64 (.leaf 1300935428) (.leaf 1277265994)) (.branch 66 (.leaf 1254115826) (.leaf 1231469309)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1209311477) (.leaf 1187627978)) (.branch 70 (.leaf 1166405042) (.leaf 1145629454))) (.branch 73 (.branch 72 (.leaf 1125288528) (.leaf 1105370074)) (.branch 74 (.leaf 1085862382) (.leaf 1066754192))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1048034675) (.branch 77 (.leaf 1029693412) (.leaf 1011720376))) (.branch 80 (.branch 79 (.leaf 994105908) (.leaf 976840704)) (.branch 81 (.leaf 959915800) (.leaf 943322549)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 927052614) (.leaf 911097950)) (.branch 85 (.leaf 895450789) (.leaf 880103631))) (.branch 88 (.branch 87 (.leaf 865049231) (.leaf 850280586)) (.branch 89 (.leaf 835790925) (.leaf 821573701)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 807622576) (.branch 92 (.leaf 793931419) (.leaf 780494290))) (.branch 95 (.branch 94 (.leaf 767305438) (.leaf 754359288)) (.branch 96 (.leaf 741650438) (.leaf 729173648)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 716923836) (.leaf 704896069)) (.branch 100 (.leaf 693085561) (.leaf 681487663))) (.branch 103 (.branch 102 (.leaf 670097860) (.leaf 658911765)) (.branch 104 (.leaf 647925113) (.leaf 637133759))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 626533670) (.leaf 616120924)) (.branch 108 (.leaf 605891704) (.leaf 595842293))) (.branch 111 (.branch 110 (.leaf 585969074) (.leaf 576268522)) (.branch 112 (.leaf 566737205) (.leaf 557371777)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 548168978) (.leaf 539125627)) (.branch 116 (.leaf 530238625) (.leaf 521504946))) (.branch 119 (.branch 118 (.leaf 512921640) (.leaf 504485827)) (.branch 120 (.leaf 496194696) (.leaf 488045501)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 70).prefactor = (5290013569953033/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 70).cutoff/(generalMeanRows 70).c)).2 =
    (591713743237/1250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 70).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 70).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 70).q*(generalMeanRows 70).c/2-2 = (51/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable036.value]
    have hcontinuation : (generalMeanRows 70).q*(generalMeanRows 70).cutoff/2-2 = (248/111:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable041.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 70).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 70

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 70).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 70).criticalRate j.val*(generalMeanRows 70).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 70).c*(generalMeanRows 70).criticalPoint j.val)).2-
      (generalMeanRows 70).J/2-(generalMeanRows 70).error (generalMeanGrid j.val)+
      (generalMeanRows 70).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 70).c)).2-
      (generalMeanRows 70).J/2-(generalMeanRows 70).error 4 := by
  have he : (generalMeanRows 70).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 70) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 70)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0070

/-! Kernel-checked entropy margins for general spectral rectangle 71. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0071
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5198404706) (.branch 2 (.leaf 5007337545) (.leaf 4825507242))) (.branch 5 (.branch 4 (.leaf 4652357239) (.leaf 4487371294)) (.branch 6 (.leaf 4330069961) (.leaf 4180007445)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4036768780) (.leaf 3899967295)) (.branch 10 (.leaf 3769242333) (.leaf 3644257189))) (.branch 13 (.branch 12 (.leaf 3524697240) (.leaf 3410268254)) (.branch 14 (.leaf 3300694849) (.leaf 3195719089))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3095099208) (.branch 17 (.leaf 2998608433) (.leaf 2906033919))) (.branch 20 (.branch 19 (.leaf 2817175763) (.leaf 2731846100)) (.branch 21 (.leaf 2649868278) (.leaf 2571076088)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2495313065) (.leaf 2422431834)) (.branch 25 (.leaf 2352293509) (.leaf 2284767140))) (.branch 28 (.branch 27 (.leaf 2219729197) (.leaf 2157063092)) (.branch 29 (.leaf 2096658737) (.leaf 2038412135)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1982224997) (.branch 32 (.leaf 1928004385) (.leaf 1875662386))) (.branch 35 (.branch 34 (.leaf 1825115802) (.leaf 1776285863)) (.branch 36 (.leaf 1729097962) (.leaf 1683481401)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1639369166) (.leaf 1596697701)) (.branch 40 (.leaf 1555406711) (.leaf 1515438967))) (.branch 43 (.branch 42 (.leaf 1476740134) (.leaf 1439258600)) (.branch 44 (.leaf 1402945319) (.leaf 1367753670))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1333639318) (.branch 47 (.leaf 1300560082) (.leaf 1268475821))) (.branch 50 (.branch 49 (.leaf 1237348313) (.leaf 1207141158)) (.branch 51 (.leaf 1177819671) (.leaf 1149350791)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1121702993) (.leaf 1094846206)) (.branch 55 (.leaf 1068751733) (.leaf 1043392180))) (.branch 58 (.branch 57 (.leaf 1018741384) (.leaf 994774352)) (.branch 59 (.leaf 971467198) (.leaf 948797084))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 926742167) (.branch 62 (.leaf 905281549) (.leaf 884395227))) (.branch 65 (.branch 64 (.leaf 864064047) (.leaf 844269665)) (.branch 66 (.leaf 824994499) (.leaf 806221700)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 787935108) (.leaf 770119223)) (.branch 70 (.leaf 752759171) (.leaf 735840671))) (.branch 73 (.branch 72 (.leaf 719350011) (.leaf 703274018)) (.branch 74 (.leaf 687600031) (.leaf 672315882))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 657409864) (.branch 77 (.leaf 642870720) (.leaf 628687612))) (.branch 80 (.branch 79 (.leaf 614850110) (.leaf 601348167)) (.branch 81 (.leaf 588172105) (.leaf 575312598)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 562760656) (.leaf 550507609)) (.branch 85 (.leaf 538545092) (.leaf 526865037))) (.branch 88 (.branch 87 (.leaf 515459654) (.leaf 504321420)) (.branch 89 (.leaf 493443071) (.leaf 482817588)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 472438188) (.branch 92 (.leaf 462298312) (.leaf 452391617))) (.branch 95 (.branch 94 (.leaf 442711970) (.leaf 433253433)) (.branch 96 (.leaf 424010262) (.leaf 414976894)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 406147941) (.leaf 397518186)) (.branch 100 (.leaf 389082571) (.leaf 380836197))) (.branch 103 (.branch 102 (.leaf 372774313) (.leaf 364892311)) (.branch 104 (.leaf 357185723) (.leaf 349650213))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 342281575) (.leaf 335075725)) (.branch 108 (.leaf 328028698) (.leaf 321136644))) (.branch 111 (.branch 110 (.leaf 314395823) (.leaf 307802603)) (.branch 112 (.leaf 301353453) (.leaf 295044941)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 288873732) (.leaf 282836583)) (.branch 116 (.leaf 276930338) (.leaf 271151931))) (.branch 119 (.branch 118 (.leaf 265498375) (.leaf 259966767)) (.branch 120 (.leaf 254554279) (.leaf 249258160)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 71).prefactor = (5446307899279137/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 71).cutoff/(generalMeanRows 71).c)).2 =
    (204564362930623/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 71).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 71).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 71).q*(generalMeanRows 71).c/2-2 = (13/16:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable042.value]
    have hcontinuation : (generalMeanRows 71).q*(generalMeanRows 71).cutoff/2-2 = (248/111:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable041.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 71).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 71

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 71).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 71).criticalRate j.val*(generalMeanRows 71).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 71).c*(generalMeanRows 71).criticalPoint j.val)).2-
      (generalMeanRows 71).J/2-(generalMeanRows 71).error (generalMeanGrid j.val)+
      (generalMeanRows 71).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 71).c)).2-
      (generalMeanRows 71).J/2-(generalMeanRows 71).error 4 := by
  have he : (generalMeanRows 71).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 71) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 71)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0071

/-! Kernel-checked entropy margins for general spectral rectangle 72. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0072
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4882791147) (.branch 2 (.leaf 4689867650) (.leaf 4506462624))) (.branch 5 (.branch 4 (.leaf 4332003498) (.leaf 4165959036)) (.branch 6 (.leaf 4007835726) (.leaf 3857174561)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3713548148) (.leaf 3576558112)) (.branch 10 (.leaf 3445832759) (.leaf 3321024965))) (.branch 13 (.branch 12 (.leaf 3201810263) (.leaf 3087885106)) (.branch 14 (.leaf 2978965297) (.leaf 2874784543))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2775093154) (.branch 17 (.leaf 2679656838) (.leaf 2588255606))) (.branch 20 (.branch 19 (.leaf 2500682768) (.leaf 2416744005)) (.branch 21 (.leaf 2336256522) (.leaf 2259048267)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2184957205) (.leaf 2113830655)) (.branch 25 (.leaf 2045524677) (.leaf 1979903499))) (.branch 28 (.branch 27 (.leaf 1916838990) (.leaf 1856210173)) (.branch 29 (.leaf 1797902774) (.leaf 1741808795)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1687826130) (.branch 32 (.leaf 1635858195) (.leaf 1585813594))) (.branch 35 (.branch 34 (.leaf 1537605801) (.leaf 1491152867)) (.branch 36 (.leaf 1446377148) (.leaf 1403205045)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1361566768) (.leaf 1321396112)) (.branch 40 (.leaf 1282630248) (.leaf 1245209528))) (.branch 43 (.branch 42 (.leaf 1209077305) (.leaf 1174179755)) (.branch 44 (.leaf 1140465725) (.leaf 1107886576))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1076396048) (.branch 47 (.leaf 1045950121) (.leaf 1016506897))) (.branch 50 (.branch 49 (.leaf 988026482) (.leaf 960470874)) (.branch 51 (.leaf 933803863) (.leaf 907990935)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 882999176) (.leaf 858797194)) (.branch 55 (.leaf 835355032) (.leaf 812644096))) (.branch 58 (.branch 57 (.leaf 790637083) (.leaf 769307912)) (.branch 59 (.leaf 748631663) (.leaf 728584518))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 709143700) (.branch 62 (.leaf 690287426) (.leaf 671994851))) (.branch 65 (.branch 64 (.leaf 654246028) (.leaf 637021855)) (.branch 66 (.leaf 620304038) (.leaf 604075052)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 588318100) (.leaf 573017080)) (.branch 70 (.leaf 558156548) (.leaf 543721692))) (.branch 73 (.branch 72 (.leaf 529698295) (.leaf 516072713)) (.branch 74 (.leaf 502831844) (.leaf 489963104))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 477454400) (.branch 77 (.leaf 465294113) (.leaf 453471072))) (.branch 80 (.branch 79 (.leaf 441974533) (.leaf 430794162)) (.branch 81 (.leaf 419920015) (.leaf 409342521)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 399052466) (.leaf 389040974)) (.branch 85 (.leaf 379299498) (.leaf 369819800))) (.branch 88 (.branch 87 (.leaf 360593940) (.leaf 351614264)) (.branch 89 (.leaf 342873388) (.leaf 334364193)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 326079807) (.branch 92 (.leaf 318013599) (.leaf 310159168))) (.branch 95 (.branch 94 (.leaf 302510331) (.leaf 295061119)) (.branch 96 (.leaf 287805762) (.leaf 280738688)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 273854509) (.leaf 267148016)) (.branch 100 (.leaf 260614173) (.leaf 254248109))) (.branch 103 (.branch 102 (.leaf 248045110) (.leaf 242000618)) (.branch 104 (.leaf 236110217) (.leaf 230369636))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 224774738) (.leaf 219321516)) (.branch 108 (.leaf 214006089) (.leaf 208824699))) (.branch 111 (.branch 110 (.leaf 203773700) (.leaf 198849563)) (.branch 112 (.leaf 194048864) (.leaf 189368285)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 184804608) (.leaf 180354710)) (.branch 116 (.leaf 176015565) (.leaf 171784235))) (.branch 119 (.branch 118 (.leaf 167657869) (.leaf 163633699)) (.branch 120 (.leaf 159709042) (.leaf 155881289)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 72).prefactor = (1121443994103543/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 72).cutoff/(generalMeanRows 72).c)).2 =
    (91410903480377/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 72).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 72).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 72).q*(generalMeanRows 72).cutoff/2-2 = (248/111:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable041.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 72).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 72

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 72).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 72).criticalRate j.val*(generalMeanRows 72).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 72).c*(generalMeanRows 72).criticalPoint j.val)).2-
      (generalMeanRows 72).J/2-(generalMeanRows 72).error (generalMeanGrid j.val)+
      (generalMeanRows 72).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 72).c)).2-
      (generalMeanRows 72).J/2-(generalMeanRows 72).error 4 := by
  have he : (generalMeanRows 72).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 72) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 72)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0072

/-! Kernel-checked entropy margins for general spectral rectangle 73. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0073
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4937614341) (.branch 2 (.leaf 4739878453) (.leaf 4551941616))) (.branch 5 (.branch 4 (.leaf 4373214343) (.leaf 4203149679)) (.branch 6 (.leaf 4041239483) (.leaf 3887011117)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3740024472) (.leaf 3599869299)) (.branch 10 (.leaf 3466162806) (.leaf 3338547480))) (.branch 13 (.branch 12 (.leaf 3216689129) (.leaf 3100275088)) (.branch 14 (.leaf 2989012605) (.leaf 2882627359))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2780862113) (.branch 17 (.leaf 2683475482) (.leaf 2590240804))) (.branch 20 (.branch 19 (.leaf 2500945105) (.leaf 2415388148)) (.branch 21 (.leaf 2333381560) (.leaf 2254748028)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2179320553) (.leaf 2106941771)) (.branch 25 (.leaf 2037463315) (.leaf 1970745230))) (.branch 28 (.branch 27 (.leaf 1906655434) (.leaf 1845069212)) (.branch 29 (.leaf 1785868752) (.leaf 1728942709)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1674185808) (.branch 32 (.leaf 1621498462) (.leaf 1570786431))) (.branch 35 (.branch 34 (.leaf 1521960494) (.leaf 1474936147)) (.branch 36 (.leaf 1429633319) (.leaf 1385976114)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1343892558) (.leaf 1303314377)) (.branch 40 (.leaf 1264176774) (.leaf 1226418236))) (.branch 43 (.branch 42 (.leaf 1189980340) (.leaf 1154807578)) (.branch 44 (.leaf 1120847195) (.leaf 1088049031))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1056365378) (.branch 47 (.leaf 1025750841) (.leaf 996162214))) (.branch 50 (.branch 49 (.leaf 967558358) (.leaf 939900088)) (.branch 51 (.leaf 913150069) (.leaf 887272712)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 862234086) (.leaf 838001827)) (.branch 55 (.leaf 814545055) (.leaf 791834297))) (.branch 58 (.branch 57 (.leaf 769841411) (.leaf 748539520)) (.branch 59 (.leaf 727902945) (.leaf 707907144))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 688528653) (.branch 62 (.leaf 669745032) (.leaf 651534815))) (.branch 65 (.branch 64 (.leaf 633877456) (.leaf 616753290)) (.branch 66 (.leaf 600143484) (.leaf 584029997)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 568395545) (.leaf 553223558)) (.branch 70 (.leaf 538498151) (.leaf 524204088))) (.branch 73 (.branch 72 (.leaf 510326752) (.leaf 496852114)) (.branch 74 (.leaf 483766708) (.leaf 471057602))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 458712376) (.branch 77 (.leaf 446719095) (.leaf 435066289))) (.branch 80 (.branch 79 (.leaf 423742929) (.leaf 412738410)) (.branch 81 (.leaf 402042533) (.leaf 391645481)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 381537806) (.leaf 371710414)) (.branch 85 (.leaf 362154545) (.leaf 352861764))) (.branch 88 (.branch 87 (.leaf 343823939) (.leaf 335033238)) (.branch 89 (.leaf 326482107) (.leaf 318163262)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 310069681) (.branch 92 (.leaf 302194586) (.leaf 294531437))) (.branch 95 (.branch 94 (.leaf 287073922) (.leaf 279815948)) (.branch 96 (.leaf 272751628) (.leaf 265875280)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 259181410) (.leaf 252664713)) (.branch 100 (.leaf 246320059) (.leaf 240142488))) (.branch 103 (.branch 102 (.leaf 234127205) (.leaf 228269572)) (.branch 104 (.leaf 222565104) (.leaf 217009457))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 211598432) (.leaf 206327961)) (.branch 108 (.leaf 201194107) (.leaf 196193057))) (.branch 111 (.branch 110 (.leaf 191321119) (.leaf 186574716)) (.branch 112 (.leaf 181950383) (.leaf 177444760)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 173054594) (.leaf 168776729)) (.branch 116 (.leaf 164608105) (.leaf 160545757))) (.branch 119 (.branch 118 (.leaf 156586807) (.leaf 152728465)) (.branch 120 (.leaf 148968025) (.leaf 145302858)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 73).prefactor = (721610776952541/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 73).cutoff/(generalMeanRows 73).c)).2 =
    (71433797386107/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 73).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 73).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 73).q*(generalMeanRows 73).cutoff/2-2 = (248/111:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable041.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 73).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 73

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 73).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 73).criticalRate j.val*(generalMeanRows 73).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 73).c*(generalMeanRows 73).criticalPoint j.val)).2-
      (generalMeanRows 73).J/2-(generalMeanRows 73).error (generalMeanGrid j.val)+
      (generalMeanRows 73).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 73).c)).2-
      (generalMeanRows 73).J/2-(generalMeanRows 73).error 4 := by
  have he : (generalMeanRows 73).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 73) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 73)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0073

/-! Kernel-checked entropy margins for general spectral rectangle 74. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0074
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5270031080) (.branch 2 (.leaf 5064659152) (.leaf 4869376247))) (.branch 5 (.branch 4 (.leaf 4683575430) (.leaf 4506693614)) (.branch 6 (.leaf 4338207725) (.leaf 4177631284)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4024511347) (.leaf 3878425745)) (.branch 10 (.leaf 3738980609) (.leaf 3605808124))) (.branch 13 (.branch 12 (.leaf 3478564505) (.leaf 3356928155)) (.branch 14 (.leaf 3240597992) (.leaf 3129291923))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3022745458) (.branch 17 (.leaf 2920710435) (.leaf 2822953857))) (.branch 20 (.branch 19 (.leaf 2729256824) (.leaf 2639413554)) (.branch 21 (.leaf 2553230482) (.leaf 2470525426)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2391126826) (.leaf 2314873037)) (.branch 25 (.leaf 2241611673) (.leaf 2171199008))) (.branch 28 (.branch 27 (.leaf 2103499411) (.leaf 2038384833)) (.branch 29 (.leaf 1975734325) (.leaf 1915433589)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1857374565) (.branch 32 (.leaf 1801455047) (.leaf 1747578319))) (.branch 35 (.branch 34 (.leaf 1695652828) (.leaf 1645591864)) (.branch 36 (.leaf 1597313275) (.leaf 1550739194)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1505795786) (.leaf 1462413011)) (.branch 40 (.leaf 1420524403) (.leaf 1380066861))) (.branch 43 (.branch 42 (.leaf 1340980459) (.leaf 1303208263)) (.branch 44 (.leaf 1266696160) (.leaf 1231392699))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1197248944) (.branch 47 (.leaf 1164218332) (.leaf 1132256540))) (.branch 50 (.branch 49 (.leaf 1101321366) (.leaf 1071372608)) (.branch 51 (.leaf 1042371962) (.leaf 1014282910)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 987070632) (.leaf 960701913)) (.branch 55 (.leaf 935145057) (.leaf 910369805))) (.branch 58 (.branch 57 (.leaf 886347265) (.leaf 863049835)) (.branch 59 (.leaf 840451140) (.leaf 818525967))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 797250205) (.branch 62 (.leaf 776600792) (.leaf 756555658))) (.branch 65 (.branch 64 (.leaf 737093675) (.leaf 718194615)) (.branch 66 (.leaf 699839101) (.leaf 682008563)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 664685205) (.leaf 647851961)) (.branch 70 (.leaf 631492463) (.leaf 615591006))) (.branch 73 (.branch 72 (.leaf 600132516) (.leaf 585102522)) (.branch 74 (.leaf 570487124) (.leaf 556272969))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 542447227) (.branch 77 (.leaf 528997560) (.leaf 515912108))) (.branch 80 (.branch 79 (.leaf 503179459) (.leaf 490788634)) (.branch 81 (.leaf 478729067) (.leaf 466990583)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 455563385) (.leaf 444438034)) (.branch 85 (.leaf 433605434) (.leaf 423056818))) (.branch 88 (.branch 87 (.leaf 412783732) (.leaf 402778025)) (.branch 89 (.leaf 393031831) (.leaf 383537561)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 374287890) (.branch 92 (.leaf 365275744) (.leaf 356494293))) (.branch 95 (.branch 94 (.leaf 347936939) (.leaf 339597306)) (.branch 96 (.leaf 331469233) (.leaf 323546762)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 315824135) (.leaf 308295779)) (.branch 100 (.leaf 300956305) (.leaf 293800499))) (.branch 103 (.branch 102 (.leaf 286823313) (.leaf 280019859)) (.branch 104 (.leaf 273385408) (.leaf 266915376))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 260605323) (.leaf 254450950)) (.branch 108 (.leaf 248448087) (.leaf 242592695))) (.branch 111 (.branch 110 (.leaf 236880856) (.leaf 231308772)) (.branch 112 (.leaf 225872758) (.leaf 220569241)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 215394754) (.leaf 210345933)) (.branch 116 (.leaf 205419511) (.leaf 200612318))) (.branch 119 (.branch 118 (.leaf 195921278) (.leaf 191343400)) (.branch 120 (.leaf 186875782) (.leaf 182515605)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 74).prefactor = (5943447097443231/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 74).cutoff/(generalMeanRows 74).c)).2 =
    (187095337249983/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 74).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 74).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 74).q*(generalMeanRows 74).cutoff/2-2 = (248/111:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable041.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 74).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 74

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 74).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 74).criticalRate j.val*(generalMeanRows 74).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 74).c*(generalMeanRows 74).criticalPoint j.val)).2-
      (generalMeanRows 74).J/2-(generalMeanRows 74).error (generalMeanGrid j.val)+
      (generalMeanRows 74).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 74).c)).2-
      (generalMeanRows 74).J/2-(generalMeanRows 74).error 4 := by
  have he : (generalMeanRows 74).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 74) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 74)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0074

/-! Kernel-checked entropy margins for general spectral rectangle 75. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0075
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5524846679) (.branch 2 (.leaf 5340006648) (.leaf 5164008196))) (.branch 5 (.branch 4 (.leaf 4996306173) (.leaf 4836395663)) (.branch 6 (.leaf 4683808452) (.leaf 4538109878)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4398895996) (.leaf 4265791039)) (.branch 10 (.leaf 4138445124) (.leaf 4016532175))) (.branch 13 (.branch 12 (.leaf 3899748051) (.leaf 3787808840)) (.branch 14 (.leaf 3680449311) (.leaf 3577421500))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3478493428) (.branch 17 (.leaf 3383447919) (.leaf 3292081526))) (.branch 20 (.branch 19 (.leaf 3204203540) (.leaf 3119635088)) (.branch 21 (.leaf 3038208296) (.leaf 2959765526)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2884158664) (.leaf 2811248475)) (.branch 25 (.leaf 2740903999) (.leaf 2673001992))) (.branch 28 (.branch 27 (.leaf 2607426417) (.leaf 2544067966)) (.branch 29 (.leaf 2482823619) (.leaf 2423596234)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2366294169) (.branch 32 (.leaf 2310830932) (.leaf 2257124847))) (.branch 35 (.branch 34 (.leaf 2205098756) (.leaf 2154679732)) (.branch 36 (.leaf 2105798818) (.leaf 2058390777)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2012393870) (.leaf 1967749634)) (.branch 40 (.leaf 1924402688) (.leaf 1882300548))) (.branch 43 (.branch 42 (.leaf 1841393448) (.leaf 1801634184)) (.branch 44 (.leaf 1762977956) (.leaf 1725382232))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1688806610) (.branch 47 (.leaf 1653212699) (.leaf 1618563998))) (.branch 50 (.branch 49 (.leaf 1584825790) (.leaf 1551965038)) (.branch 51 (.leaf 1519950291) (.leaf 1488751594)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1458340402) (.leaf 1428689505)) (.branch 55 (.leaf 1399772950) (.leaf 1371565972))) (.branch 58 (.branch 57 (.leaf 1344044931) (.leaf 1317187249)) (.branch 59 (.leaf 1290971353) (.leaf 1265376619))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1240383326) (.branch 62 (.leaf 1215972599) (.leaf 1192126376))) (.branch 65 (.branch 64 (.leaf 1168827353) (.leaf 1146058955)) (.branch 66 (.leaf 1123805291) (.leaf 1102051122)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1080781827) (.leaf 1059983370)) (.branch 70 (.leaf 1039642275) (.leaf 1019745591))) (.branch 73 (.branch 72 (.leaf 1000280873) (.leaf 981236151)) (.branch 74 (.leaf 962599912) (.leaf 944361072))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 926508961) (.branch 77 (.leaf 909033300) (.leaf 891924181))) (.branch 80 (.branch 79 (.leaf 875172054) (.leaf 858767706)) (.branch 81 (.leaf 842702248) (.leaf 826967098)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 811553969) (.leaf 796454854)) (.branch 85 (.leaf 781662015) (.leaf 767167969))) (.branch 88 (.branch 87 (.leaf 752965479) (.leaf 739047542)) (.branch 89 (.leaf 725407379) (.leaf 712038426)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 698934322) (.branch 92 (.leaf 686088906) (.leaf 673496204))) (.branch 95 (.branch 94 (.leaf 661150421) (.leaf 649045940)) (.branch 96 (.leaf 637177305) (.leaf 625539224)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 614126556) (.leaf 602934307)) (.branch 100 (.leaf 591957627) (.leaf 581191800))) (.branch 103 (.branch 102 (.leaf 570632241) (.leaf 560274494)) (.branch 104 (.leaf 550114220) (.leaf 540147201))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 530369328) (.leaf 520776604)) (.branch 108 (.leaf 511365134) (.leaf 502131125))) (.branch 111 (.branch 110 (.leaf 493070883) (.leaf 484180806)) (.branch 112 (.leaf 475457383) (.leaf 466897192)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 458496897) (.leaf 450253240)) (.branch 116 (.leaf 442163046) (.leaf 434223217))) (.branch 119 (.branch 118 (.leaf 426430726) (.leaf 418782623)) (.branch 120 (.leaf 411276022) (.leaf 403908111)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 75).prefactor = (1352839605727059/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 75).cutoff/(generalMeanRows 75).c)).2 =
    (478121597348197/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 75).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 75).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 75).q*(generalMeanRows 75).c/2-2 = (7/10:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable043.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 75).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 75

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 75).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 75).criticalRate j.val*(generalMeanRows 75).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 75).c*(generalMeanRows 75).criticalPoint j.val)).2-
      (generalMeanRows 75).J/2-(generalMeanRows 75).error (generalMeanGrid j.val)+
      (generalMeanRows 75).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 75).c)).2-
      (generalMeanRows 75).J/2-(generalMeanRows 75).error 4 := by
  have he : (generalMeanRows 75).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 75) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 75)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0075

/-! Kernel-checked entropy margins for general spectral rectangle 76. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0076
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8277378047) (.branch 2 (.leaf 8027126245) (.leaf 7787859584))) (.branch 5 (.branch 4 (.leaf 7558965701) (.leaf 7339874863)) (.branch 6 (.leaf 7130056176) (.leaf 6929014223)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6736286076) (.leaf 6551438614)) (.branch 10 (.leaf 6374066132) (.leaf 6203788183))) (.branch 13 (.branch 12 (.leaf 6040247635) (.leaf 5883108916)) (.branch 14 (.leaf 5732056423) (.leaf 5586793078))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5447039008) (.branch 17 (.leaf 5312530347) (.leaf 5183018143))) (.branch 20 (.branch 19 (.leaf 5058267343) (.leaf 4938055879)) (.branch 21 (.leaf 4822173819) (.leaf 4710422579)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4602614213) (.leaf 4498570740)) (.branch 25 (.leaf 4398123532) (.leaf 4301112743))) (.branch 28 (.branch 27 (.leaf 4207386780) (.leaf 4116801814)) (.branch 29 (.leaf 4029221320) (.leaf 3944515655)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3862561662) (.branch 32 (.leaf 3783242297) (.leaf 3706446289))) (.branch 35 (.branch 34 (.leaf 3632067815) (.leaf 3560006198)) (.branch 36 (.leaf 3490165626) (.leaf 3422454886)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3356787118) (.leaf 3293079581)) (.branch 40 (.leaf 3231253433) (.leaf 3171233530))) (.branch 43 (.branch 42 (.leaf 3112948225) (.leaf 3056329196)) (.branch 44 (.leaf 3001311265) (.leaf 2947832245))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2895832781) (.branch 47 (.leaf 2845256213) (.leaf 2796048436))) (.branch 50 (.branch 49 (.leaf 2748157772) (.leaf 2701534854)) (.branch 51 (.leaf 2656132508) (.leaf 2611905645)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2568811160) (.leaf 2526807839)) (.branch 55 (.leaf 2485856259) (.leaf 2445918712))) (.branch 58 (.branch 57 (.leaf 2406959114) (.leaf 2368942933)) (.branch 59 (.leaf 2331837112) (.leaf 2295610004))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2260231299) (.branch 62 (.leaf 2225671967) (.leaf 2191904194))) (.branch 65 (.branch 64 (.leaf 2158901330) (.leaf 2126637831)) (.branch 66 (.leaf 2095089210) (.leaf 2064231988)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 2034043649) (.leaf 2004502595)) (.branch 70 (.leaf 1975588102) (.leaf 1947280286))) (.branch 73 (.branch 72 (.leaf 1919560061) (.leaf 1892409103)) (.branch 74 (.leaf 1865809820) (.leaf 1839745313))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1814199352) (.branch 77 (.leaf 1789156341) (.leaf 1764601293))) (.branch 80 (.branch 79 (.leaf 1740519800) (.leaf 1716898015)) (.branch 81 (.leaf 1693722617) (.leaf 1670980797)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1648660231) (.leaf 1626749060)) (.branch 85 (.leaf 1605235872) (.leaf 1584109679))) (.branch 88 (.branch 87 (.leaf 1563359902) (.leaf 1542976353)) (.branch 89 (.leaf 1522949218) (.leaf 1503269039)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1483926702) (.branch 92 (.leaf 1464913424) (.leaf 1446220732))) (.branch 95 (.branch 94 (.leaf 1427840459) (.leaf 1409764723)) (.branch 96 (.leaf 1391985923) (.leaf 1374496720)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1357290032) (.leaf 1340359019)) (.branch 100 (.leaf 1323697077) (.leaf 1307297825))) (.branch 103 (.branch 102 (.leaf 1291155098) (.leaf 1275262938)) (.branch 104 (.leaf 1259615586) (.leaf 1244207471))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1229033206) (.leaf 1214087580)) (.branch 108 (.leaf 1199365550) (.leaf 1184862235))) (.branch 111 (.branch 110 (.leaf 1170572908) (.leaf 1156492992)) (.branch 112 (.leaf 1142618056) (.leaf 1128943802)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1115466068) (.leaf 1102180819)) (.branch 116 (.leaf 1089084141) (.leaf 1076172238))) (.branch 119 (.branch 118 (.leaf 1063441429) (.leaf 1050888140)) (.branch 120 (.leaf 1038508902) (.leaf 1026300349)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 76).prefactor = (2852050798999563/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 76).cutoff/(generalMeanRows 76).c)).2 =
    (21164123664967/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 76).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 76).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 76).q*(generalMeanRows 76).c/2-2 = (43/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable022.value]
    have hcontinuation : (generalMeanRows 76).q*(generalMeanRows 76).cutoff/2-2 = (65/38:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable044.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 76).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 76

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 76).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 76).criticalRate j.val*(generalMeanRows 76).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 76).c*(generalMeanRows 76).criticalPoint j.val)).2-
      (generalMeanRows 76).J/2-(generalMeanRows 76).error (generalMeanGrid j.val)+
      (generalMeanRows 76).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 76).c)).2-
      (generalMeanRows 76).J/2-(generalMeanRows 76).error 4 := by
  have he : (generalMeanRows 76).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 76) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 76)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0076

/-! Kernel-checked entropy margins for general spectral rectangle 77. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0077
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7920479184) (.branch 2 (.leaf 7658060071) (.leaf 7407208073))) (.branch 5 (.branch 4 (.leaf 7167282268) (.leaf 6937686342)) (.branch 6 (.leaf 6717864608) (.leaf 6507298492)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6305503390) (.leaf 6112025868)) (.branch 10 (.leaf 5926441150) (.leaf 5748350858))) (.branch 13 (.branch 12 (.leaf 5577380981) (.leaf 5413180035)) (.branch 14 (.leaf 5255417394) (.leaf 5103781783))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4957979897) (.branch 17 (.leaf 4817735147) (.leaf 4682786511))) (.branch 20 (.branch 19 (.leaf 4552887483) (.leaf 4427805110)) (.branch 21 (.leaf 4307319104) (.leaf 4191221026)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4079313536) (.leaf 3971409693)) (.branch 25 (.leaf 3867332318) (.leaf 3766913396))) (.branch 28 (.branch 27 (.leaf 3669993525) (.leaf 3576421401)) (.branch 29 (.leaf 3486053347) (.leaf 3398752864)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3314390221) (.branch 32 (.leaf 3232842071) (.leaf 3153991088))) (.branch 35 (.branch 34 (.leaf 3077725634) (.leaf 3003939443)) (.branch 36 (.leaf 2932531327) (.leaf 2863404903)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2796468329) (.leaf 2731634068)) (.branch 40 (.leaf 2668818657) (.leaf 2607942491))) (.branch 43 (.branch 42 (.leaf 2548929627) (.leaf 2491707590)) (.branch 44 (.leaf 2436207198) (.leaf 2382362393))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2330110080) (.branch 47 (.leaf 2279389984) (.leaf 2230144503))) (.branch 50 (.branch 49 (.leaf 2182318579) (.leaf 2135859571)) (.branch 51 (.leaf 2090717134) (.leaf 2046843113)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2004191429) (.leaf 1962717987)) (.branch 55 (.leaf 1922380574) (.leaf 1883138772))) (.branch 58 (.branch 57 (.leaf 1844953872) (.leaf 1807788794)) (.branch 59 (.leaf 1771608012) (.leaf 1736377476))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1702064550) (.branch 62 (.leaf 1668637939) (.leaf 1636067635))) (.branch 65 (.branch 64 (.leaf 1604324853) (.leaf 1573381974)) (.branch 66 (.leaf 1543212497) (.leaf 1513790984)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1485093013) (.leaf 1457095134)) (.branch 70 (.leaf 1429774824) (.leaf 1403110445))) (.branch 73 (.branch 72 (.leaf 1377081208) (.leaf 1351667130)) (.branch 74 (.leaf 1326849004) (.leaf 1302608362))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1278927445) (.branch 77 (.leaf 1255789168) (.leaf 1233177096))) (.branch 80 (.branch 79 (.leaf 1211075412) (.leaf 1189468891)) (.branch 81 (.leaf 1168342878) (.leaf 1147683260)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1127476444) (.leaf 1107709335)) (.branch 85 (.leaf 1088369316) (.leaf 1069444226))) (.branch 88 (.branch 87 (.leaf 1050922345) (.leaf 1032792369)) (.branch 89 (.leaf 1015043399) (.leaf 997664921)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 980646791) (.branch 92 (.leaf 963979220) (.leaf 947652758))) (.branch 95 (.branch 94 (.leaf 931658284) (.leaf 915986987)) (.branch 96 (.leaf 900630360) (.leaf 885580181)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 870828509) (.leaf 856367665)) (.branch 100 (.leaf 842190228) (.leaf 828289021))) (.branch 103 (.branch 102 (.leaf 814657103) (.leaf 801287759)) (.branch 104 (.leaf 788174493) (.leaf 775311017))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 762691243) (.leaf 750309279)) (.branch 108 (.leaf 738159417) (.leaf 726236127))) (.branch 111 (.branch 110 (.leaf 714534054) (.leaf 703048005)) (.branch 112 (.leaf 691772948) (.leaf 680704006)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 669836445) (.leaf 659165679)) (.branch 116 (.leaf 648687253) (.leaf 638396848))) (.branch 119 (.branch 118 (.leaf 628290270) (.leaf 618363448)) (.branch 120 (.leaf 608612429) (.leaf 599033374)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 77).prefactor = (6013474155145631/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 77).cutoff/(generalMeanRows 77).c)).2 =
    (2838940091549/7812500000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 77).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 77).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 77).q*(generalMeanRows 77).c/2-2 = (29/50:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable045.value]
    have hcontinuation : (generalMeanRows 77).q*(generalMeanRows 77).cutoff/2-2 = (65/38:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable044.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 77).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 77

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 77).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 77).criticalRate j.val*(generalMeanRows 77).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 77).c*(generalMeanRows 77).criticalPoint j.val)).2-
      (generalMeanRows 77).J/2-(generalMeanRows 77).error (generalMeanGrid j.val)+
      (generalMeanRows 77).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 77).c)).2-
      (generalMeanRows 77).J/2-(generalMeanRows 77).error 4 := by
  have he : (generalMeanRows 77).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 77) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 77)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0077

/-! Kernel-checked entropy margins for general spectral rectangle 78. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0078
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6879439807) (.branch 2 (.leaf 6670793298) (.leaf 6471544759))) (.branch 5 (.branch 4 (.leaf 6281154343) (.leaf 6099120155)) (.branch 6 (.leaf 5924974926) (.leaf 5758283053)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5598637954) (.leaf 5445659703)) (.branch 10 (.leaf 5298992896) (.leaf 5158304736))) (.branch 13 (.branch 12 (.leaf 5023283295) (.leaf 4893635952)) (.branch 14 (.leaf 4769087957) (.leaf 4649381142))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4534272734) (.branch 17 (.leaf 4423534274) (.leaf 4316950629))) (.branch 20 (.branch 19 (.leaf 4214319084) (.leaf 4115448506)) (.branch 21 (.leaf 4020158581) (.leaf 3928279103)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3839649325) (.leaf 3754117354)) (.branch 25 (.leaf 3671539591) (.leaf 3591780222))) (.branch 28 (.branch 27 (.leaf 3514710728) (.leaf 3440209448)) (.branch 29 (.leaf 3368161160) (.leaf 3298456701)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3230992601) (.branch 32 (.leaf 3165670754) (.leaf 3102398106))) (.branch 35 (.branch 34 (.leaf 3041086360) (.leaf 2981651705)) (.branch 36 (.leaf 2924014562) (.leaf 2868099345)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2813834237) (.leaf 2761150979)) (.branch 40 (.leaf 2709984679) (.leaf 2660273621))) (.branch 43 (.branch 42 (.leaf 2611959093) (.leaf 2564985230)) (.branch 44 (.leaf 2519298854) (.leaf 2474849332))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2431588445) (.branch 47 (.leaf 2389470252) (.leaf 2348450980))) (.branch 50 (.branch 49 (.leaf 2308488902) (.leaf 2269544234)) (.branch 51 (.leaf 2231579036) (.leaf 2194557115)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2158443935) (.leaf 2123206532)) (.branch 55 (.leaf 2088813437) (.leaf 2055234599))) (.branch 58 (.branch 57 (.leaf 2022441311) (.leaf 1990406145)) (.branch 59 (.leaf 1959102891) (.leaf 1928506489))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1898592980) (.branch 62 (.leaf 1869339448) (.leaf 1840723966))) (.branch 65 (.branch 64 (.leaf 1812725553) (.leaf 1785324127)) (.branch 66 (.leaf 1758500458) (.leaf 1732236130)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1706513499) (.leaf 1681315660)) (.branch 70 (.leaf 1656626409) (.leaf 1632430209))) (.branch 73 (.branch 72 (.leaf 1608712162) (.leaf 1585457975)) (.branch 74 (.leaf 1562653932) (.leaf 1540286870))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1518344151) (.branch 77 (.leaf 1496813636) (.leaf 1475683667))) (.branch 80 (.branch 79 (.leaf 1454943040) (.leaf 1434580984)) (.branch 81 (.leaf 1414587147) (.leaf 1394951569)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1375664672) (.leaf 1356717235)) (.branch 85 (.leaf 1338100385) (.leaf 1319805576))) (.branch 88 (.branch 87 (.leaf 1301824579) (.leaf 1284149464)) (.branch 89 (.leaf 1266772588) (.leaf 1249686585)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1232884348) (.branch 92 (.leaf 1216359024) (.leaf 1200104001))) (.branch 95 (.branch 94 (.leaf 1184112893) (.leaf 1168379538)) (.branch 96 (.leaf 1152897982) (.leaf 1137662473)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1122667454) (.leaf 1107907549)) (.branch 100 (.leaf 1093377563) (.leaf 1079072467))) (.branch 103 (.branch 102 (.leaf 1064987397) (.leaf 1051117644)) (.branch 104 (.leaf 1037458649) (.leaf 1024005995))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1010755404) (.leaf 997702728)) (.branch 108 (.leaf 984843947) (.leaf 972175162))) (.branch 111 (.branch 110 (.leaf 959692590) (.leaf 947392560)) (.branch 112 (.leaf 935271510) (.leaf 923325981)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 911552610) (.leaf 899948135)) (.branch 116 (.leaf 888509381) (.leaf 877233264))) (.branch 119 (.branch 118 (.leaf 866116783) (.leaf 855157021)) (.branch 120 (.leaf 844351138) (.leaf 833696371)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 78).prefactor = (205442269850663/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 78).cutoff/(generalMeanRows 78).c)).2 =
    (225726675133017/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 78).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 78).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 78).q*(generalMeanRows 78).c/2-2 = (19/40:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable046.value]
    have hcontinuation : (generalMeanRows 78).q*(generalMeanRows 78).cutoff/2-2 = (251/133:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable047.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 78).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 78

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 78).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 78).criticalRate j.val*(generalMeanRows 78).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 78).c*(generalMeanRows 78).criticalPoint j.val)).2-
      (generalMeanRows 78).J/2-(generalMeanRows 78).error (generalMeanGrid j.val)+
      (generalMeanRows 78).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 78).c)).2-
      (generalMeanRows 78).J/2-(generalMeanRows 78).error 4 := by
  have he : (generalMeanRows 78).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 78) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 78)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0078

/-! Kernel-checked entropy margins for general spectral rectangle 79. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0079
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7024735179) (.branch 2 (.leaf 6807471053) (.leaf 6599996176))) (.branch 5 (.branch 4 (.leaf 6401749150) (.leaf 6212208036)) (.branch 6 (.leaf 6030886893) (.leaf 5857332704)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5691122621) (.leaf 5531861506)) (.branch 10 (.leaf 5379179713) (.leaf 5232731095))) (.branch 13 (.branch 12 (.leaf 5092191201) (.leaf 4957255643)) (.branch 14 (.leaf 4827638615) (.leaf 4703071540))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4583301846) (.branch 17 (.leaf 4468091836) (.leaf 4357217664))) (.branch 20 (.branch 19 (.leaf 4250468390) (.leaf 4147645112)) (.branch 21 (.leaf 4048560169) (.leaf 3953036410)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3860906509) (.leaf 3772012345)) (.branch 25 (.leaf 3686204419) (.leaf 3603341315))) (.branch 28 (.branch 27 (.leaf 3523289207) (.leaf 3445921391)) (.branch 29 (.leaf 3371117859) (.leaf 3298764895)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3228754706) (.branch 32 (.leaf 3160985071) (.leaf 3095359018))) (.branch 35 (.branch 34 (.leaf 3031784523) (.leaf 2970174223)) (.branch 36 (.leaf 2910445157) (.leaf 2852518510)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2796319389) (.leaf 2741776600)) (.branch 40 (.leaf 2688822445) (.leaf 2637392533))) (.branch 43 (.branch 42 (.leaf 2587425596) (.leaf 2538863323)) (.branch 44 (.leaf 2491650200) (.leaf 2445733362))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2401062447) (.branch 47 (.leaf 2357589471) (.leaf 2315268700))) (.branch 50 (.branch 49 (.leaf 2274056530) (.leaf 2233911379)) (.branch 51 (.leaf 2194793582) (.leaf 2156665292)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2119490389) (.leaf 2083234387)) (.branch 55 (.leaf 2047864357) (.leaf 2013348843))) (.branch 58 (.branch 57 (.leaf 1979657793) (.leaf 1946762486)) (.branch 59 (.leaf 1914635465) (.leaf 1883250476))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1852582409) (.branch 62 (.leaf 1822607241) (.leaf 1793301981))) (.branch 65 (.branch 64 (.leaf 1764644624) (.leaf 1736614097)) (.branch 66 (.leaf 1709190222) (.leaf 1682353664)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1656085899) (.leaf 1630369168)) (.branch 70 (.leaf 1605186447) (.leaf 1580521407))) (.branch 73 (.branch 72 (.leaf 1556358385) (.leaf 1532682348)) (.branch 74 (.leaf 1509478871) (.leaf 1486734102))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1464434737) (.branch 77 (.leaf 1442567996) (.leaf 1421121599))) (.branch 80 (.branch 79 (.leaf 1400083742) (.leaf 1379443074)) (.branch 81 (.leaf 1359188681) (.leaf 1339310061)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1319797107) (.leaf 1300640093)) (.branch 85 (.leaf 1281829649) (.leaf 1263356755))) (.branch 88 (.branch 87 (.leaf 1245212718) (.leaf 1227389159)) (.branch 89 (.leaf 1209878002) (.leaf 1192671458)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1175762014) (.branch 92 (.leaf 1159142421) (.leaf 1142805680))) (.branch 95 (.branch 94 (.leaf 1126745036) (.leaf 1110953962)) (.branch 96 (.leaf 1095426155) (.leaf 1080155522)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1065136173) (.leaf 1050362413)) (.branch 100 (.leaf 1035828733) (.leaf 1021529801))) (.branch 103 (.branch 102 (.leaf 1007460459) (.leaf 993615711)) (.branch 104 (.leaf 979990718) (.leaf 966580793))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 953381395) (.leaf 940388120)) (.branch 108 (.leaf 927596698) (.leaf 915002988))) (.branch 111 (.branch 110 (.leaf 902602970) (.leaf 890392746)) (.branch 112 (.leaf 878368529) (.leaf 866526641)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 854863510) (.leaf 843375666)) (.branch 116 (.leaf 832059734) (.leaf 820912434))) (.branch 119 (.branch 118 (.leaf 809930576) (.leaf 799111056)) (.branch 120 (.leaf 788450853) (.leaf 777947028)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 79).prefactor = (534903085925393/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 79).cutoff/(generalMeanRows 79).c)).2 =
    (220201757039727/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 79).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 79).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 79).q*(generalMeanRows 79).c/2-2 = (201/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable029.value]
    have hcontinuation : (generalMeanRows 79).q*(generalMeanRows 79).cutoff/2-2 = (251/133:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable047.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 79).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 79

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 79).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 79).criticalRate j.val*(generalMeanRows 79).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 79).c*(generalMeanRows 79).criticalPoint j.val)).2-
      (generalMeanRows 79).J/2-(generalMeanRows 79).error (generalMeanGrid j.val)+
      (generalMeanRows 79).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 79).c)).2-
      (generalMeanRows 79).J/2-(generalMeanRows 79).error 4 := by
  have he : (generalMeanRows 79).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 79) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 79)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0079

/-! Kernel-checked entropy margins for general spectral rectangle 80. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0080
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7174343175) (.branch 2 (.leaf 6948198413) (.leaf 6732250800))) (.branch 5 (.branch 4 (.leaf 6525916453) (.leaf 6328652518)) (.branch 6 (.leaf 6139953574) (.leaf 5959348425)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5786397249) (.leaf 5620689027)) (.branch 10 (.leaf 5461839244) (.leaf 5309487816))) (.branch 13 (.branch 12 (.leaf 5163297213) (.leaf 5022950759)) (.branch 14 (.leaf 4888151096) (.leaf 4758618777))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4634090990) (.branch 17 (.leaf 4514320385) (.leaf 4399074011))) (.branch 20 (.branch 19 (.leaf 4288132330) (.leaf 4181288318)) (.branch 21 (.leaf 4078346636) (.leaf 3979122867)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3883442808) (.leaf 3791141824)) (.branch 25 (.leaf 3702064241) (.leaf 3616062788))) (.branch 28 (.branch 27 (.leaf 3532998082) (.leaf 3452738145)) (.branch 29 (.leaf 3375157957) (.leaf 3300139041)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3227569074) (.branch 32 (.leaf 3157341530) (.leaf 3089355336))) (.branch 35 (.branch 34 (.leaf 3023514564) (.leaf 2959728134)) (.branch 36 (.leaf 2897909539) (.leaf 2837976586)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2779851158) (.leaf 2723458985)) (.branch 40 (.leaf 2668729435) (.leaf 2615595311))) (.branch 43 (.branch 42 (.leaf 2563992668) (.leaf 2513860633)) (.branch 44 (.leaf 2465141244) (.leaf 2417779295))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2371722185) (.branch 47 (.leaf 2326919785) (.leaf 2283324306))) (.branch 50 (.branch 49 (.leaf 2240890179) (.leaf 2199573938)) (.branch 51 (.leaf 2159334111) (.leaf 2120131120)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2081927183) (.leaf 2044686221)) (.branch 55 (.leaf 2008373774) (.leaf 1972956919))) (.branch 58 (.branch 57 (.leaf 1938404193) (.leaf 1904685520)) (.branch 59 (.leaf 1871772140) (.leaf 1839636549))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1808252432) (.branch 62 (.leaf 1777594607) (.leaf 1747638971))) (.branch 65 (.branch 64 (.leaf 1718362446) (.leaf 1689742927)) (.branch 66 (.leaf 1661759241) (.leaf 1634391096)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1607619046) (.leaf 1581424442)) (.branch 70 (.leaf 1555789401) (.leaf 1530696770))) (.branch 73 (.branch 72 (.leaf 1506130085) (.leaf 1482073548)) (.branch 74 (.leaf 1458511987) (.leaf 1435430833))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1412816092) (.branch 77 (.leaf 1390654314) (.leaf 1368932572))) (.branch 80 (.branch 79 (.leaf 1347638438) (.leaf 1326759959)) (.branch 81 (.leaf 1306285635) (.leaf 1286204400)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1266505603) (.leaf 1247178987)) (.branch 85 (.leaf 1228214674) (.leaf 1209603147))) (.branch 88 (.branch 87 (.leaf 1191335233) (.leaf 1173402093)) (.branch 89 (.leaf 1155795198) (.leaf 1138506326)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1121527542) (.branch 92 (.leaf 1104851186) (.leaf 1088469866))) (.branch 95 (.branch 94 (.leaf 1072376441) (.leaf 1056564012)) (.branch 96 (.leaf 1041025915) (.leaf 1025755706)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1010747155) (.leaf 995994238)) (.branch 100 (.leaf 981491124) (.leaf 967232172))) (.branch 103 (.branch 102 (.leaf 953211920) (.leaf 939425081)) (.branch 104 (.leaf 925866530) (.leaf 912531306))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 899414596) (.leaf 886511736)) (.branch 108 (.leaf 873818204) (.leaf 861329611))) (.branch 111 (.branch 110 (.leaf 849041700) (.leaf 836950336)) (.branch 112 (.leaf 825051508) (.leaf 813341319)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 801815981) (.leaf 790471816)) (.branch 116 (.leaf 779305248) (.leaf 768312798))) (.branch 119 (.branch 118 (.leaf 757491086) (.leaf 746836821)) (.branch 120 (.leaf 736346801) (.leaf 726017910)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 80).prefactor = (5570836255664259/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 80).cutoff/(generalMeanRows 80).c)).2 =
    (429474443547261/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 80).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 80).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 80).q*(generalMeanRows 80).c/2-2 = (53/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable031.value]
    have hcontinuation : (generalMeanRows 80).q*(generalMeanRows 80).cutoff/2-2 = (251/133:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable047.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 80).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 80

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 80).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 80).criticalRate j.val*(generalMeanRows 80).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 80).c*(generalMeanRows 80).criticalPoint j.val)).2-
      (generalMeanRows 80).J/2-(generalMeanRows 80).error (generalMeanGrid j.val)+
      (generalMeanRows 80).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 80).c)).2-
      (generalMeanRows 80).J/2-(generalMeanRows 80).error 4 := by
  have he : (generalMeanRows 80).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 80) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 80)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0080

/-! Kernel-checked entropy margins for general spectral rectangle 81. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0081
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6094604441) (.branch 2 (.leaf 5865543931) (.leaf 5647114907))) (.branch 5 (.branch 4 (.leaf 5438714141) (.leaf 5239780597)) (.branch 6 (.leaf 5049791729) (.leaf 4868260179)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4694730838) (.leaf 4528778205)) (.branch 10 (.leaf 4370004019) (.leaf 4218035124))) (.branch 13 (.branch 12 (.leaf 4072521545) (.leaf 3933134737)) (.branch 14 (.leaf 3799566007) (.leaf 3671525068))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3548738731) (.branch 17 (.leaf 3430949701) (.leaf 3317915480))) (.branch 20 (.branch 19 (.leaf 3209407362) (.leaf 3105209511)) (.branch 21 (.leaf 3005118105) (.leaf 2908940559)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2816494800) (.leaf 2727608599)) (.branch 25 (.leaf 2642118955) (.leaf 2559871522))) (.branch 28 (.branch 27 (.leaf 2480720083) (.leaf 2404526049)) (.branch 29 (.leaf 2331158011) (.leaf 2260491308)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2192407632) (.branch 32 (.leaf 2126794661) (.leaf 2063545710))) (.branch 35 (.branch 34 (.leaf 2002559413) (.leaf 1943739418)) (.branch 36 (.leaf 1886994109) (.leaf 1832236342)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1779383194) (.leaf 1728355737)) (.branch 40 (.leaf 1679078820) (.leaf 1631480862))) (.branch 43 (.branch 42 (.leaf 1585493662) (.leaf 1541052221)) (.branch 44 (.leaf 1498094573) (.leaf 1456561622))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1416396997) (.branch 47 (.leaf 1377546907) (.leaf 1339960011))) (.branch 50 (.branch 49 (.leaf 1303587291) (.leaf 1268381937)) (.branch 51 (.leaf 1234299229) (.leaf 1201296438)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1169332725) (.leaf 1138369046)) (.branch 55 (.leaf 1108368063) (.leaf 1079294062))) (.branch 58 (.branch 57 (.leaf 1051112872) (.leaf 1023791792)) (.branch 59 (.leaf 997299516) (.leaf 971606072))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 946682750) (.branch 62 (.leaf 922502051) (.leaf 899037623))) (.branch 65 (.branch 64 (.leaf 876264208) (.leaf 854157594)) (.branch 66 (.leaf 832694563) (.leaf 811852845)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 791611075) (.leaf 771948753)) (.branch 70 (.leaf 752846201) (.leaf 734284527))) (.branch 73 (.branch 72 (.leaf 716245590) (.leaf 698711967)) (.branch 74 (.leaf 681666917) (.leaf 665094355))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 648978820) (.branch 77 (.leaf 633305447) (.leaf 618059943))) (.branch 80 (.branch 79 (.leaf 603228562) (.leaf 588798076)) (.branch 81 (.leaf 574755760) (.leaf 561089365)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 547787100) (.leaf 534837609)) (.branch 85 (.leaf 522229958) (.leaf 509953612))) (.branch 88 (.branch 87 (.leaf 497998422) (.leaf 486354604)) (.branch 89 (.leaf 475012729) (.leaf 463963705)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 453198764) (.branch 92 (.leaf 442709449) (.leaf 432487600))) (.branch 95 (.branch 94 (.leaf 422525342) (.leaf 412815077)) (.branch 96 (.leaf 403349467) (.leaf 394121426)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 385124114) (.leaf 376350919)) (.branch 100 (.leaf 367795456) (.leaf 359451552))) (.branch 103 (.branch 102 (.leaf 351313243) (.leaf 343374759)) (.branch 104 (.leaf 335630525) (.leaf 328075146))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 320703405) (.leaf 313510251)) (.branch 108 (.leaf 306490800) (.leaf 299640323))) (.branch 111 (.branch 110 (.leaf 292954240) (.leaf 286428120)) (.branch 112 (.leaf 280057667) (.leaf 273838725)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 267767262) (.leaf 261839375)) (.branch 116 (.leaf 256051281) (.leaf 250399310))) (.branch 119 (.branch 118 (.leaf 244879906) (.leaf 239489621)) (.branch 120 (.leaf 234225111) (.leaf 229083130)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 81).prefactor = (2900919568797547/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 81).cutoff/(generalMeanRows 81).c)).2 =
    (158267016183333/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 81).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 81).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 81).q*(generalMeanRows 81).c/2-2 = (333/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable039.value]
    have hcontinuation : (generalMeanRows 81).q*(generalMeanRows 81).cutoff/2-2 = (251/133:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable047.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 81).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 81

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 81).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 81).criticalRate j.val*(generalMeanRows 81).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 81).c*(generalMeanRows 81).criticalPoint j.val)).2-
      (generalMeanRows 81).J/2-(generalMeanRows 81).error (generalMeanGrid j.val)+
      (generalMeanRows 81).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 81).c)).2-
      (generalMeanRows 81).J/2-(generalMeanRows 81).error 4 := by
  have he : (generalMeanRows 81).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 81) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 81)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0081

/-! Kernel-checked entropy margins for general spectral rectangle 82. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0082
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5857650200) (.branch 2 (.leaf 5679673506) (.leaf 5509907191))) (.branch 5 (.branch 4 (.leaf 5347860990) (.leaf 5193079898)) (.branch 6 (.leaf 5045141091) (.leaf 4903651183)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4768243773) (.leaf 4638577236)) (.branch 10 (.leaf 4514332736) (.leaf 4395212428))) (.branch 13 (.branch 12 (.leaf 4280937839) (.leaf 4171248388)) (.branch 14 (.leaf 4065900050) (.leaf 3964664134))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3867326168) (.branch 17 (.leaf 3773684880) (.leaf 3683551264))) (.branch 20 (.branch 19 (.leaf 3596747727) (.leaf 3513107297)) (.branch 21 (.leaf 3432472904) (.leaf 3354696710)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3279639494) (.leaf 3207170085)) (.branch 25 (.leaf 3137164837) (.leaf 3069507137))) (.branch 28 (.branch 27 (.leaf 3004086963) (.leaf 2940800457)) (.branch 29 (.leaf 2879549543) (.leaf 2820241563)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2762788943) (.branch 32 (.leaf 2707108878) (.leaf 2653123046))) (.branch 35 (.branch 34 (.leaf 2600757330) (.leaf 2549941572)) (.branch 36 (.leaf 2500609330) (.leaf 2452697663)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2406146921) (.leaf 2360900555)) (.branch 40 (.leaf 2316904934) (.leaf 2274109177))) (.branch 43 (.branch 42 (.leaf 2232464997) (.leaf 2191926548)) (.branch 44 (.leaf 2152450291) (.leaf 2113994860))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2076520942) (.branch 47 (.leaf 2039991159) (.leaf 2004369964))) (.branch 50 (.branch 49 (.leaf 1969623538) (.leaf 1935719693)) (.branch 51 (.leaf 1902627787) (.leaf 1870318633)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1838764426) (.leaf 1807938666)) (.branch 55 (.leaf 1777816087) (.leaf 1748372592))) (.branch 58 (.branch 57 (.leaf 1719585190) (.leaf 1691431938)) (.branch 59 (.leaf 1663891885) (.leaf 1636945022))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1610572228) (.branch 62 (.leaf 1584755229) (.leaf 1559476552))) (.branch 65 (.branch 64 (.leaf 1534719481) (.leaf 1510468024)) (.branch 66 (.leaf 1486706870) (.leaf 1463421360)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1440597447) (.leaf 1418221672)) (.branch 70 (.leaf 1396281133) (.leaf 1374763453))) (.branch 73 (.branch 72 (.leaf 1353656759) (.leaf 1332949654)) (.branch 74 (.leaf 1312631195) (.leaf 1292690872))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1273118582) (.branch 77 (.leaf 1253904617) (.leaf 1235039638))) (.branch 80 (.branch 79 (.leaf 1216514661) (.leaf 1198321039)) (.branch 81 (.leaf 1180450446) (.leaf 1162894864)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1145646564) (.leaf 1128698097)) (.branch 85 (.leaf 1112042281) (.leaf 1095672183))) (.branch 88 (.branch 87 (.leaf 1079581115) (.leaf 1063762619)) (.branch 89 (.leaf 1048210458) (.leaf 1032918602)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1017881227) (.branch 92 (.leaf 1003092697) (.leaf 988547562))) (.branch 95 (.branch 94 (.leaf 974240547) (.leaf 960166546)) (.branch 96 (.leaf 946320612) (.leaf 932697953)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 919293926) (.leaf 906104027)) (.branch 100 (.leaf 893123887) (.leaf 880349270))) (.branch 103 (.branch 102 (.leaf 867776061) (.leaf 855400267)) (.branch 104 (.leaf 843218007) (.leaf 831225513))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 819419119) (.leaf 807795264)) (.branch 108 (.leaf 796350482) (.leaf 785081401))) (.branch 111 (.branch 110 (.leaf 773984741) (.leaf 763057306)) (.branch 112 (.leaf 752295984) (.leaf 741697746)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 731259637) (.leaf 720978778)) (.branch 116 (.leaf 710852361) (.leaf 700877647))) (.branch 119 (.branch 118 (.leaf 691051967) (.leaf 681372712)) (.branch 120 (.leaf 671837337) (.leaf 662443357)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 82).prefactor = (4798156056469697/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 82).cutoff/(generalMeanRows 82).c)).2 =
    (242677450970859/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 82).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 82).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 82).q*(generalMeanRows 82).c/2-2 = (43/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable048.value]
    have hcontinuation : (generalMeanRows 82).q*(generalMeanRows 82).cutoff/2-2 = (121/57:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable049.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 82).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 82

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 82).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 82).criticalRate j.val*(generalMeanRows 82).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 82).c*(generalMeanRows 82).criticalPoint j.val)).2-
      (generalMeanRows 82).J/2-(generalMeanRows 82).error (generalMeanGrid j.val)+
      (generalMeanRows 82).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 82).c)).2-
      (generalMeanRows 82).J/2-(generalMeanRows 82).error 4 := by
  have he : (generalMeanRows 82).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 82) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 82)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0082

/-! Kernel-checked entropy margins for general spectral rectangle 83. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0083
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5925290389) (.branch 2 (.leaf 5741756137) (.leaf 5566697501))) (.branch 5 (.branch 4 (.leaf 5399609327) (.leaf 5240022768)) (.branch 6 (.leaf 5087502120) (.leaf 4941641995)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4802064792) (.leaf 4668418424)) (.branch 10 (.leaf 4540374268) (.leaf 4417625320))) (.branch 13 (.branch 12 (.leaf 4299884521) (.leaf 4186883235)) (.branch 14 (.leaf 4078369877) (.leaf 3974108646))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3873878387) (.branch 17 (.leaf 3777471534) (.leaf 3684693154))) (.branch 20 (.branch 19 (.leaf 3595360061) (.leaf 3509300013)) (.branch 21 (.leaf 3426350957) (.leaf 3346360352)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3269184528) (.leaf 3194688105)) (.branch 25 (.leaf 3122743453) (.leaf 3053230185))) (.branch 28 (.branch 27 (.leaf 2986034702) (.leaf 2921049753)) (.branch 29 (.leaf 2858174043) (.leaf 2797311858)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2738372719) (.branch 32 (.leaf 2681271062) (.leaf 2625925940))) (.branch 35 (.branch 34 (.leaf 2572260738) (.leaf 2520202921)) (.branch 36 (.leaf 2469683783) (.leaf 2420638224)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2373004538) (.leaf 2326724212)) (.branch 40 (.leaf 2281741745) (.leaf 2238004467))) (.branch 43 (.branch 42 (.leaf 2195462382) (.leaf 2154068015)) (.branch 44 (.leaf 2113776264) (.leaf 2074544273))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2036331300) (.branch 47 (.leaf 1999098601) (.leaf 1962809320))) (.branch 50 (.branch 49 (.leaf 1927428384) (.leaf 1892922404)) (.branch 51 (.leaf 1859259583) (.leaf 1826409632)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1794343682) (.leaf 1763034217)) (.branch 55 (.leaf 1732454991) (.leaf 1702580969))) (.branch 58 (.branch 57 (.leaf 1673388257) (.leaf 1644854043)) (.branch 59 (.leaf 1616956541) (.leaf 1589674939))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1562989343) (.branch 62 (.leaf 1536880734) (.leaf 1511330922))) (.branch 65 (.branch 64 (.leaf 1486322501) (.leaf 1461838812)) (.branch 66 (.leaf 1437863903) (.leaf 1414382495)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1391379946) (.leaf 1368842220)) (.branch 70 (.leaf 1346755857) (.leaf 1325107944))) (.branch 73 (.branch 72 (.leaf 1303886090) (.leaf 1283078396)) (.branch 74 (.leaf 1262673435) (.leaf 1242660229))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1223028223) (.branch 77 (.leaf 1203767269) (.leaf 1184867607))) (.branch 80 (.branch 79 (.leaf 1166319841) (.leaf 1148114929)) (.branch 81 (.leaf 1130244161) (.leaf 1112699146)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1095471796) (.leaf 1078554313)) (.branch 85 (.leaf 1061939175) (.leaf 1045619125))) (.branch 88 (.branch 87 (.leaf 1029587154) (.leaf 1013836499)) (.branch 89 (.leaf 998360621) (.leaf 983153204)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 968208141) (.branch 92 (.leaf 953519524) (.leaf 939081638))) (.branch 95 (.branch 94 (.leaf 924888952) (.leaf 910936111)) (.branch 96 (.leaf 897217925) (.leaf 883729369)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 870465569) (.leaf 857421802)) (.branch 100 (.leaf 844593483) (.leaf 831976167))) (.branch 103 (.branch 102 (.leaf 819565537) (.leaf 807357400)) (.branch 104 (.leaf 795347686) (.leaf 783532438))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 771907812) (.leaf 760470068)) (.branch 108 (.leaf 749215571) (.leaf 738140781))) (.branch 111 (.branch 110 (.leaf 727242257) (.leaf 716516645)) (.branch 112 (.leaf 705960683) (.leaf 695571189)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 685345065) (.leaf 675279292)) (.branch 116 (.leaf 665370925) (.leaf 655617093))) (.branch 119 (.branch 118 (.leaf 646014995) (.leaf 636561897)) (.branch 120 (.leaf 627255133) (.leaf 618092098)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 83).prefactor = (2474731868759581/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 83).cutoff/(generalMeanRows 83).c)).2 =
    (59443862730637/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 83).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 83).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 83).q*(generalMeanRows 83).c/2-2 = (9/16:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable040.value]
    have hcontinuation : (generalMeanRows 83).q*(generalMeanRows 83).cutoff/2-2 = (121/57:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable049.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 83).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 83

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 83).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 83).criticalRate j.val*(generalMeanRows 83).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 83).c*(generalMeanRows 83).criticalPoint j.val)).2-
      (generalMeanRows 83).J/2-(generalMeanRows 83).error (generalMeanGrid j.val)+
      (generalMeanRows 83).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 83).c)).2-
      (generalMeanRows 83).J/2-(generalMeanRows 83).error 4 := by
  have he : (generalMeanRows 83).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 83) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 83)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0083

/-! Kernel-checked entropy margins for general spectral rectangle 84. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0084
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5994505516) (.branch 2 (.leaf 5805309855) (.leaf 5624863602))) (.branch 5 (.branch 4 (.leaf 5452646204) (.leaf 5288174500)) (.branch 6 (.leaf 5130999464) (.leaf 4980703292)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4836896793) (.leaf 4699217055)) (.branch 10 (.leaf 4567325327) (.leaf 4440905125))) (.branch 13 (.branch 12 (.leaf 4319660501) (.leaf 4203314481)) (.branch 14 (.leaf 4091607648) (.leaf 3984296843))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3881153985) (.branch 17 (.leaf 3781964991) (.leaf 3686528784))) (.branch 20 (.branch 19 (.leaf 3594656389) (.leaf 3506170097)) (.branch 21 (.leaf 3420902695) (.leaf 3338696765)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3259404026) (.leaf 3182884736)) (.branch 25 (.leaf 3109007132) (.leaf 3037646917))) (.branch 28 (.branch 27 (.leaf 2968686779) (.leaf 2902015953)) (.branch 29 (.leaf 2837529802) (.leaf 2775129443)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2714721385) (.branch 32 (.leaf 2656217202) (.leaf 2599533223))) (.branch 35 (.branch 34 (.leaf 2544590245) (.leaf 2491313265)) (.branch 36 (.leaf 2439631227) (.leaf 2389476796)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2340786130) (.leaf 2293498681)) (.branch 40 (.leaf 2247557005) (.leaf 2202906580))) (.branch 43 (.branch 42 (.leaf 2159495638) (.leaf 2117275010)) (.branch 44 (.leaf 2076197980) (.leaf 2036220143))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1997299276) (.branch 47 (.leaf 1959395222) (.leaf 1922469766))) (.branch 50 (.branch 49 (.leaf 1886486536) (.leaf 1851410899)) (.branch 51 (.leaf 1817209864) (.leaf 1783851996)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1751307331) (.leaf 1719547296)) (.branch 55 (.leaf 1688544636) (.leaf 1658273341))) (.branch 58 (.branch 57 (.leaf 1628708585) (.leaf 1599826660)) (.branch 59 (.leaf 1571604916) (.leaf 1544021710))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1517056351) (.branch 62 (.leaf 1490689052) (.leaf 1464900882))) (.branch 65 (.branch 64 (.leaf 1439673725) (.leaf 1414990233)) (.branch 66 (.leaf 1390833795) (.leaf 1367188494)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1344039072) (.leaf 1321370903)) (.branch 70 (.leaf 1299169953) (.leaf 1277422759))) (.branch 73 (.branch 72 (.leaf 1256116396) (.leaf 1235238451)) (.branch 74 (.leaf 1214777002) (.leaf 1194720589))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1175058195) (.branch 77 (.leaf 1155779224) (.leaf 1136873481))) (.branch 80 (.branch 79 (.leaf 1118331154) (.leaf 1100142795)) (.branch 81 (.leaf 1082299301) (.leaf 1064791904)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1047612147) (.leaf 1030751879)) (.branch 85 (.leaf 1014203234) (.leaf 997958620))) (.branch 88 (.branch 87 (.leaf 982010709) (.leaf 966352423)) (.branch 89 (.leaf 950976922) (.leaf 935877596)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 921048054) (.branch 92 (.leaf 906482113) (.leaf 892173792))) (.branch 95 (.branch 94 (.leaf 878117301) (.leaf 864307031)) (.branch 96 (.leaf 850737553) (.leaf 837403603)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 824300080) (.leaf 811422038)) (.branch 100 (.leaf 798764677) (.leaf 786323341))) (.branch 103 (.branch 102 (.leaf 774093512) (.leaf 762070800)) (.branch 104 (.leaf 750250942) (.leaf 738629799))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 727203343) (.leaf 715967662)) (.branch 108 (.leaf 704918950) (.leaf 694053503))) (.branch 111 (.branch 110 (.leaf 683367718) (.leaf 672858089)) (.branch 112 (.leaf 662521199) (.leaf 652353723)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 642352420) (.leaf 632514131)) (.branch 116 (.leaf 622835779) (.leaf 613314361))) (.branch 119 (.branch 118 (.leaf 603946951) (.leaf 594730691)) (.branch 120 (.leaf 585662796) (.leaf 576740546)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 84).prefactor = (127638570946363/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 84).cutoff/(generalMeanRows 84).c)).2 =
    (58230260964767/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 84).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 84).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 84).q*(generalMeanRows 84).c/2-2 = (47/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable034.value]
    have hcontinuation : (generalMeanRows 84).q*(generalMeanRows 84).cutoff/2-2 = (121/57:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable049.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 84).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 84

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 84).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 84).criticalRate j.val*(generalMeanRows 84).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 84).c*(generalMeanRows 84).criticalPoint j.val)).2-
      (generalMeanRows 84).J/2-(generalMeanRows 84).error (generalMeanGrid j.val)+
      (generalMeanRows 84).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 84).c)).2-
      (generalMeanRows 84).J/2-(generalMeanRows 84).error 4 := by
  have he : (generalMeanRows 84).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 84) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 84)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0084

/-! Kernel-checked entropy margins for general spectral rectangle 85. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0085
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5518361399) (.branch 2 (.leaf 5325291507) (.leaf 5141282536))) (.branch 5 (.branch 4 (.leaf 4965799710) (.leaf 4798346518)) (.branch 6 (.leaf 4638461379) (.leaf 4485714659)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4339706005) (.leaf 4200061947)) (.branch 10 (.leaf 4066433740) (.leaf 3938495421))) (.branch 13 (.branch 12 (.leaf 3815942038) (.leaf 3698488061)) (.branch 14 (.leaf 3585865918) (.leaf 3477824683))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3374128856) (.branch 17 (.leaf 3274557269) (.leaf 3178902069))) (.branch 20 (.branch 19 (.leaf 3086967793) (.leaf 2998570515)) (.branch 21 (.leaf 2913537062) (.leaf 2831704292)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2752918431) (.leaf 2677034452)) (.branch 25 (.leaf 2603915513) (.leaf 2533432425))) (.branch 28 (.branch 27 (.leaf 2465463170) (.leaf 2399892441)) (.branch 29 (.leaf 2336611232) (.leaf 2275516437)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2216510496) (.branch 32 (.leaf 2159501053) (.leaf 2104400641))) (.branch 35 (.branch 34 (.leaf 2051126391) (.leaf 1999599755)) (.branch 36 (.leaf 1949746256) (.leaf 1901495242)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1854779669) (.leaf 1809535891)) (.branch 40 (.leaf 1765703463) (.leaf 1723224958))) (.branch 43 (.branch 42 (.leaf 1682045800) (.leaf 1642114099)) (.branch 44 (.leaf 1603380501) (.leaf 1565798050))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1529322052) (.branch 47 (.leaf 1493909952) (.leaf 1459521215))) (.branch 50 (.branch 49 (.leaf 1426117222) (.leaf 1393661160)) (.branch 51 (.leaf 1362117927) (.leaf 1331454043)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1301637559) (.leaf 1272637983)) (.branch 55 (.leaf 1244426195) (.leaf 1216974383))) (.branch 58 (.branch 57 (.leaf 1190255970) (.leaf 1164245553)) (.branch 59 (.leaf 1138918841) (.leaf 1114252598))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1090224592) (.branch 62 (.leaf 1066813541) (.leaf 1043999067))) (.branch 65 (.branch 64 (.leaf 1021761651) (.leaf 1000082587)) (.branch 66 (.leaf 978943948) (.leaf 958328542)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 938219880) (.leaf 918602137)) (.branch 70 (.leaf 899460127) (.leaf 880779264))) (.branch 73 (.branch 72 (.leaf 862545542) (.leaf 844745499)) (.branch 74 (.leaf 827366198) (.leaf 810395198))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 793820535) (.branch 77 (.leaf 777630694) (.leaf 761814594))) (.branch 80 (.branch 79 (.leaf 746361566) (.leaf 731261332)) (.branch 81 (.leaf 716503993) (.leaf 702080004)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 687980165) (.leaf 674195604)) (.branch 85 (.leaf 660717760) (.leaf 647538371))) (.branch 88 (.branch 87 (.leaf 634649463) (.leaf 622043334)) (.branch 89 (.leaf 609712545) (.leaf 597649907)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 585848472) (.branch 92 (.leaf 574301521) (.leaf 563002557))) (.branch 95 (.branch 94 (.leaf 551945294) (.leaf 541123648)) (.branch 96 (.leaf 530531729) (.leaf 520163835)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 510014442) (.leaf 500078198)) (.branch 100 (.leaf 490349918) (.leaf 480824572))) (.branch 103 (.branch 102 (.leaf 471497285) (.leaf 462363329)) (.branch 104 (.leaf 453418114) (.leaf 444657188))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 436076230) (.leaf 427671042)) (.branch 108 (.leaf 419437548) (.leaf 411371789))) (.branch 111 (.branch 110 (.leaf 403469918) (.leaf 395728196)) (.branch 112 (.leaf 388142988) (.leaf 380710758)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 373428071) (.leaf 366291581)) (.branch 116 (.leaf 359298036) (.leaf 352444268))) (.branch 119 (.branch 118 (.leaf 345727196) (.leaf 339143817)) (.branch 120 (.leaf 332691211) (.leaf 326366531)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 85).prefactor = (2633271911012429/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 85).cutoff/(generalMeanRows 85).c)).2 =
    (81897830233401/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 85).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 85).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 85).q*(generalMeanRows 85).c/2-2 = (59/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable050.value]
    have hcontinuation : (generalMeanRows 85).q*(generalMeanRows 85).cutoff/2-2 = (121/57:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable049.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 85).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 85

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 85).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 85).criticalRate j.val*(generalMeanRows 85).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 85).c*(generalMeanRows 85).criticalPoint j.val)).2-
      (generalMeanRows 85).J/2-(generalMeanRows 85).error (generalMeanGrid j.val)+
      (generalMeanRows 85).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 85).c)).2-
      (generalMeanRows 85).J/2-(generalMeanRows 85).error 4 := by
  have he : (generalMeanRows 85).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 85) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 85)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0085

/-! Kernel-checked entropy margins for general spectral rectangle 86. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0086
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5497549636) (.branch 2 (.leaf 5322577611) (.leaf 5155774075))) (.branch 5 (.branch 4 (.leaf 4996644767) (.leaf 4844731397)) (.branch 6 (.leaf 4699608508) (.leaf 4560880663)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4428179937) (.leaf 4301163643)) (.branch 10 (.leaf 4179512306) (.leaf 4062927810))) (.branch 13 (.branch 12 (.leaf 3951131739) (.leaf 3843863857)) (.branch 14 (.leaf 3740880737) (.leaf 3641954504))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3546871693) (.branch 17 (.leaf 3455432199) (.leaf 3367448325))) (.branch 20 (.branch 19 (.leaf 3282743897) (.leaf 3201153463)) (.branch 21 (.leaf 3122521544) (.leaf 3046701959)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2973557187) (.leaf 2902957791)) (.branch 25 (.leaf 2834781878) (.leaf 2768914602))) (.branch 28 (.branch 27 (.leaf 2705247706) (.leaf 2643679092)) (.branch 29 (.leaf 2584112428) (.leaf 2526456782)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2470626276) (.branch 32 (.leaf 2416539774) (.leaf 2364120585))) (.branch 35 (.branch 34 (.leaf 2313296185) (.leaf 2263997968)) (.branch 36 (.leaf 2216160999) (.leaf 2169723800)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2124628134) (.leaf 2080818817)) (.branch 40 (.leaf 2038243534) (.leaf 1996852668))) (.branch 43 (.branch 42 (.leaf 1956599145) (.leaf 1917438285)) (.branch 44 (.leaf 1879327660) (.leaf 1842226965))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1806097901) (.branch 47 (.leaf 1770904053) (.leaf 1736610788))) (.branch 50 (.branch 49 (.leaf 1703185152) (.leaf 1670595780)) (.branch 51 (.leaf 1638812801) (.leaf 1607807759)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1577553535) (.leaf 1548024270)) (.branch 55 (.leaf 1519195303) (.leaf 1491043097))) (.branch 58 (.branch 57 (.leaf 1463545186) (.leaf 1436680114)) (.branch 59 (.leaf 1410427379) (.leaf 1384767388))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1359681402) (.branch 62 (.leaf 1335151497) (.leaf 1311160518))) (.branch 65 (.branch 64 (.leaf 1287692040) (.leaf 1264730331)) (.branch 66 (.leaf 1242260315) (.leaf 1220267538)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1198738140) (.leaf 1177658820)) (.branch 70 (.leaf 1157016811) (.leaf 1136799855))) (.branch 73 (.branch 72 (.leaf 1116996171) (.leaf 1097594440)) (.branch 74 (.leaf 1078583778) (.leaf 1059953712))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1041694167) (.branch 77 (.leaf 1023795441) (.leaf 1006248191))) (.branch 80 (.branch 79 (.leaf 989043413) (.leaf 972172429)) (.branch 81 (.leaf 955626868) (.leaf 939398656)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 923480001) (.leaf 907863376)) (.branch 85 (.leaf 892541515) (.leaf 877507392))) (.branch 88 (.branch 87 (.leaf 862754220) (.leaf 848275431)) (.branch 89 (.leaf 834064674) (.leaf 820115799)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 806422856) (.branch 92 (.leaf 792980078) (.leaf 779781880))) (.branch 95 (.branch 94 (.leaf 766822847) (.leaf 754097729)) (.branch 96 (.leaf 741601434) (.leaf 729329022)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 717275695) (.leaf 705436798)) (.branch 100 (.leaf 693807808) (.leaf 682384329))) (.branch 103 (.branch 102 (.leaf 671162091) (.leaf 660136941)) (.branch 104 (.leaf 649304840) (.leaf 638661859))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 628204175) (.leaf 617928067)) (.branch 108 (.leaf 607829909) (.leaf 597906174))) (.branch 111 (.branch 110 (.leaf 588153421) (.leaf 578568300)) (.branch 112 (.leaf 569147544) (.leaf 559887970)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 550786469) (.leaf 541840013)) (.branch 116 (.leaf 533045645) (.leaf 524400478))) (.branch 119 (.branch 118 (.leaf 515901697) (.leaf 507546551)) (.branch 120 (.leaf 499332354) (.leaf 491256481)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 86).prefactor = (4922238967174953/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 86).cutoff/(generalMeanRows 86).c)).2 =
    (95696404530791/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 86).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 86).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 86).q*(generalMeanRows 86).cutoff/2-2 = (298/133:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable051.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 86).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 86

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 86).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 86).criticalRate j.val*(generalMeanRows 86).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 86).c*(generalMeanRows 86).criticalPoint j.val)).2-
      (generalMeanRows 86).J/2-(generalMeanRows 86).error (generalMeanGrid j.val)+
      (generalMeanRows 86).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 86).c)).2-
      (generalMeanRows 86).J/2-(generalMeanRows 86).error 4 := by
  have he : (generalMeanRows 86).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 86) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 86)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0086

/-! Kernel-checked entropy margins for general spectral rectangle 87. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0087
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5545134964) (.branch 2 (.leaf 5365459443) (.leaf 5194190631))) (.branch 5 (.branch 4 (.leaf 5030820691) (.leaf 4874878719)) (.branch 6 (.leaf 4725927519) (.leaf 4583560717)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4447400185) (.leaf 4317093708)) (.branch 10 (.leaf 4192312899) (.leaf 4072751305))) (.branch 13 (.branch 12 (.leaf 3958122694) (.leaf 3848159504)) (.branch 14 (.leaf 3742611428) (.leaf 3641244129))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3543838063) (.branch 17 (.leaf 3450187408) (.leaf 3360099076))) (.branch 20 (.branch 19 (.leaf 3273391819) (.leaf 3189895393)) (.branch 21 (.leaf 3109449799) (.leaf 3031904585)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2957118193) (.leaf 2884957367)) (.branch 25 (.leaf 2815296601) (.leaf 2748017627))) (.branch 28 (.branch 27 (.leaf 2683008942) (.leaf 2620165377)) (.branch 29 (.leaf 2559387680) (.leaf 2500582150)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2443660279) (.branch 32 (.leaf 2388538432) (.leaf 2335137541))) (.branch 35 (.branch 34 (.leaf 2283382822) (.leaf 2233203515)) (.branch 36 (.leaf 2184532641) (.leaf 2137306765)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2091465793) (.leaf 2046952765)) (.branch 40 (.leaf 2003713674) (.leaf 1961697288))) (.branch 43 (.branch 42 (.leaf 1920854992) (.leaf 1881140629)) (.branch 44 (.leaf 1842510364) (.leaf 1804922548))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1768337590) (.branch 47 (.leaf 1732717845) (.leaf 1698027500))) (.branch 50 (.branch 49 (.leaf 1664232473) (.leaf 1631300313)) (.branch 51 (.leaf 1599200114) (.leaf 1567902426)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1537379174) (.leaf 1507603587)) (.branch 55 (.leaf 1478550124) (.leaf 1450194406))) (.branch 58 (.branch 57 (.leaf 1422513156) (.leaf 1395484141)) (.branch 59 (.leaf 1369086112) (.leaf 1343298757))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1318102646) (.branch 62 (.leaf 1293479191) (.leaf 1269410597))) (.branch 65 (.branch 64 (.leaf 1245879824) (.leaf 1222870547)) (.branch 66 (.leaf 1200367120) (.leaf 1178354540)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1156818417) (.leaf 1135744940)) (.branch 70 (.leaf 1115120851) (.leaf 1094933417))) (.branch 73 (.branch 72 (.leaf 1075170402) (.leaf 1055820043)) (.branch 74 (.leaf 1036871032) (.leaf 1018312487))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1000133936) (.branch 77 (.leaf 982325293) (.leaf 964876848))) (.branch 80 (.branch 79 (.leaf 947779240) (.leaf 931023445)) (.branch 81 (.leaf 914600762) (.leaf 898502794)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 882721439) (.leaf 867248871)) (.branch 85 (.leaf 852077532) (.leaf 837200118))) (.branch 88 (.branch 87 (.leaf 822609570) (.leaf 808299057)) (.branch 89 (.leaf 794261976) (.leaf 780491933)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 766982738) (.branch 92 (.leaf 753728398) (.leaf 740723104))) (.branch 95 (.branch 94 (.leaf 727961228) (.leaf 715437312)) (.branch 96 (.leaf 703146064) (.leaf 691082349)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 679241182) (.leaf 667617725)) (.branch 100 (.leaf 656207280) (.leaf 645005282))) (.branch 103 (.branch 102 (.leaf 634007294) (.leaf 623209005)) (.branch 104 (.leaf 612606221) (.leaf 602194866))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 591970970) (.leaf 581930672)) (.branch 108 (.leaf 572070214) (.leaf 562385935))) (.branch 111 (.branch 110 (.leaf 552874269) (.leaf 543531744)) (.branch 112 (.leaf 534354974) (.leaf 525340660)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 516485585) (.leaf 507786612)) (.branch 116 (.leaf 499240680) (.leaf 490844804))) (.branch 119 (.branch 118 (.leaf 482596069) (.leaf 474491632)) (.branch 120 (.leaf 466528716) (.leaf 458704609)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 87).prefactor = (1012192877998879/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 87).cutoff/(generalMeanRows 87).c)).2 =
    (469391050952703/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 87).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 87).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 87).q*(generalMeanRows 87).c/2-2 = (163/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable052.value]
    have hcontinuation : (generalMeanRows 87).q*(generalMeanRows 87).cutoff/2-2 = (298/133:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable051.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 87).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 87

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 87).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 87).criticalRate j.val*(generalMeanRows 87).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 87).c*(generalMeanRows 87).criticalPoint j.val)).2-
      (generalMeanRows 87).J/2-(generalMeanRows 87).error (generalMeanGrid j.val)+
      (generalMeanRows 87).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 87).c)).2-
      (generalMeanRows 87).J/2-(generalMeanRows 87).error 4 := by
  have he : (generalMeanRows 87).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 87) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 87)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0087

/-! Kernel-checked entropy margins for general spectral rectangle 88. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0088
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5094325518) (.branch 2 (.leaf 4912083631) (.leaf 4738526518))) (.branch 5 (.branch 4 (.leaf 4573133300) (.leaf 4415420802)) (.branch 6 (.leaf 4264940261) (.leaf 4121274381)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3984034701) (.leaf 3852859219)) (.branch 10 (.leaf 3727410263) (.leaf 3607372557))) (.branch 13 (.branch 12 (.leaf 3492451479) (.leaf 3382371473)) (.branch 14 (.leaf 3276874611) (.leaf 3175719282))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3078678991) (.branch 17 (.leaf 2985541267) (.leaf 2896106662))) (.branch 20 (.branch 19 (.leaf 2810187829) (.leaf 2727608678)) (.branch 21 (.leaf 2648203604) (.leaf 2571816769)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2498301444) (.leaf 2427519399)) (.branch 25 (.leaf 2359340345) (.leaf 2293641413))) (.branch 28 (.branch 27 (.leaf 2230306672) (.leaf 2169226682)) (.branch 29 (.leaf 2110298083) (.leaf 2053423211)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1998509737) (.branch 32 (.leaf 1945470342) (.leaf 1894222402))) (.branch 35 (.branch 34 (.leaf 1844687705) (.leaf 1796792180)) (.branch 36 (.leaf 1750465651) (.leaf 1705641599)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1662256949) (.leaf 1620251864)) (.branch 40 (.leaf 1579569556) (.leaf 1540156108))) (.branch 43 (.branch 42 (.leaf 1501960309) (.leaf 1464933497)) (.branch 44 (.leaf 1429029414) (.leaf 1394204070))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1360415614) (.branch 47 (.leaf 1327624214) (.leaf 1295791946))) (.branch 50 (.branch 49 (.leaf 1264882687) (.leaf 1234862016)) (.branch 51 (.leaf 1205697121) (.leaf 1177356712)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1149810937) (.leaf 1123031306)) (.branch 55 (.leaf 1096990621) (.leaf 1071662901))) (.branch 58 (.branch 57 (.leaf 1047023323) (.leaf 1023048159)) (.branch 59 (.leaf 999714719) (.leaf 977001299))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 954887128) (.branch 62 (.leaf 933352321) (.leaf 912377833))) (.branch 65 (.branch 64 (.leaf 891945420) (.leaf 872037593)) (.branch 66 (.leaf 852637587) (.leaf 833729317)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 815297354) (.leaf 797326885)) (.branch 70 (.leaf 779803686) (.leaf 762714094))) (.branch 73 (.branch 72 (.leaf 746044980) (.leaf 729783721)) (.branch 74 (.leaf 713918180) (.leaf 698436681))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 683327986) (.branch 77 (.leaf 668581277) (.leaf 654186137))) (.branch 80 (.branch 79 (.leaf 640132528) (.leaf 626410780)) (.branch 81 (.leaf 613011567) (.leaf 599925898)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 587145097) (.leaf 574660793)) (.branch 85 (.leaf 562464905) (.leaf 550549630))) (.branch 88 (.branch 87 (.leaf 538907429) (.leaf 527531018)) (.branch 89 (.leaf 516413357) (.leaf 505547639)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 494927280) (.branch 92 (.leaf 484545910) (.leaf 474397365))) (.branch 95 (.branch 94 (.leaf 464475677) (.leaf 454775068)) (.branch 96 (.leaf 445289941) (.leaf 436014874)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 426944610) (.leaf 418074056)) (.branch 100 (.leaf 409398272) (.leaf 400912466))) (.branch 103 (.branch 102 (.leaf 392611989) (.leaf 384492331)) (.branch 104 (.leaf 376549114) (.leaf 368778085))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 361175118) (.leaf 353736202)) (.branch 108 (.leaf 346457442) (.leaf 339335051))) (.branch 111 (.branch 110 (.leaf 332365349) (.leaf 325544759)) (.branch 112 (.leaf 318869802) (.leaf 312337094)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 305943344) (.leaf 299685349)) (.branch 116 (.leaf 293559992) (.leaf 287564239))) (.branch 119 (.branch 118 (.leaf 281695137) (.leaf 275949810)) (.branch 120 (.leaf 270325457) (.leaf 264819350)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 88).prefactor = (1300899891675299/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 88).cutoff/(generalMeanRows 88).c)).2 =
    (104128824726189/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 88).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 88).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 88).q*(generalMeanRows 88).c/2-2 = (199/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable053.value]
    have hcontinuation : (generalMeanRows 88).q*(generalMeanRows 88).cutoff/2-2 = (298/133:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable051.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 88).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 88

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 88).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 88).criticalRate j.val*(generalMeanRows 88).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 88).c*(generalMeanRows 88).criticalPoint j.val)).2-
      (generalMeanRows 88).J/2-(generalMeanRows 88).error (generalMeanGrid j.val)+
      (generalMeanRows 88).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 88).c)).2-
      (generalMeanRows 88).J/2-(generalMeanRows 88).error 4 := by
  have he : (generalMeanRows 88).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 88) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 88)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0088

/-! Kernel-checked entropy margins for general spectral rectangle 89. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0089
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5049744632) (.branch 2 (.leaf 4863585449) (.leaf 4686365509))) (.branch 5 (.branch 4 (.leaf 4517549382) (.leaf 4356640335)) (.branch 6 (.leaf 4203176956) (.leaf 4056730129)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3916900331) (.leaf 3783315204)) (.branch 10 (.leaf 3655627360) (.leaf 3533512403))) (.branch 13 (.branch 12 (.leaf 3416667140) (.leaf 3304807954)) (.branch 14 (.leaf 3197669326) (.leaf 3095002491))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2996574209) (.branch 17 (.leaf 2902165641) (.leaf 2811571323))) (.branch 20 (.branch 19 (.leaf 2724598221) (.leaf 2641064870)) (.branch 21 (.leaf 2560800571) (.leaf 2483644665)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2409445851) (.leaf 2338061568)) (.branch 25 (.leaf 2269357415) (.leaf 2203206619))) (.branch 28 (.branch 27 (.leaf 2139489542) (.leaf 2078093223)) (.branch 29 (.leaf 2018910952) (.leaf 1961841881)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1906790652) (.branch 32 (.leaf 1853667060) (.leaf 1802385737))) (.branch 35 (.branch 34 (.leaf 1752865855) (.leaf 1705030850)) (.branch 36 (.leaf 1658808171) (.leaf 1614129034)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1570928203) (.leaf 1529143781)) (.branch 40 (.leaf 1488717013) (.leaf 1449592105))) (.branch 43 (.branch 42 (.leaf 1411716055) (.leaf 1375038489)) (.branch 44 (.leaf 1339511516) (.leaf 1305089582))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1271729346) (.branch 47 (.leaf 1239389551) (.leaf 1208030909))) (.branch 50 (.branch 49 (.leaf 1177615996) (.leaf 1148109145)) (.branch 51 (.leaf 1119476354) (.leaf 1091685194)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1064704726) (.leaf 1038505418)) (.branch 55 (.leaf 1013059076) (.leaf 988338767))) (.branch 58 (.branch 57 (.leaf 964318757) (.leaf 940974446)) (.branch 59 (.leaf 918282313) (.leaf 896219855))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 874765538) (.branch 62 (.leaf 853898749) (.leaf 833599745))) (.branch 65 (.branch 64 (.leaf 813849614) (.leaf 794630231)) (.branch 66 (.leaf 775924219) (.leaf 757714912)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 739986322) (.leaf 722723103)) (.branch 70 (.leaf 705910522) (.leaf 689534429))) (.branch 73 (.branch 72 (.leaf 673581230) (.leaf 658037859)) (.branch 74 (.leaf 642891754) (.leaf 628130833))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 613743473) (.branch 77 (.leaf 599718487) (.leaf 586045106))) (.branch 80 (.branch 79 (.leaf 572712956) (.leaf 559712047)) (.branch 81 (.leaf 547032749) (.leaf 534665780)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 522602188) (.leaf 510833338)) (.branch 85 (.leaf 499350900) (.leaf 488146832))) (.branch 88 (.branch 87 (.leaf 477213369) (.leaf 466543014)) (.branch 89 (.leaf 456128521) (.leaf 445962890)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 436039354) (.branch 92 (.leaf 426351371) (.leaf 416892611))) (.branch 95 (.branch 94 (.leaf 407656952) (.leaf 398638470)) (.branch 96 (.leaf 389831429) (.leaf 381230276)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 372829634) (.leaf 364624292)) (.branch 100 (.leaf 356609203) (.leaf 348779475))) (.branch 103 (.branch 102 (.leaf 341130363) (.leaf 333657269)) (.branch 104 (.leaf 326355732) (.leaf 319221424))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 312250146) (.leaf 305437823)) (.branch 108 (.leaf 298780498) (.leaf 292274329))) (.branch 111 (.branch 110 (.leaf 285915586) (.leaf 279700645)) (.branch 112 (.leaf 273625986) (.leaf 267688186)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 261883921) (.leaf 256209957)) (.branch 116 (.leaf 250663153) (.leaf 245240452))) (.branch 119 (.branch 118 (.leaf 239938881) (.leaf 234755548)) (.branch 120 (.leaf 229687639) (.leaf 224732418)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 89).prefactor = (2675127343723799/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 89).cutoff/(generalMeanRows 89).c)).2 =
    (15979744453413/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 89).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 89).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 89).q*(generalMeanRows 89).cutoff/2-2 = (298/133:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable051.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 89).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 89

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 89).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 89).criticalRate j.val*(generalMeanRows 89).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 89).c*(generalMeanRows 89).criticalPoint j.val)).2-
      (generalMeanRows 89).J/2-(generalMeanRows 89).error (generalMeanGrid j.val)+
      (generalMeanRows 89).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 89).c)).2-
      (generalMeanRows 89).J/2-(generalMeanRows 89).error 4 := by
  have he : (generalMeanRows 89).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 89) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 89)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0089

/-! Kernel-checked entropy margins for general spectral rectangle 90. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0090
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5287594011) (.branch 2 (.leaf 5095541261) (.leaf 4912675036))) (.branch 5 (.branch 4 (.leaf 4738444764) (.leaf 4572339700)) (.branch 6 (.leaf 4413885440) (.leaf 4262640818)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4118195123) (.leaf 3980165590)) (.branch 10 (.leaf 3848195153) (.leaf 3721950403))) (.branch 13 (.branch 12 (.leaf 3601119746) (.leaf 3485411730)) (.branch 14 (.leaf 3374553525) (.leaf 3268289537))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3166380141) (.branch 17 (.leaf 3068600530) (.leaf 2974739655))) (.branch 20 (.branch 19 (.leaf 2884599253) (.leaf 2797992957)) (.branch 21 (.leaf 2714745479) (.leaf 2634691852)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2557676734) (.leaf 2483553771)) (.branch 25 (.leaf 2412184999) (.leaf 2343440297))) (.branch 28 (.branch 27 (.leaf 2277196877) (.leaf 2213338819)) (.branch 29 (.leaf 2151756628) (.leaf 2092346829)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2035011596) (.branch 32 (.leaf 1979658394) (.leaf 1926199660))) (.branch 35 (.branch 34 (.leaf 1874552495) (.leaf 1824638382)) (.branch 36 (.leaf 1776382923) (.leaf 1729715592)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1684569506) (.leaf 1640881210)) (.branch 40 (.leaf 1598590477) (.leaf 1557640118))) (.branch 43 (.branch 42 (.leaf 1517975810) (.leaf 1479545929)) (.branch 44 (.leaf 1442301397) (.leaf 1406195538))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1371183941) (.branch 47 (.leaf 1337224336) (.leaf 1304276474))) (.branch 50 (.branch 49 (.leaf 1272302015) (.leaf 1241264421)) (.branch 51 (.leaf 1211128863) (.leaf 1181862122)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1153432509) (.leaf 1125809775)) (.branch 55 (.leaf 1098965041) (.leaf 1072870724))) (.branch 58 (.branch 57 (.leaf 1047500465) (.leaf 1022829070)) (.branch 59 (.leaf 998832446) (.leaf 975487545))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 952772312) (.branch 62 (.leaf 930665631) (.leaf 909147281))) (.branch 65 (.branch 64 (.leaf 888197889) (.leaf 867798885)) (.branch 66 (.leaf 847932469) (.leaf 828581564)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 809729789) (.leaf 791361418)) (.branch 70 (.leaf 773461354) (.leaf 756015092))) (.branch 73 (.branch 72 (.leaf 739008699) (.leaf 722428780)) (.branch 74 (.leaf 706262454) (.leaf 690497333))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 675121497) (.branch 77 (.leaf 660123469) (.leaf 645492201))) (.branch 80 (.branch 79 (.leaf 631217051) (.leaf 617287762)) (.branch 81 (.leaf 603694451) (.leaf 590427587)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 577477978) (.leaf 564836754)) (.branch 85 (.leaf 552495356) (.leaf 540445520))) (.branch 88 (.branch 87 (.leaf 528679264) (.leaf 517188879)) (.branch 89 (.leaf 505966915) (.leaf 495006168)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 484299676) (.branch 92 (.leaf 473840703) (.leaf 463622733))) (.branch 95 (.branch 94 (.leaf 453639460) (.leaf 443884779)) (.branch 96 (.leaf 434352779) (.leaf 425037735)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 415934100) (.leaf 407036499)) (.branch 100 (.leaf 398339721) (.leaf 389838715))) (.branch 103 (.branch 102 (.leaf 381528582) (.leaf 373404568)) (.branch 104 (.leaf 365462063) (.leaf 357696591))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 350103807) (.leaf 342679495)) (.branch 108 (.leaf 335419556) (.leaf 328320012))) (.branch 111 (.branch 110 (.leaf 321376996) (.leaf 314586751)) (.branch 112 (.leaf 307945625) (.leaf 301450068)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 295096627) (.leaf 288881945)) (.branch 116 (.leaf 282802756) (.leaf 276855881))) (.branch 119 (.branch 118 (.leaf 271038230) (.leaf 265346793)) (.branch 120 (.leaf 259778640) (.leaf 254330920)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 90).prefactor = (5501043047918813/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 90).cutoff/(generalMeanRows 90).c)).2 =
    (407968238326299/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 90).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 90).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 90).q*(generalMeanRows 90).cutoff/2-2 = (298/133:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable051.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 90).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 90

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 90).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 90).criticalRate j.val*(generalMeanRows 90).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 90).c*(generalMeanRows 90).criticalPoint j.val)).2-
      (generalMeanRows 90).J/2-(generalMeanRows 90).error (generalMeanGrid j.val)+
      (generalMeanRows 90).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 90).c)).2-
      (generalMeanRows 90).J/2-(generalMeanRows 90).error 4 := by
  have he : (generalMeanRows 90).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 90) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 90)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0090

/-! Kernel-checked entropy margins for general spectral rectangle 91. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0091
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5293297865) (.branch 2 (.leaf 5121038231) (.leaf 4956903954))) (.branch 5 (.branch 4 (.leaf 4800395177) (.leaf 4651048989)) (.branch 6 (.leaf 4508436177) (.leaf 4372158331)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4241845244) (.leaf 4117152567)) (.branch 10 (.leaf 3997759706) (.leaf 3883367915))) (.branch 13 (.branch 12 (.leaf 3773698569) (.leaf 3668491599)) (.branch 14 (.leaf 3567504068) (.leaf 3470508874))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3377293568) (.branch 17 (.leaf 3287659271) (.leaf 3201419683))) (.branch 20 (.branch 19 (.leaf 3118400180) (.leaf 3038436977)) (.branch 21 (.leaf 2961376365) (.leaf 2887074008)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2815394292) (.leaf 2746209727)) (.branch 25 (.leaf 2679400399) (.leaf 2614853455))) (.branch 28 (.branch 27 (.leaf 2552462635) (.leaf 2492127834)) (.branch 29 (.leaf 2433754698) (.leaf 2377254247)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2322542533) (.branch 32 (.leaf 2269540310) (.leaf 2218172739))) (.branch 35 (.branch 34 (.leaf 2168369107) (.leaf 2120062568)) (.branch 36 (.leaf 2073189900) (.leaf 2027691285)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1983510092) (.leaf 1940592689)) (.branch 40 (.leaf 1898888254) (.leaf 1858348610))) (.branch 43 (.branch 42 (.leaf 1818928065) (.leaf 1780583260)) (.branch 44 (.leaf 1743273037) (.leaf 1706958303))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1671601911) (.branch 47 (.leaf 1637168548) (.leaf 1603624629))) (.branch 50 (.branch 49 (.leaf 1570938193) (.leaf 1539078814)) (.branch 51 (.leaf 1508017515) (.leaf 1477726682)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1448179988) (.leaf 1419352324)) (.branch 55 (.leaf 1391219730) (.leaf 1363759329))) (.branch 58 (.branch 57 (.leaf 1336949271) (.leaf 1310768676)) (.branch 59 (.leaf 1285197581) (.leaf 1260216891))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1235808332) (.branch 62 (.leaf 1211954408) (.leaf 1188638359))) (.branch 65 (.branch 64 (.leaf 1165844126) (.leaf 1143556308)) (.branch 66 (.leaf 1121760134) (.leaf 1100441429)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1079586580) (.leaf 1059182513)) (.branch 70 (.leaf 1039216663) (.leaf 1019676948))) (.branch 73 (.branch 72 (.leaf 1000551749) (.leaf 981829880)) (.branch 74 (.leaf 963500576) (.leaf 945553465))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 927978553) (.branch 77 (.leaf 910766205) (.leaf 893907128))) (.branch 80 (.branch 79 (.leaf 877392356) (.leaf 861213234)) (.branch 81 (.leaf 845361403) (.leaf 829828787)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 814607583) (.leaf 799690242)) (.branch 85 (.leaf 785069466) (.leaf 770738191))) (.branch 88 (.branch 87 (.leaf 756689579) (.leaf 742917009)) (.branch 89 (.leaf 729414065) (.leaf 716174530)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 703192377) (.branch 92 (.leaf 690461761) (.leaf 677977011))) (.branch 95 (.branch 94 (.leaf 665732623) (.leaf 653723254)) (.branch 96 (.leaf 641943717) (.leaf 630388969)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 619054113) (.leaf 607934388)) (.branch 100 (.leaf 597025164) (.leaf 586321938))) (.branch 103 (.branch 102 (.leaf 575820329) (.leaf 565516073)) (.branch 104 (.leaf 555405021) (.leaf 545483130))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 535746466) (.leaf 526191193)) (.branch 108 (.leaf 516813574) (.leaf 507609969))) (.branch 111 (.branch 110 (.leaf 498576825) (.leaf 489710680)) (.branch 112 (.leaf 481008158) (.leaf 472465963)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 464080880) (.leaf 455849772)) (.branch 116 (.leaf 447769575) (.leaf 439837300))) (.branch 119 (.branch 118 (.leaf 432050024) (.leaf 424404897)) (.branch 120 (.leaf 416899130) (.leaf 409530002)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 91).prefactor = (5073433996162651/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 91).cutoff/(generalMeanRows 91).c)).2 =
    (243170304633239/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 91).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 91).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 91).q*(generalMeanRows 91).c/2-2 = (691/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable054.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 91).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 91

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 91).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 91).criticalRate j.val*(generalMeanRows 91).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 91).c*(generalMeanRows 91).criticalPoint j.val)).2-
      (generalMeanRows 91).J/2-(generalMeanRows 91).error (generalMeanGrid j.val)+
      (generalMeanRows 91).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 91).c)).2-
      (generalMeanRows 91).J/2-(generalMeanRows 91).error 4 := by
  have he : (generalMeanRows 91).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 91) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 91)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0091

/-! Kernel-checked entropy margins for general spectral rectangle 92. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0092
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7254901306) (.branch 2 (.leaf 6986450240) (.leaf 6729846172))) (.branch 5 (.branch 4 (.leaf 6484447074) (.leaf 6249655321)) (.branch 6 (.leaf 6024913704) (.leaf 5809701888)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5603533271) (.leaf 5405952183)) (.branch 10 (.leaf 5216531371) (.leaf 5034869752))) (.branch 13 (.branch 12 (.leaf 4860590385) (.leaf 4693338643)) (.branch 14 (.leaf 4532780557) (.leaf 4378601319))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4230503915) (.branch 17 (.leaf 4088207884) (.leaf 3951448184))) (.branch 20 (.branch 19 (.leaf 3819974151) (.leaf 3693548553)) (.branch 21 (.leaf 3571946711) (.leaf 3454955701)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3342373611) (.leaf 3234008855)) (.branch 25 (.leaf 3129679549) (.leaf 3029212920))) (.branch 28 (.branch 27 (.leaf 2932444766) (.leaf 2839218956)) (.branch 29 (.leaf 2749386961) (.leaf 2662807416)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2579345723) (.branch 32 (.leaf 2498873666) (.leaf 2421269063))) (.branch 35 (.branch 34 (.leaf 2346415435) (.leaf 2274201696)) (.branch 36 (.leaf 2204521871) (.leaf 2137274819)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2072363982) (.leaf 2009697149)) (.branch 40 (.leaf 1949186228) (.leaf 1890747040))) (.branch 43 (.branch 42 (.leaf 1834299122) (.leaf 1779765534)) (.branch 44 (.leaf 1727072693) (.leaf 1676150201))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1626930690) (.branch 47 (.leaf 1579349677) (.leaf 1533345425))) (.branch 50 (.branch 49 (.leaf 1488858809) (.leaf 1445833192)) (.branch 51 (.leaf 1404214312) (.leaf 1363950164)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1324990901) (.leaf 1287288728)) (.branch 55 (.leaf 1250797814) (.leaf 1215474197))) (.branch 58 (.branch 57 (.leaf 1181275702) (.leaf 1148161859)) (.branch 59 (.leaf 1116093825) (.leaf 1085034315))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1054947528) (.branch 62 (.leaf 1025799088) (.leaf 997555972))) (.branch 65 (.branch 64 (.leaf 970186459) (.leaf 943660069)) (.branch 66 (.leaf 917947513) (.leaf 893020634)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 868852369) (.leaf 845416692)) (.branch 70 (.leaf 822688578) (.leaf 800643956))) (.branch 73 (.branch 72 (.leaf 779259669) (.leaf 758513437)) (.branch 74 (.leaf 738383822) (.leaf 718850189))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 699892674) (.branch 77 (.leaf 681492155) (.leaf 663630218))) (.branch 80 (.branch 79 (.leaf 646289131) (.leaf 629451812)) (.branch 81 (.leaf 613101807) (.leaf 597223262)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 581800902) (.leaf 566820003)) (.branch 85 (.leaf 552266373) (.leaf 538126331))) (.branch 88 (.branch 87 (.leaf 524386685) (.leaf 511034714)) (.branch 89 (.leaf 498058149) (.leaf 485445158)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 473184322) (.branch 92 (.leaf 461264626) (.leaf 449675440))) (.branch 95 (.branch 94 (.leaf 438406504) (.leaf 427447917)) (.branch 96 (.leaf 416790117) (.leaf 406423875)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 396340276) (.leaf 386530714)) (.branch 100 (.leaf 376986872) (.leaf 367700719))) (.branch 103 (.branch 102 (.leaf 358664493) (.leaf 349870697)) (.branch 104 (.leaf 341312083) (.leaf 332981646))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 324872617) (.leaf 316978448)) (.branch 108 (.leaf 309292810) (.leaf 301809583))) (.branch 111 (.branch 110 (.leaf 294522847) (.leaf 287426876)) (.branch 112 (.leaf 280516132) (.leaf 273785254)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 267229056) (.leaf 260842522)) (.branch 116 (.leaf 254620792) (.leaf 248559166))) (.branch 119 (.branch 118 (.leaf 242653092) (.leaf 236898162)) (.branch 120 (.leaf 231290109) (.leaf 225824799)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 92).prefactor = (384630601764083/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 92).cutoff/(generalMeanRows 92).c)).2 =
    (118939624983989/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 92).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 92).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 92).q*(generalMeanRows 92).c/2-2 = (17/20:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable055.value]
    have hcontinuation : (generalMeanRows 92).q*(generalMeanRows 92).cutoff/2-2 = (21/13:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable056.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 92).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 92

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 92).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 92).criticalRate j.val*(generalMeanRows 92).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 92).c*(generalMeanRows 92).criticalPoint j.val)).2-
      (generalMeanRows 92).J/2-(generalMeanRows 92).error (generalMeanGrid j.val)+
      (generalMeanRows 92).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 92).c)).2-
      (generalMeanRows 92).J/2-(generalMeanRows 92).error 4 := by
  have he : (generalMeanRows 92).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 92) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 92)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0092

/-! Kernel-checked entropy margins for general spectral rectangle 93. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0093
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7281963032) (.branch 2 (.leaf 7062413889) (.leaf 6852507758))) (.branch 5 (.branch 4 (.leaf 6651702994) (.leaf 6459495720)) (.branch 6 (.leaf 6275416503) (.leaf 6099027394)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5929919286) (.leaf 5767709558)) (.branch 10 (.leaf 5612039947) (.leaf 5462574650))) (.branch 13 (.branch 12 (.leaf 5318998594) (.leaf 5181015881)) (.branch 14 (.leaf 5048348374) (.leaf 4920734412))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4797927641) (.branch 17 (.leaf 4679695941) (.leaf 4565820449))) (.branch 20 (.branch 19 (.leaf 4456094665) (.leaf 4350323627)) (.branch 21 (.leaf 4248323152) (.leaf 4149919143)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4054946940) (.leaf 3963250731)) (.branch 25 (.leaf 3874682996) (.leaf 3789104004))) (.branch 28 (.branch 27 (.leaf 3706381333) (.leaf 3626389435)) (.branch 29 (.leaf 3549009230) (.leaf 3474127720)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3401637638) (.branch 32 (.leaf 3331437120) (.leaf 3263429392))) (.branch 35 (.branch 34 (.leaf 3197522486) (.leaf 3133628969)) (.branch 36 (.leaf 3071665691) (.leaf 3011553546)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2953217258) (.leaf 2896585164)) (.branch 40 (.leaf 2841589028) (.leaf 2788163851))) (.branch 43 (.branch 42 (.leaf 2736247703) (.leaf 2685781558)) (.branch 44 (.leaf 2636709145) (.leaf 2588976803))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2542533346) (.branch 47 (.leaf 2497329934) (.leaf 2453319957))) (.branch 50 (.branch 49 (.leaf 2410458919) (.leaf 2368704330)) (.branch 51 (.leaf 2328015607) (.leaf 2288353979)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2249682396) (.leaf 2211965443)) (.branch 55 (.leaf 2175169260) (.leaf 2139261467))) (.branch 58 (.branch 57 (.leaf 2104211091) (.leaf 2069988497)) (.branch 59 (.leaf 2036565324) (.leaf 2003914424))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1972009802) (.branch 62 (.leaf 1940826564) (.leaf 1910340862))) (.branch 65 (.branch 64 (.leaf 1880529848) (.leaf 1851371622)) (.branch 66 (.leaf 1822845191) (.leaf 1794930426)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1767608023) (.leaf 1740859461)) (.branch 70 (.leaf 1714666970) (.leaf 1689013493))) (.branch 73 (.branch 72 (.leaf 1663882658) (.leaf 1639258741)) (.branch 74 (.leaf 1615126642) (.leaf 1591471851))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1568280428) (.branch 77 (.leaf 1545538972) (.leaf 1523234600))) (.branch 80 (.branch 79 (.leaf 1501354921) (.leaf 1479888019)) (.branch 81 (.leaf 1458822426) (.leaf 1438147106)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1417851437) (.leaf 1397925189)) (.branch 85 (.leaf 1378358511) (.leaf 1359141910))) (.branch 88 (.branch 87 (.leaf 1340266241) (.leaf 1321722687)) (.branch 89 (.leaf 1303502750) (.leaf 1285598231)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1268001222) (.branch 92 (.leaf 1250704094) (.leaf 1233699483))) (.branch 95 (.branch 94 (.leaf 1216980278) (.leaf 1200539613)) (.branch 96 (.leaf 1184370856) (.leaf 1168467599)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1152823649) (.leaf 1137433018)) (.branch 100 (.leaf 1122289916) (.leaf 1107388742))) (.branch 103 (.branch 102 (.leaf 1092724079) (.leaf 1078290680)) (.branch 104 (.leaf 1064083470) (.leaf 1050097532))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1036328105) (.leaf 1022770573)) (.branch 108 (.leaf 1009420467) (.leaf 996273450))) (.branch 111 (.branch 110 (.leaf 983325319) (.leaf 970571997)) (.branch 112 (.leaf 958009529) (.leaf 945634074)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 933441907) (.leaf 921429408)) (.branch 116 (.leaf 909593061) (.leaf 897929453))) (.branch 119 (.branch 118 (.leaf 886435263) (.leaf 875107265)) (.branch 120 (.leaf 863942322) (.leaf 852937384)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 93).prefactor = (52317800455761/10000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 93).cutoff/(generalMeanRows 93).c)).2 =
    (212738931931387/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 93).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 93).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 93).q*(generalMeanRows 93).c/2-2 = (19/40:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable046.value]
    have hcontinuation : (generalMeanRows 93).q*(generalMeanRows 93).cutoff/2-2 = (488/273:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable057.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 93).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 93

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 93).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 93).criticalRate j.val*(generalMeanRows 93).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 93).c*(generalMeanRows 93).criticalPoint j.val)).2-
      (generalMeanRows 93).J/2-(generalMeanRows 93).error (generalMeanGrid j.val)+
      (generalMeanRows 93).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 93).c)).2-
      (generalMeanRows 93).J/2-(generalMeanRows 93).error 4 := by
  have he : (generalMeanRows 93).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 93) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 93)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0093

/-! Kernel-checked entropy margins for general spectral rectangle 94. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0094
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7463728851) (.branch 2 (.leaf 7234406752) (.leaf 7015161796))) (.branch 5 (.branch 4 (.leaf 6805428820) (.leaf 6604682061)) (.branch 6 (.leaf 6412431687) (.leaf 6228220708)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6051622224) (.leaf 5882236956)) (.branch 10 (.leaf 5719691039) (.leaf 5563634028))) (.branch 13 (.branch 12 (.leaf 5413737103) (.leaf 5269691443)) (.branch 14 (.leaf 5131206750) (.leaf 4998009908))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4869843766) (.branch 17 (.leaf 4746466016) (.leaf 4627648178))) (.branch 20 (.branch 19 (.leaf 4513174662) (.leaf 4402841910)) (.branch 21 (.leaf 4296457605) (.leaf 4193839949)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4094816984) (.leaf 3999225978)) (.branch 25 (.leaf 3906912846) (.leaf 3817731625))) (.branch 28 (.branch 27 (.leaf 3731543975) (.leaf 3648218725)) (.branch 29 (.leaf 3567631445) (.leaf 3489664050)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3414204433) (.branch 32 (.leaf 3341146119) (.leaf 3270387943))) (.branch 35 (.branch 34 (.leaf 3201833751) (.leaf 3135392118)) (.branch 36 (.leaf 3070976088) (.leaf 3008502922)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2947893876) (.leaf 2889073975)) (.branch 40 (.leaf 2831971816) (.leaf 2776519376))) (.branch 43 (.branch 42 (.leaf 2722651833) (.leaf 2670307394)) (.branch 44 (.leaf 2619427141) (.leaf 2569954879))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2521836993) (.branch 47 (.leaf 2475022322) (.leaf 2429462028))) (.branch 50 (.branch 49 (.leaf 2385109477) (.leaf 2341920135)) (.branch 51 (.leaf 2299851454) (.leaf 2258862781)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2218915255) (.leaf 2179971727)) (.branch 55 (.leaf 2141996669) (.leaf 2104956100))) (.branch 58 (.branch 57 (.leaf 2068817508) (.leaf 2033549777)) (.branch 59 (.leaf 1999123124) (.leaf 1965509032))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1932680191) (.branch 62 (.leaf 1900610440) (.leaf 1869274711))) (.branch 65 (.branch 64 (.leaf 1838648981) (.leaf 1808710218)) (.branch 66 (.leaf 1779436341) (.leaf 1750806171)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1722799389) (.leaf 1695396500)) (.branch 70 (.leaf 1668578790) (.leaf 1642328297))) (.branch 73 (.branch 72 (.leaf 1616627769) (.leaf 1591460638)) (.branch 74 (.leaf 1566810984) (.leaf 1542663512))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1519003518) (.branch 77 (.leaf 1495816864) (.leaf 1473089955))) (.branch 80 (.branch 79 (.leaf 1450809714) (.leaf 1428963557)) (.branch 81 (.leaf 1407539375) (.leaf 1386525509)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1365910734) (.leaf 1345684238)) (.branch 85 (.leaf 1325835605) (.leaf 1306354796))) (.branch 88 (.branch 87 (.leaf 1287232138) (.leaf 1268458300)) (.branch 89 (.leaf 1250024288) (.leaf 1231921422)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1214141328) (.branch 92 (.leaf 1196675925) (.leaf 1179517409))) (.branch 95 (.branch 94 (.leaf 1162658245) (.leaf 1146091156)) (.branch 96 (.leaf 1129809107) (.leaf 1113805304)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1098073175) (.leaf 1082606367)) (.branch 100 (.leaf 1067398736) (.leaf 1052444335))) (.branch 103 (.branch 102 (.leaf 1037737411) (.leaf 1023272394)) (.branch 104 (.leaf 1009043891) (.leaf 995046678))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 981275694) (.leaf 967726035)) (.branch 108 (.leaf 954392948) (.leaf 941271823))) (.branch 111 (.branch 110 (.leaf 928358190) (.leaf 915647712)) (.branch 112 (.leaf 903136181) (.leaf 890819511)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 878693737) (.leaf 866755008)) (.branch 116 (.leaf 854999581) (.leaf 843423821))) (.branch 119 (.branch 118 (.leaf 832024195) (.leaf 820797268)) (.branch 120 (.leaf 809739698) (.leaf 798848238)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 94).prefactor = (5466326003801253/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 94).cutoff/(generalMeanRows 94).c)).2 =
    (414428027676191/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 94).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 94).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 94).q*(generalMeanRows 94).c/2-2 = (201/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable029.value]
    have hcontinuation : (generalMeanRows 94).q*(generalMeanRows 94).cutoff/2-2 = (488/273:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable057.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 94).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 94

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 94).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 94).criticalRate j.val*(generalMeanRows 94).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 94).c*(generalMeanRows 94).criticalPoint j.val)).2-
      (generalMeanRows 94).J/2-(generalMeanRows 94).error (generalMeanGrid j.val)+
      (generalMeanRows 94).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 94).c)).2-
      (generalMeanRows 94).J/2-(generalMeanRows 94).error 4 := by
  have he : (generalMeanRows 94).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 94) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 94)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0094

/-! Kernel-checked entropy margins for general spectral rectangle 95. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0095
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6497837637) (.branch 2 (.leaf 6263370022) (.leaf 6039448903))) (.branch 5 (.branch 4 (.leaf 5825488116) (.leaf 5620942210)) (.branch 6 (.leaf 5425302854) (.leaf 5238095642)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5058877243) (.leaf 4887232853)) (.branch 10 (.leaf 4722773910) (.leaf 4565136032))) (.branch 13 (.branch 12 (.leaf 4413977162) (.leaf 4268975891)) (.branch 14 (.leaf 4129829929) (.leaf 3996254728))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3867982214) (.branch 17 (.leaf 3744759640) (.leaf 3626348532))) (.branch 20 (.branch 19 (.leaf 3512523726) (.leaf 3403072481)) (.branch 21 (.leaf 3297793665) (.leaf 3196497006)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3099002401) (.leaf 3005139275)) (.branch 25 (.leaf 2914745995) (.leaf 2827669316))) (.branch 28 (.branch 27 (.leaf 2743763879) (.leaf 2662891738)) (.branch 29 (.leaf 2584921921) (.leaf 2509730025)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2437197831) (.branch 32 (.leaf 2367212958) (.leaf 2299668524))) (.branch 35 (.branch 34 (.leaf 2234462846) (.leaf 2171499141)) (.branch 36 (.leaf 2110685265) (.leaf 2051933455)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1995160093) (.leaf 1940285485)) (.branch 40 (.leaf 1887233649) (.leaf 1835932120))) (.branch 43 (.branch 42 (.leaf 1786311768) (.leaf 1738306622)) (.branch 44 (.leaf 1691853706) (.leaf 1646892889))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1603366735) (.branch 47 (.leaf 1561220373) (.leaf 1520401362))) (.branch 50 (.branch 49 (.leaf 1480859573) (.leaf 1442547073)) (.branch 51 (.leaf 1405418018) (.leaf 1369428549)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1334536696) (.leaf 1300702288)) (.branch 55 (.leaf 1267886863) (.leaf 1236053588))) (.branch 58 (.branch 57 (.leaf 1205167183) (.leaf 1175193844)) (.branch 59 (.leaf 1146101176) (.leaf 1117858126))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1090434921) (.branch 62 (.leaf 1063803008) (.leaf 1037934998))) (.branch 65 (.branch 64 (.leaf 1012804611) (.leaf 988386628)) (.branch 66 (.leaf 964656842) (.leaf 941592010)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 919169812) (.leaf 897368810)) (.branch 70 (.leaf 876168406) (.leaf 855548805))) (.branch 73 (.branch 72 (.leaf 835490985) (.leaf 815976653)) (.branch 74 (.leaf 796988224) (.leaf 778508781))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 760522052) (.branch 77 (.leaf 743012379) (.leaf 725964693))) (.branch 80 (.branch 79 (.leaf 709364489) (.leaf 693197799)) (.branch 81 (.leaf 677451176) (.leaf 662111662)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 647166778) (.leaf 632604496)) (.branch 85 (.leaf 618413224) (.leaf 604581787))) (.branch 88 (.branch 87 (.leaf 591099410) (.leaf 577955700)) (.branch 89 (.leaf 565140636) (.leaf 552644544)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 540458093) (.branch 92 (.leaf 528572273) (.leaf 516978390))) (.branch 95 (.branch 94 (.leaf 505668046) (.leaf 494633131)) (.branch 96 (.leaf 483865811) (.leaf 473358519)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 463103939) (.leaf 453095002)) (.branch 100 (.leaf 443324875) (.leaf 433786949))) (.branch 103 (.branch 102 (.leaf 424474834) (.leaf 415382347)) (.branch 104 (.leaf 406503508) (.leaf 397832530))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 389363811) (.leaf 381091930)) (.branch 108 (.leaf 373011637) (.leaf 365117847))) (.branch 111 (.branch 110 (.leaf 357405638) (.leaf 349870238)) (.branch 112 (.leaf 342507026) (.leaf 335311523)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 328279388) (.leaf 321406412)) (.branch 116 (.leaf 314688513) (.leaf 308121736))) (.branch 119 (.branch 118 (.leaf 301702240) (.leaf 295426302)) (.branch 120 (.leaf 289290309) (.leaf 283290754)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 95).prefactor = (5711386893090123/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 95).cutoff/(generalMeanRows 95).c)).2 =
    (310167017351783/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 95).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 95).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 95).q*(generalMeanRows 95).c/2-2 = (311/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable032.value]
    have hcontinuation : (generalMeanRows 95).q*(generalMeanRows 95).cutoff/2-2 = (488/273:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable057.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 95).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 95

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 95).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 95).criticalRate j.val*(generalMeanRows 95).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 95).c*(generalMeanRows 95).criticalPoint j.val)).2-
      (generalMeanRows 95).J/2-(generalMeanRows 95).error (generalMeanGrid j.val)+
      (generalMeanRows 95).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 95).c)).2-
      (generalMeanRows 95).J/2-(generalMeanRows 95).error 4 := by
  have he : (generalMeanRows 95).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 95) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 95)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0095

/-! Kernel-checked entropy margins for general spectral rectangle 96. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0096
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6097921453) (.branch 2 (.leaf 5916080933) (.leaf 5742450531))) (.branch 5 (.branch 4 (.leaf 5576550423) (.leaf 5417934873)) (.branch 6 (.leaf 5266189257) (.leaf 5120927419)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4981789293) (.leaf 4848438775)) (.branch 10 (.leaf 4720561810) (.leaf 4597864662))) (.branch 13 (.branch 12 (.leaf 4480072350) (.leaf 4366927230)) (.branch 14 (.leaf 4258187709) (.leaf 4153627068))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4053032394) (.branch 17 (.leaf 3956203599) (.leaf 3862952526))) (.branch 20 (.branch 19 (.leaf 3773102124) (.leaf 3686485695)) (.branch 21 (.leaf 3602946197) (.leaf 3522335601)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3444514305) (.leaf 3369350582)) (.branch 25 (.leaf 3296720079) (.leaf 3226505347))) (.branch 28 (.branch 27 (.leaf 3158595404) (.leaf 3092885337)) (.branch 29 (.leaf 3029275928) (.leaf 2967673298)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2907988593) (.branch 32 (.leaf 2850137675) (.leaf 2794040846))) (.branch 35 (.branch 34 (.leaf 2739622579) (.leaf 2686811280)) (.branch 36 (.leaf 2635539053) (.leaf 2585741488)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2537357462) (.leaf 2490328949)) (.branch 40 (.leaf 2444600846) (.leaf 2400120806))) (.branch 43 (.branch 42 (.leaf 2356839086) (.leaf 2314708399)) (.branch 44 (.leaf 2273683782) (.leaf 2233722463))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2194783747) (.branch 47 (.leaf 2156828895) (.leaf 2119821026))) (.branch 50 (.branch 49 (.leaf 2083725013) (.leaf 2048507388)) (.branch 51 (.leaf 2014136255) (.leaf 1980581206)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1947813245) (.leaf 1915804707)) (.branch 55 (.leaf 1884529198) (.leaf 1853961518))) (.branch 58 (.branch 57 (.leaf 1824077610) (.leaf 1794854492)) (.branch 59 (.leaf 1766270207) (.leaf 1738303769))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1710935112) (.branch 62 (.leaf 1684145048) (.leaf 1657915217))) (.branch 65 (.branch 64 (.leaf 1632228050) (.leaf 1607066726)) (.branch 66 (.leaf 1582415137) (.leaf 1558257853)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1534580086) (.leaf 1511367660)) (.branch 70 (.leaf 1488606984) (.leaf 1466285016))) (.branch 73 (.branch 72 (.leaf 1444389245) (.leaf 1422907660)) (.branch 74 (.leaf 1401828727) (.leaf 1381141368))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1360834936) (.branch 77 (.leaf 1340899197) (.leaf 1321324313))) (.branch 80 (.branch 79 (.leaf 1302100816) (.leaf 1283219599)) (.branch 81 (.leaf 1264671893) (.leaf 1246449255)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1228543553) (.leaf 1210946949)) (.branch 85 (.leaf 1193651888) (.leaf 1176651083))) (.branch 88 (.branch 87 (.leaf 1159937507) (.leaf 1143504378)) (.branch 89 (.leaf 1127345148) (.leaf 1111453494)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1095823308) (.branch 92 (.leaf 1080448686) (.leaf 1065323921))) (.branch 95 (.branch 94 (.leaf 1050443496) (.leaf 1035802070)) (.branch 96 (.leaf 1021394476) (.leaf 1007215711)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 993260932) (.leaf 979525444)) (.branch 100 (.leaf 966004698) (.leaf 952694285))) (.branch 103 (.branch 102 (.leaf 939589927) (.leaf 926687477)) (.branch 104 (.leaf 913982907) (.leaf 901472309))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 889151887) (.leaf 877017952)) (.branch 108 (.leaf 865066923) (.leaf 853295315))) (.branch 111 (.branch 110 (.leaf 841699741) (.leaf 830276908)) (.branch 112 (.leaf 819023608) (.leaf 807936723)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 797013215) (.leaf 786250125)) (.branch 116 (.leaf 775644571) (.leaf 765193746))) (.branch 119 (.branch 118 (.leaf 754894910) (.leaf 744745397)) (.branch 120 (.leaf 734742601) (.leaf 724883984)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 96).prefactor = (237004792140441/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 96).cutoff/(generalMeanRows 96).c)).2 =
    (469280486521167/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 96).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 96).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 96).q*(generalMeanRows 96).c/2-2 = (41/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable058.value]
    have hcontinuation : (generalMeanRows 96).q*(generalMeanRows 96).cutoff/2-2 = (236/117:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable059.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 96).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 96

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 96).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 96).criticalRate j.val*(generalMeanRows 96).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 96).c*(generalMeanRows 96).criticalPoint j.val)).2-
      (generalMeanRows 96).J/2-(generalMeanRows 96).error (generalMeanGrid j.val)+
      (generalMeanRows 96).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 96).c)).2-
      (generalMeanRows 96).J/2-(generalMeanRows 96).error 4 := by
  have he : (generalMeanRows 96).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 96) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 96)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0096

/-! Kernel-checked entropy margins for general spectral rectangle 97. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0097
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6183638471) (.branch 2 (.leaf 5995673587) (.leaf 5816201900))) (.branch 5 (.branch 4 (.leaf 5644727956) (.leaf 5480791485)) (.branch 6 (.leaf 5323964329) (.leaf 5173847707)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5030069764) (.leaf 4892283379)) (.branch 10 (.leaf 4760164179) (.leaf 4633408764))) (.branch 13 (.branch 12 (.leaf 4511733086) (.leaf 4394870991)) (.branch 14 (.leaf 4282572885) (.leaf 4174604524))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4070745912) (.branch 17 (.leaf 3970790285) (.leaf 3874543194))) (.branch 20 (.branch 19 (.leaf 3781821648) (.leaf 3692453340)) (.branch 21 (.leaf 3606275925) (.leaf 3523136365)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3442890312) (.leaf 3365401549)) (.branch 25 (.leaf 3290541466) (.leaf 3218188579))) (.branch 28 (.branch 27 (.leaf 3148228079) (.leaf 3080551421)) (.branch 29 (.leaf 3015055933) (.leaf 2951644462)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2890225035) (.branch 32 (.leaf 2830710550) (.leaf 2773018485))) (.branch 35 (.branch 34 (.leaf 2717070630) (.leaf 2662792828)) (.branch 36 (.leaf 2610114746) (.leaf 2558969648)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2509294190) (.leaf 2461028231)) (.branch 40 (.leaf 2414114642) (.leaf 2368499148))) (.branch 43 (.branch 42 (.leaf 2324130156) (.leaf 2280958617)) (.branch 44 (.leaf 2238937878) (.leaf 2198023552))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2158173396) (.branch 47 (.leaf 2119347192) (.leaf 2081506639))) (.branch 50 (.branch 49 (.leaf 2044615249) (.leaf 2008638250)) (.branch 51 (.leaf 1973542495) (.leaf 1939296377)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1905869746) (.leaf 1873233832)) (.branch 55 (.leaf 1841361176) (.leaf 1810225560))) (.branch 58 (.branch 57 (.leaf 1779801941) (.leaf 1750066395)) (.branch 59 (.leaf 1720996056) (.leaf 1692569064))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1664764511) (.branch 62 (.leaf 1637562399) (.leaf 1610943587))) (.branch 65 (.branch 64 (.leaf 1584889754) (.leaf 1559383353)) (.branch 66 (.leaf 1534407578) (.leaf 1509946323)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1485984150) (.leaf 1462506256)) (.branch 70 (.leaf 1439498442) (.leaf 1416947082))) (.branch 73 (.branch 72 (.leaf 1394839098) (.leaf 1373161933)) (.branch 74 (.leaf 1351903526) (.leaf 1331052285))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1310597073) (.branch 77 (.leaf 1290527177) (.leaf 1270832295))) (.branch 80 (.branch 79 (.leaf 1251502514) (.leaf 1232528293)) (.branch 81 (.leaf 1213900444) (.leaf 1195610119)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1177648790) (.leaf 1160008239)) (.branch 85 (.leaf 1142680541) (.leaf 1125658053))) (.branch 88 (.branch 87 (.leaf 1108933400) (.leaf 1092499461)) (.branch 89 (.leaf 1076349364) (.leaf 1060476467)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1044874357) (.branch 92 (.leaf 1029536829) (.leaf 1014457889))) (.branch 95 (.branch 94 (.leaf 999631736) (.leaf 985052757)) (.branch 96 (.leaf 970715521) (.leaf 956614765)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 942745397) (.leaf 929102478)) (.branch 100 (.leaf 915681224) (.leaf 902476994))) (.branch 103 (.branch 102 (.leaf 889485290) (.leaf 876701743)) (.branch 104 (.leaf 864122118) (.leaf 851742300))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 839558293) (.leaf 827566215)) (.branch 108 (.leaf 815762295) (.leaf 804142864))) (.branch 111 (.branch 110 (.leaf 792704357) (.leaf 781443305)) (.branch 112 (.leaf 770356334) (.leaf 759440158)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 748691579) (.leaf 738107483)) (.branch 116 (.leaf 727684835) (.leaf 717420680))) (.branch 119 (.branch 118 (.leaf 707312136) (.leaf 697356392)) (.branch 120 (.leaf 687550710) (.leaf 677892417)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 97).prefactor = (980010141136097/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 97).cutoff/(generalMeanRows 97).c)).2 =
    (229689707769229/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 97).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 97).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 97).q*(generalMeanRows 97).c/2-2 = (43/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable048.value]
    have hcontinuation : (generalMeanRows 97).q*(generalMeanRows 97).cutoff/2-2 = (236/117:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable059.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 97).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 97

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 97).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 97).criticalRate j.val*(generalMeanRows 97).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 97).c*(generalMeanRows 97).criticalPoint j.val)).2-
      (generalMeanRows 97).J/2-(generalMeanRows 97).error (generalMeanGrid j.val)+
      (generalMeanRows 97).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 97).c)).2-
      (generalMeanRows 97).J/2-(generalMeanRows 97).error 4 := by
  have he : (generalMeanRows 97).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 97) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 97)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0097

/-! Kernel-checked entropy margins for general spectral rectangle 98. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0098
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6153631387) (.branch 2 (.leaf 5959562162) (.leaf 5774285361))) (.branch 5 (.branch 4 (.leaf 5597289806) (.leaf 5428100584)) (.branch 6 (.leaf 5266275877) (.leaf 5111404142)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4963101587) (.leaf 4821009907)) (.branch 10 (.leaf 4684794242) (.leaf 4554141343))) (.branch 13 (.branch 12 (.leaf 4428757901) (.leaf 4308369048)) (.branch 14 (.leaf 4192716978) (.leaf 4081559704))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3974669919) (.branch 17 (.leaf 3871833953) (.leaf 3772850822))) (.branch 20 (.branch 19 (.leaf 3677531353) (.leaf 3585697380)) (.branch 21 (.leaf 3497181004) (.leaf 3411823917)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3329476768) (.leaf 3249998583)) (.branch 25 (.leaf 3173256232) (.leaf 3099123927))) (.branch 28 (.branch 27 (.leaf 3027482764) (.leaf 2958220294)) (.branch 29 (.leaf 2891230124) (.leaf 2826411549)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2763669210) (.branch 32 (.leaf 2702912767) (.leaf 2644056608))) (.branch 35 (.branch 34 (.leaf 2587019563) (.leaf 2531724648)) (.branch 36 (.leaf 2478098823) (.leaf 2426072758)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2375580628) (.leaf 2326559908)) (.branch 40 (.leaf 2278951190) (.leaf 2232698005))) (.branch 43 (.branch 42 (.leaf 2187746661) (.leaf 2144046088)) (.branch 44 (.leaf 2101547695) (.leaf 2060205231))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2019974662) (.branch 47 (.leaf 1980814046) (.leaf 1942683424))) (.branch 50 (.branch 49 (.leaf 1905544712) (.leaf 1869361604)) (.branch 51 (.leaf 1834099470) (.leaf 1799725279)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1766207505) (.leaf 1733516054)) (.branch 55 (.leaf 1701622190) (.leaf 1670498459))) (.branch 58 (.branch 57 (.leaf 1640118631) (.leaf 1610457632)) (.branch 59 (.leaf 1581491488) (.leaf 1553197266))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1525553026) (.branch 62 (.leaf 1498537766) (.leaf 1472131382))) (.branch 65 (.branch 64 (.leaf 1446314615) (.leaf 1421069018)) (.branch 66 (.leaf 1396376908) (.leaf 1372221334)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1348586039) (.leaf 1325455429)) (.branch 70 (.leaf 1302814537) (.leaf 1280648994))) (.branch 73 (.branch 72 (.leaf 1258945004) (.leaf 1237689313)) (.branch 74 (.leaf 1216869184) (.leaf 1196472374))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1176487108) (.branch 77 (.leaf 1156902063) (.leaf 1137706339))) (.branch 80 (.branch 79 (.leaf 1118889447) (.leaf 1100441285)) (.branch 81 (.leaf 1082352123) (.leaf 1064612587)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1047213638) (.leaf 1030146563)) (.branch 85 (.leaf 1013402957) (.leaf 996974709))) (.branch 88 (.branch 87 (.leaf 980853993) (.leaf 965033249)) (.branch 89 (.leaf 949505177) (.leaf 934262725)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 919299075) (.branch 92 (.leaf 904607636) (.leaf 890182034))) (.branch 95 (.branch 94 (.leaf 876016100) (.leaf 862103866)) (.branch 96 (.leaf 848439554) (.leaf 835017567)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 821832485) (.leaf 808879054)) (.branch 100 (.leaf 796152181) (.leaf 783646928))) (.branch 103 (.branch 102 (.leaf 771358506) (.leaf 759282268)) (.branch 104 (.leaf 747413701) (.leaf 735748428))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 724282196) (.leaf 713010872)) (.branch 108 (.leaf 701930441) (.leaf 691037002))) (.branch 111 (.branch 110 (.leaf 680326760) (.leaf 669796024)) (.branch 112 (.leaf 659441204) (.leaf 649258807)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 639245432) (.leaf 629397766)) (.branch 116 (.leaf 619712587) (.leaf 610186752))) (.branch 119 (.branch 118 (.leaf 600817200) (.leaf 591600947)) (.branch 120 (.leaf 582535085) (.leaf 573616778)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 98).prefactor = (158293851765321/31250000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 98).cutoff/(generalMeanRows 98).c)).2 =
    (109966650328719/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 98).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 98).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 98).q*(generalMeanRows 98).c/2-2 = (47/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable034.value]
    have hcontinuation : (generalMeanRows 98).q*(generalMeanRows 98).cutoff/2-2 = (236/117:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable059.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 98).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 98

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 98).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 98).criticalRate j.val*(generalMeanRows 98).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 98).c*(generalMeanRows 98).criticalPoint j.val)).2-
      (generalMeanRows 98).J/2-(generalMeanRows 98).error (generalMeanGrid j.val)+
      (generalMeanRows 98).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 98).c)).2-
      (generalMeanRows 98).J/2-(generalMeanRows 98).error 4 := by
  have he : (generalMeanRows 98).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 98) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 98)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0098

/-! Kernel-checked entropy margins for general spectral rectangle 99. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0099
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5591921152) (.branch 2 (.leaf 5394115000) (.leaf 5205436766))) (.branch 5 (.branch 4 (.leaf 5025360015) (.leaf 4853395494)) (.branch 6 (.leaf 4689087886) (.leaf 4532012918)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4381774766) (.leaf 4238003741)) (.branch 10 (.leaf 4100354188) (.leaf 3968502613))) (.branch 13 (.branch 12 (.leaf 3842145967) (.leaf 3721000110)) (.branch 14 (.leaf 3604798400) (.leaf 3493290417))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3386240798) (.branch 17 (.leaf 3283428172) (.leaf 3184644181))) (.branch 20 (.branch 19 (.leaf 3089692587) (.leaf 2998388450)) (.branch 21 (.leaf 2910557371) (.leaf 2826034795)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2744665371) (.leaf 2666302352)) (.branch 25 (.leaf 2590807052) (.leaf 2518048333))) (.branch 28 (.branch 27 (.leaf 2447902138) (.leaf 2380251046)) (.branch 29 (.leaf 2314983874) (.leaf 2251995291)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2191185474) (.branch 32 (.leaf 2132459773) (.leaf 2075728409))) (.branch 35 (.branch 34 (.leaf 2020906190) (.leaf 1967912242)) (.branch 36 (.leaf 1916669762) (.leaf 1867105783)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1819150962) (.leaf 1772739366)) (.branch 40 (.leaf 1727808294) (.leaf 1684298085))) (.branch 43 (.branch 42 (.leaf 1642151960) (.leaf 1601315859)) (.branch 44 (.leaf 1561738295) (.leaf 1523370213))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1486164862) (.branch 47 (.leaf 1450077671) (.leaf 1415066131))) (.branch 50 (.branch 49 (.leaf 1381089691) (.leaf 1348109650)) (.branch 51 (.leaf 1316089065) (.leaf 1284992657)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1254786728) (.leaf 1225439076)) (.branch 55 (.leaf 1196918922) (.leaf 1169196837))) (.branch 58 (.branch 57 (.leaf 1142244676) (.leaf 1116035509)) (.branch 59 (.leaf 1090543564) (.leaf 1065744169))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1041613698) (.branch 62 (.leaf 1018129518) (.leaf 995269942))) (.branch 65 (.branch 64 (.leaf 973014185) (.leaf 951342316)) (.branch 66 (.leaf 930235220) (.leaf 909674559)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 889642734) (.leaf 870122852)) (.branch 70 (.leaf 851098690) (.leaf 832554666))) (.branch 73 (.branch 72 (.leaf 814475808) (.leaf 796847728)) (.branch 74 (.leaf 779656591) (.leaf 762889093))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 746532437) (.branch 77 (.leaf 730574309) (.leaf 715002855))) (.branch 80 (.branch 79 (.leaf 699806663) (.leaf 684974742)) (.branch 81 (.leaf 670496504) (.leaf 656361746)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 642560631) (.leaf 629083677)) (.branch 85 (.leaf 615921739) (.leaf 603065991))) (.branch 88 (.branch 87 (.leaf 590507919) (.leaf 578239303)) (.branch 89 (.leaf 566252208) (.leaf 554538968)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 543092179) (.branch 92 (.leaf 531904684) (.leaf 520969567))) (.branch 95 (.branch 94 (.leaf 510280141) (.leaf 499829938)) (.branch 96 (.leaf 489612702) (.leaf 479622379)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 469853109) (.leaf 460299220)) (.branch 100 (.leaf 450955220) (.leaf 441815787))) (.branch 103 (.branch 102 (.leaf 432875766) (.leaf 424130164)) (.branch 104 (.leaf 415574137) (.leaf 407202991))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 399012174) (.leaf 390997270)) (.branch 108 (.leaf 383153994) (.leaf 375478189))) (.branch 111 (.branch 110 (.leaf 367965818) (.leaf 360612965)) (.branch 112 (.leaf 353415823) (.leaf 346370698)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 339474000) (.leaf 332722239)) (.branch 116 (.leaf 326112025) (.leaf 319640063))) (.branch 119 (.branch 118 (.leaf 313303148) (.leaf 307098164)) (.branch 120 (.leaf 301022079) (.leaf 295071946)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 99).prefactor = (523633564059191/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 99).cutoff/(generalMeanRows 99).c)).2 =
    (374422693062493/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 99).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 99).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 99).q*(generalMeanRows 99).cutoff/2-2 = (236/117:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable059.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 99).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 99

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 99).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 99).criticalRate j.val*(generalMeanRows 99).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 99).c*(generalMeanRows 99).criticalPoint j.val)).2-
      (generalMeanRows 99).J/2-(generalMeanRows 99).error (generalMeanGrid j.val)+
      (generalMeanRows 99).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 99).c)).2-
      (generalMeanRows 99).J/2-(generalMeanRows 99).error 4 := by
  have he : (generalMeanRows 99).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 99) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 99)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0099

/-! Kernel-checked entropy margins for general spectral rectangle 100. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0100
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5757767131) (.branch 2 (.leaf 5577451869) (.leaf 5405386830))) (.branch 5 (.branch 4 (.leaf 5241083344) (.leaf 5084087829)) (.branch 6 (.leaf 4933978728) (.leaf 4790363778)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4652877563) (.leaf 4521179317)) (.branch 10 (.leaf 4394950945) (.leaf 4273895236))) (.branch 13 (.branch 12 (.leaf 4157734243) (.leaf 4046207822)) (.branch 14 (.leaf 3939072289) (.leaf 3836099212))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3737074301) (.branch 17 (.leaf 3641796391) (.leaf 3550076514))) (.branch 20 (.branch 19 (.leaf 3461737053) (.leaf 3376610949)) (.branch 21 (.leaf 3294540993) (.leaf 3215379153)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3138985967) (.leaf 3065229978)) (.branch 25 (.leaf 2993987211) (.leaf 2925140689))) (.branch 28 (.branch 27 (.leaf 2858579985) (.leaf 2794200809)) (.branch 29 (.leaf 2731904617) (.leaf 2671598260)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2613193643) (.branch 32 (.leaf 2556607421) (.leaf 2501760706))) (.branch 35 (.branch 34 (.leaf 2448578801) (.leaf 2396990946)) (.branch 36 (.leaf 2346930083) (.leaf 2298332642)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2251138332) (.leaf 2205289948)) (.branch 40 (.leaf 2160733197) (.leaf 2117416529))) (.branch 43 (.branch 42 (.leaf 2075290977) (.leaf 2034310012)) (.branch 44 (.leaf 1994429406) (.leaf 1955607102))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1917803089) (.branch 47 (.leaf 1880979295) (.leaf 1845099475))) (.branch 50 (.branch 49 (.leaf 1810129111) (.leaf 1776035319)) (.branch 51 (.leaf 1742786759) (.leaf 1710353552)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1678707200) (.leaf 1647820515)) (.branch 55 (.leaf 1617667545) (.leaf 1588223514))) (.branch 58 (.branch 57 (.leaf 1559464753) (.leaf 1531368650)) (.branch 59 (.leaf 1503913586) (.leaf 1477078893))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1450844796) (.branch 62 (.leaf 1425192373) (.leaf 1400103510))) (.branch 65 (.branch 64 (.leaf 1375560857) (.leaf 1351547795)) (.branch 66 (.leaf 1328048393) (.leaf 1305047380)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1282530105) (.leaf 1260482512)) (.branch 70 (.leaf 1238891110) (.leaf 1217742942))) (.branch 73 (.branch 72 (.leaf 1197025562) (.leaf 1176727009)) (.branch 74 (.leaf 1156835784) (.leaf 1137340830))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1118231505) (.branch 77 (.leaf 1099497570) (.leaf 1081129164))) (.branch 80 (.branch 79 (.leaf 1063116789) (.leaf 1045451294)) (.branch 81 (.leaf 1028123857) (.leaf 1011125970)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 994449427) (.leaf 978086306)) (.branch 85 (.leaf 962028962) (.leaf 946270010))) (.branch 88 (.branch 87 (.leaf 930802315) (.leaf 915618981)) (.branch 89 (.leaf 900713341) (.leaf 886078947)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 871709558) (.branch 92 (.leaf 857599136) (.leaf 843741832))) (.branch 95 (.branch 94 (.leaf 830131984) (.leaf 816764102)) (.branch 96 (.leaf 803632868) (.leaf 790733123)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 778059866) (.leaf 765608241)) (.branch 100 (.leaf 753373539) (.leaf 741351184))) (.branch 103 (.branch 102 (.leaf 729536735) (.leaf 717925875)) (.branch 104 (.leaf 706514412) (.leaf 695298266))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 684273473) (.leaf 673436177)) (.branch 108 (.leaf 662782625) (.leaf 652309164))) (.branch 111 (.branch 110 (.leaf 642012239) (.leaf 631888387)) (.branch 112 (.leaf 621934234) (.leaf 612146495)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 602521966) (.leaf 593057524)) (.branch 116 (.leaf 583750124) (.leaf 574596796))) (.branch 119 (.branch 118 (.leaf 565594642) (.leaf 556740835)) (.branch 120 (.leaf 548032614) (.leaf 539467286)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 100).prefactor = (98014434520351/20000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 100).cutoff/(generalMeanRows 100).c)).2 =
    (230840456263367/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 100).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 100).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 100).q*(generalMeanRows 100).c/2-2 = (151/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable060.value]
    have hcontinuation : (generalMeanRows 100).q*(generalMeanRows 100).cutoff/2-2 = (194/91:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable061.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 100).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 100

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 100).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 100).criticalRate j.val*(generalMeanRows 100).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 100).c*(generalMeanRows 100).criticalPoint j.val)).2-
      (generalMeanRows 100).J/2-(generalMeanRows 100).error (generalMeanGrid j.val)+
      (generalMeanRows 100).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 100).c)).2-
      (generalMeanRows 100).J/2-(generalMeanRows 100).error 4 := by
  have he : (generalMeanRows 100).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 100) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 100)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0100

/-! Kernel-checked entropy margins for general spectral rectangle 101. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0101
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5306312027) (.branch 2 (.leaf 5122559524) (.leaf 4947348238))) (.branch 5 (.branch 4 (.leaf 4780176281) (.leaf 4620577644)) (.branch 6 (.leaf 4468119066) (.leaf 4322397243)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4183036325) (.leaf 4049685667)) (.branch 10 (.leaf 3922017810) (.leaf 3799726652))) (.branch 13 (.branch 12 (.leaf 3682525795) (.leaf 3570147046)) (.branch 14 (.leaf 3462339054) (.leaf 3358866070))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3259506812) (.branch 17 (.leaf 3164053432) (.leaf 3072310567))) (.branch 20 (.branch 19 (.leaf 2984094469) (.leaf 2899232207)) (.branch 21 (.leaf 2817560930) (.leaf 2738927194)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2663186335) (.leaf 2590201892)) (.branch 25 (.leaf 2519845076) (.leaf 2451994277))) (.branch 28 (.branch 27 (.leaf 2386534602) (.leaf 2323357460)) (.branch 29 (.leaf 2262360158) (.leaf 2203445545)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2146521665) (.branch 32 (.leaf 2091501444) (.leaf 2038302394))) (.branch 35 (.branch 34 (.leaf 1986846339) (.leaf 1937059157)) (.branch 36 (.leaf 1888870543) (.leaf 1842213784)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1797025550) (.leaf 1753245700)) (.branch 40 (.leaf 1710817097) (.leaf 1669685438))) (.branch 43 (.branch 42 (.leaf 1629799094) (.leaf 1591108959)) (.branch 44 (.leaf 1553568310) (.leaf 1517132674))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1481759701) (.branch 47 (.leaf 1447409055) (.leaf 1414042296))) (.branch 50 (.branch 49 (.leaf 1381622783) (.leaf 1350115574)) (.branch 51 (.leaf 1319487336) (.leaf 1289706261)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1260741982) (.leaf 1232565500)) (.branch 55 (.leaf 1205149111) (.leaf 1178466338))) (.branch 58 (.branch 57 (.leaf 1152491871) (.leaf 1127201503)) (.branch 59 (.leaf 1102572075) (.leaf 1078581423))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1055208328) (.branch 62 (.leaf 1032432468) (.leaf 1010234374))) (.branch 65 (.branch 64 (.leaf 988595386) (.leaf 967497613)) (.branch 66 (.leaf 946923899) (.leaf 926857781)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 907283461) (.leaf 888185772)) (.branch 70 (.leaf 869550144) (.leaf 851362583))) (.branch 73 (.branch 72 (.leaf 833609637) (.leaf 816278374)) (.branch 74 (.leaf 799356355) (.leaf 782831616))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 766692640) (.branch 77 (.leaf 750928340) (.leaf 735528039))) (.branch 80 (.branch 79 (.leaf 720481451) (.leaf 705778662)) (.branch 81 (.leaf 691410118) (.leaf 677366603)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 663639227) (.leaf 650219413)) (.branch 85 (.leaf 637098880) (.leaf 624269633))) (.branch 88 (.branch 87 (.leaf 611723951) (.leaf 599454372)) (.branch 89 (.leaf 587453685) (.leaf 575714918)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 564231330) (.branch 92 (.leaf 552996399) (.leaf 542003813))) (.branch 95 (.branch 94 (.leaf 531247464) (.leaf 520721438)) (.branch 96 (.leaf 510420006) (.leaf 500337619)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 490468900) (.leaf 480808636)) (.branch 100 (.leaf 471351774) (.leaf 462093411))) (.branch 103 (.branch 102 (.leaf 453028794) (.leaf 444153308)) (.branch 104 (.leaf 435462475) (.leaf 426951949))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 418617507) (.leaf 410455049)) (.branch 108 (.leaf 402460591) (.leaf 394630262))) (.branch 111 (.branch 110 (.leaf 386960299) (.leaf 379447043)) (.branch 112 (.leaf 372086937) (.leaf 364876521)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 357812427) (.leaf 350891382)) (.branch 116 (.leaf 344110195) (.leaf 337465765))) (.branch 119 (.branch 118 (.leaf 330955070) (.leaf 324575166)) (.branch 120 (.leaf 318323188) (.leaf 312196344)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 101).prefactor = (2524007575905689/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 101).cutoff/(generalMeanRows 101).c)).2 =
    (407856262512957/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 101).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 101).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 101).q*(generalMeanRows 101).c/2-2 = (187/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable062.value]
    have hcontinuation : (generalMeanRows 101).q*(generalMeanRows 101).cutoff/2-2 = (194/91:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable061.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 101).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 101

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 101).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 101).criticalRate j.val*(generalMeanRows 101).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 101).c*(generalMeanRows 101).criticalPoint j.val)).2-
      (generalMeanRows 101).J/2-(generalMeanRows 101).error (generalMeanGrid j.val)+
      (generalMeanRows 101).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 101).c)).2-
      (generalMeanRows 101).J/2-(generalMeanRows 101).error 4 := by
  have he : (generalMeanRows 101).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 101) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 101)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0101

/-! Kernel-checked entropy margins for general spectral rectangle 102. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0102
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4826904745) (.branch 2 (.leaf 4642055023) (.leaf 4466031761))) (.branch 5 (.branch 4 (.leaf 4298318053) (.leaf 4138433752)) (.branch 6 (.leaf 3985932275) (.leaf 3840397740)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3701442406) (.leaf 3568704373)) (.branch 10 (.leaf 3441845513) (.leaf 3320549600))) (.branch 13 (.branch 12 (.leaf 3204520619) (.leaf 3093481235)) (.branch 14 (.leaf 2987171392) (.leaf 2885347051))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2787779028) (.branch 17 (.leaf 2694251934) (.leaf 2604563207))) (.branch 20 (.branch 19 (.leaf 2518522221) (.leaf 2435949472)) (.branch 21 (.leaf 2356675823) (.leaf 2280541813)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2207397019) (.leaf 2137099465)) (.branch 25 (.leaf 2069515080) (.leaf 2004517187))) (.branch 28 (.branch 27 (.leaf 1941986042) (.leaf 1881808396)) (.branch 29 (.leaf 1823877094) (.leaf 1768090701)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1714353152) (.branch 32 (.leaf 1662573429) (.leaf 1612665259))) (.branch 35 (.branch 34 (.leaf 1564546832) (.leaf 1518140541)) (.branch 36 (.leaf 1473372732) (.leaf 1430173477)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1388476363) (.leaf 1348218285)) (.branch 40 (.leaf 1309339263) (.leaf 1271782266))) (.branch 43 (.branch 42 (.leaf 1235493045) (.leaf 1200419981)) (.branch 44 (.leaf 1166513936) (.leaf 1133728124))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1102017975) (.branch 47 (.leaf 1071341022) (.leaf 1041656783))) (.branch 50 (.branch 49 (.leaf 1012926660) (.leaf 985113834)) (.branch 51 (.leaf 958183174) (.leaf 932101148)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 906835740) (.leaf 882356371)) (.branch 55 (.leaf 858633826) (.leaf 835640183))) (.branch 58 (.branch 57 (.leaf 813348747) (.leaf 791733990)) (.branch 59 (.leaf 770771490) (.leaf 750437879))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 730710785) (.branch 62 (.leaf 711568789) (.leaf 692991375))) (.branch 65 (.branch 64 (.leaf 674958884) (.leaf 657452479)) (.branch 66 (.leaf 640454098) (.leaf 623946421)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 607912832) (.leaf 592337391)) (.branch 70 (.leaf 577204794) (.leaf 562500350))) (.branch 73 (.branch 72 (.leaf 548209949) (.leaf 534320037)) (.branch 74 (.leaf 520817589) (.leaf 507690084))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 494925485) (.branch 77 (.leaf 482512216) (.leaf 470439139))) (.branch 80 (.branch 79 (.leaf 458695536) (.leaf 447271092)) (.branch 81 (.leaf 436155875) (.leaf 425340319)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 414815212) (.leaf 404571674)) (.branch 85 (.leaf 394601149) (.leaf 384895386))) (.branch 88 (.branch 87 (.leaf 375446431) (.leaf 366246611)) (.branch 89 (.leaf 357288523) (.leaf 348565022)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 340069213) (.branch 92 (.leaf 331794439) (.leaf 323734268))) (.branch 95 (.branch 94 (.leaf 315882491) (.leaf 308233107)) (.branch 96 (.leaf 300780317) (.leaf 293518515)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 286442282) (.leaf 279546378)) (.branch 100 (.leaf 272825732) (.leaf 266275441))) (.branch 103 (.branch 102 (.leaf 259890759) (.leaf 253667093)) (.branch 104 (.leaf 247599996) (.leaf 241685164))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 235918426) (.leaf 230295745)) (.branch 108 (.leaf 224813207) (.leaf 219467021))) (.branch 111 (.branch 110 (.leaf 214253513) (.leaf 209169121)) (.branch 112 (.leaf 204210391) (.leaf 199373974)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 194656623) (.leaf 190055186)) (.branch 116 (.leaf 185566609) (.leaf 181187923))) (.branch 119 (.branch 118 (.leaf 176916251) (.leaf 172748799)) (.branch 120 (.leaf 168682854) (.leaf 164715783)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 102).prefactor = (1039947109734179/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 102).cutoff/(generalMeanRows 102).c)).2 =
    (174258411363323/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 102).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 102).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 102).q*(generalMeanRows 102).c/2-2 = (229/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable063.value]
    have hcontinuation : (generalMeanRows 102).q*(generalMeanRows 102).cutoff/2-2 = (194/91:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable061.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 102).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 102

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 102).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 102).criticalRate j.val*(generalMeanRows 102).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 102).c*(generalMeanRows 102).criticalPoint j.val)).2-
      (generalMeanRows 102).J/2-(generalMeanRows 102).error (generalMeanGrid j.val)+
      (generalMeanRows 102).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 102).c)).2-
      (generalMeanRows 102).J/2-(generalMeanRows 102).error 4 := by
  have he : (generalMeanRows 102).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 102) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 102)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0102

/-! Kernel-checked entropy margins for general spectral rectangle 103. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0103
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5384369294) (.branch 2 (.leaf 5214478051) (.leaf 5052438064))) (.branch 5 (.branch 4 (.leaf 4897775555) (.leaf 4750051271)) (.branch 6 (.leaf 4608857464) (.leaf 4473815193)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4344571907) (.leaf 4220799272)) (.branch 10 (.leaf 4102191212) (.leaf 3988462136))) (.branch 13 (.branch 12 (.leaf 3879345341) (.leaf 3774591556)) (.branch 14 (.leaf 3673967617) (.leaf 3577255269))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3484250060) (.branch 17 (.leaf 3394760340) (.leaf 3308606341))) (.branch 20 (.branch 19 (.leaf 3225619333) (.leaf 3145640847)) (.branch 21 (.leaf 3068521969) (.leaf 2994122676)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2922311237) (.leaf 2852963654)) (.branch 25 (.leaf 2785963146) (.leaf 2721199673))) (.branch 28 (.branch 27 (.leaf 2658569493) (.leaf 2597974757)) (.branch 29 (.leaf 2539323124) (.leaf 2482527418)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2427505290) (.branch 32 (.leaf 2374178926) (.leaf 2322474755))) (.branch 35 (.branch 34 (.leaf 2272323190) (.leaf 2223658383)) (.branch 36 (.leaf 2176417999) (.leaf 2130542995)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2085977431) (.leaf 2042668279)) (.branch 40 (.leaf 2000565249) (.leaf 1959620631))) (.branch 43 (.branch 42 (.leaf 1919789140) (.leaf 1881027775)) (.branch 44 (.leaf 1843295688) (.leaf 1806554058))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1770765976) (.branch 47 (.leaf 1735896334) (.leaf 1701911725))) (.branch 50 (.branch 49 (.leaf 1668780346) (.leaf 1636471908)) (.branch 51 (.leaf 1604957552) (.leaf 1574209769)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1544202325) (.leaf 1514910196)) (.branch 55 (.leaf 1486309494) (.leaf 1458377411))) (.branch 58 (.branch 57 (.leaf 1431092162) (.leaf 1404432923)) (.branch 59 (.leaf 1378379788) (.leaf 1352913716))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1328016486) (.branch 62 (.leaf 1303670655) (.leaf 1279859515))) (.branch 65 (.branch 64 (.leaf 1256567060) (.leaf 1233777945)) (.branch 66 (.leaf 1211477454) (.leaf 1189651468)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1168286436) (.leaf 1147369345)) (.branch 70 (.leaf 1126887695) (.leaf 1106829469))) (.branch 73 (.branch 72 (.leaf 1087183117) (.leaf 1067937526)) (.branch 74 (.leaf 1049082003) (.leaf 1030606252))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1012500358) (.branch 77 (.leaf 994754767) (.leaf 977360269))) (.branch 80 (.branch 79 (.leaf 960307983) (.leaf 943589339)) (.branch 81 (.leaf 927196069) (.leaf 911120187)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 895353980) (.leaf 879889995)) (.branch 85 (.leaf 864721028) (.leaf 849840111))) (.branch 88 (.branch 87 (.leaf 835240502) (.leaf 820915677)) (.branch 89 (.leaf 806859321) (.leaf 793065315)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 779527731) (.branch 92 (.leaf 766240825) (.leaf 753199025))) (.branch 95 (.branch 94 (.leaf 740396928) (.leaf 727829290)) (.branch 96 (.leaf 715491024) (.leaf 703377188)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 691482984) (.leaf 679803749)) (.branch 100 (.leaf 668334950) (.leaf 657072184))) (.branch 103 (.branch 102 (.leaf 646011165) (.leaf 635147726)) (.branch 104 (.leaf 624477811) (.leaf 613997473))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 603702869) (.leaf 593590255)) (.branch 108 (.leaf 583655986) (.leaf 573896508))) (.branch 111 (.branch 110 (.leaf 564308358) (.leaf 554888160)) (.branch 112 (.leaf 545632622) (.leaf 536538532)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 527602758) (.leaf 518822242)) (.branch 116 (.leaf 510193999) (.leaf 501715116))) (.branch 119 (.branch 118 (.leaf 493382748) (.leaf 485194117)) (.branch 120 (.leaf 477146507) (.leaf 469237267)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 103).prefactor = (4826666109475081/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 103).cutoff/(generalMeanRows 103).c)).2 =
    (477606929297723/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 103).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 103).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 103).q*(generalMeanRows 103).c/2-2 = (129/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable064.value]
    have hcontinuation : (generalMeanRows 103).q*(generalMeanRows 103).cutoff/2-2 = (1148/507:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable065.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 103).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 103

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 103).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 103).criticalRate j.val*(generalMeanRows 103).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 103).c*(generalMeanRows 103).criticalPoint j.val)).2-
      (generalMeanRows 103).J/2-(generalMeanRows 103).error (generalMeanGrid j.val)+
      (generalMeanRows 103).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 103).c)).2-
      (generalMeanRows 103).J/2-(generalMeanRows 103).error 4 := by
  have he : (generalMeanRows 103).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 103) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 103)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0103

/-! Kernel-checked entropy margins for general spectral rectangle 104. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0104
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5325466959) (.branch 2 (.leaf 5151539047) (.leaf 4985690455))) (.branch 5 (.branch 4 (.leaf 4827435182) (.leaf 4676322579)) (.branch 6 (.leaf 4531934263) (.leaf 4393881353)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4261801993) (.leaf 4135359129)) (.branch 10 (.leaf 4014238500) (.leaf 3898146829))) (.branch 13 (.branch 12 (.leaf 3786810182) (.leaf 3679972477)) (.branch 14 (.leaf 3577394134) (.leaf 3478850842))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3384132430) (.branch 17 (.leaf 3293041843) (.leaf 3205394199))) (.branch 20 (.branch 19 (.leaf 3121015924) (.leaf 3039743961)) (.branch 21 (.leaf 2961425040) (.leaf 2885915010)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2813078214) (.leaf 2742786924)) (.branch 25 (.leaf 2674920809) (.leaf 2609366454))) (.branch 28 (.branch 27 (.leaf 2546016899) (.leaf 2484771229)) (.branch 29 (.leaf 2425534183) (.leaf 2368215791)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2312731046) (.branch 32 (.leaf 2258999587) (.leaf 2206945414))) (.branch 35 (.branch 34 (.leaf 2156496617) (.leaf 2107585123)) (.branch 36 (.leaf 2060146468) (.leaf 2014119575)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1969446549) (.leaf 1926072493)) (.branch 40 (.leaf 1883945323) (.leaf 1843015609))) (.branch 43 (.branch 42 (.leaf 1803236416) (.leaf 1764563159)) (.branch 44 (.leaf 1726953469) (.leaf 1690367063))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1654765630) (.branch 47 (.leaf 1620112711) (.leaf 1586373603))) (.branch 50 (.branch 49 (.leaf 1553515254) (.leaf 1521506177)) (.branch 51 (.leaf 1490316357) (.leaf 1459917174)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1430281325) (.leaf 1401382753)) (.branch 55 (.leaf 1373196580) (.leaf 1345699042))) (.branch 58 (.branch 57 (.leaf 1318867431) (.leaf 1292680038)) (.branch 59 (.leaf 1267116099) (.leaf 1242155749))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1217779971) (.branch 62 (.leaf 1193970555) (.leaf 1170710054))) (.branch 65 (.branch 64 (.leaf 1147981747) (.leaf 1125769601)) (.branch 66 (.leaf 1104058236) (.leaf 1082832892)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1062079398) (.leaf 1041784146)) (.branch 70 (.leaf 1021934057) (.leaf 1002516561))) (.branch 73 (.branch 72 (.leaf 983519569) (.leaf 964931449)) (.branch 74 (.leaf 946741009) (.leaf 928937470))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 911510449) (.branch 77 (.leaf 894449944) (.leaf 877746308))) (.branch 80 (.branch 79 (.leaf 861390241) (.leaf 845372769)) (.branch 81 (.leaf 829685231) (.leaf 814319265)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 799266793) (.leaf 784520010)) (.branch 85 (.leaf 770071373) (.leaf 755913584))) (.branch 88 (.branch 87 (.leaf 742039588) (.leaf 728442555)) (.branch 89 (.leaf 715115874) (.leaf 702053143)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 689248161) (.branch 92 (.leaf 676694917) (.leaf 664387587))) (.branch 95 (.branch 94 (.leaf 652320520) (.leaf 640488238)) (.branch 96 (.leaf 628885424) (.leaf 617506916)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 606347703) (.leaf 595402920)) (.branch 100 (.leaf 584667837) (.leaf 574137860))) (.branch 103 (.branch 102 (.leaf 563808523) (.leaf 553675483)) (.branch 104 (.leaf 543734515) (.leaf 533981511))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 524412470) (.leaf 515023501)) (.branch 108 (.leaf 505810812) (.leaf 496770714))) (.branch 111 (.branch 110 (.leaf 487899609) (.leaf 479193996)) (.branch 112 (.leaf 470650459) (.leaf 462265669)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 454036383) (.leaf 445959436)) (.branch 116 (.leaf 438031739) (.leaf 430250282))) (.branch 119 (.branch 118 (.leaf 422612127) (.leaf 415114403)) (.branch 120 (.leaf 407754312) (.leaf 400529119)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 104).prefactor = (4955627105637763/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 104).cutoff/(generalMeanRows 104).c)).2 =
    (230182561431609/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 104).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 104).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 104).q*(generalMeanRows 104).c/2-2 = (691/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable054.value]
    have hcontinuation : (generalMeanRows 104).q*(generalMeanRows 104).cutoff/2-2 = (1148/507:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable065.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 104).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 104

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 104).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 104).criticalRate j.val*(generalMeanRows 104).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 104).c*(generalMeanRows 104).criticalPoint j.val)).2-
      (generalMeanRows 104).J/2-(generalMeanRows 104).error (generalMeanGrid j.val)+
      (generalMeanRows 104).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 104).c)).2-
      (generalMeanRows 104).J/2-(generalMeanRows 104).error 4 := by
  have he : (generalMeanRows 104).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 104) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 104)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0104

/-! Kernel-checked entropy margins for general spectral rectangle 105. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0105
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5570584508) (.branch 2 (.leaf 5391725723) (.leaf 5221152903))) (.branch 5 (.branch 4 (.leaf 5058366859) (.leaf 4902904745)) (.branch 6 (.leaf 4754336887) (.leaf 4612263934)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4476314322) (.leaf 4346141978)) (.branch 10 (.leaf 4221424263) (.leaf 4101860106))) (.branch 13 (.branch 12 (.leaf 3987168321) (.leaf 3877086072)) (.branch 14 (.leaf 3771367485) (.leaf 3669782381))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3572115114) (.branch 17 (.leaf 3478163519) (.leaf 3387737942))) (.branch 20 (.branch 19 (.leaf 3300660351) (.leaf 3216763521)) (.branch 21 (.leaf 3135890286) (.leaf 3057892847)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2982632138) (.leaf 2909977236)) (.branch 25 (.leaf 2839804819) (.leaf 2771998668))) (.branch 28 (.branch 27 (.leaf 2706449199) (.leaf 2643053033)) (.branch 29 (.leaf 2581712600) (.leaf 2522335766)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2464835490) (.branch 32 (.leaf 2409129503) (.leaf 2355140014))) (.branch 35 (.branch 34 (.leaf 2302793429) (.leaf 2252020099)) (.branch 36 (.leaf 2202754070) (.leaf 2154932871)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2108497294) (.leaf 2063391205)) (.branch 40 (.leaf 2019561361) (.leaf 1976957236))) (.branch 43 (.branch 42 (.leaf 1935530865) (.leaf 1895236694)) (.branch 44 (.leaf 1856031441) (.leaf 1817873961))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1780725130) (.branch 47 (.leaf 1744547725) (.leaf 1709306319))) (.branch 50 (.branch 49 (.leaf 1674967181) (.leaf 1641498175)) (.branch 51 (.leaf 1608868682) (.leaf 1577049504)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1546012796) (.leaf 1515731987)) (.branch 55 (.leaf 1486181711) (.leaf 1457337744))) (.branch 58 (.branch 57 (.leaf 1429176940) (.leaf 1401677177)) (.branch 59 (.leaf 1374817298) (.leaf 1348577065))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1322937107) (.branch 62 (.leaf 1297878878) (.leaf 1273384610))) (.branch 65 (.branch 64 (.leaf 1249437279) (.leaf 1226020561)) (.branch 66 (.leaf 1203118799) (.leaf 1180716971)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1158800654) (.leaf 1137355998)) (.branch 70 (.leaf 1116369697) (.leaf 1095828958))) (.branch 73 (.branch 72 (.leaf 1075721483) (.leaf 1056035439)) (.branch 74 (.leaf 1036759439) (.leaf 1017882518))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 999394115) (.branch 77 (.leaf 981284054) (.leaf 963542525))) (.branch 80 (.branch 79 (.leaf 946160067) (.leaf 929127551)) (.branch 81 (.leaf 912436169) (.leaf 896077413)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 880043067) (.leaf 864325191)) (.branch 85 (.leaf 848916110) (.leaf 833808401))) (.branch 88 (.branch 87 (.leaf 818994884) (.leaf 804468609)) (.branch 89 (.leaf 790222849) (.leaf 776251087)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 762547012) (.branch 92 (.leaf 749104505) (.leaf 735917635))) (.branch 95 (.branch 94 (.leaf 722980649) (.leaf 710287966)) (.branch 96 (.leaf 697834171) (.leaf 685614004)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 673622360) (.leaf 661854279)) (.branch 100 (.leaf 650304940) (.leaf 638969658))) (.branch 103 (.branch 102 (.leaf 627843879) (.leaf 616923172)) (.branch 104 (.leaf 606203226) (.leaf 595679848))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 585348954) (.leaf 575206569)) (.branch 108 (.leaf 565248822) (.leaf 555471941))) (.branch 111 (.branch 110 (.leaf 545872251) (.leaf 536446169)) (.branch 112 (.leaf 527190206) (.leaf 518100954)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 509175094) (.leaf 500409385)) (.branch 116 (.leaf 491800666) (.leaf 483345852))) (.branch 119 (.branch 118 (.leaf 475041931) (.leaf 466885962)) (.branch 120 (.leaf 458875075) (.leaf 451006463)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 105).prefactor = (2544016869317123/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 105).cutoff/(generalMeanRows 105).c)).2 =
    (29309304159663/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 105).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 105).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 105).q*(generalMeanRows 105).cutoff/2-2 = (1148/507:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable065.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 105).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 105

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 105).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 105).criticalRate j.val*(generalMeanRows 105).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 105).c*(generalMeanRows 105).criticalPoint j.val)).2-
      (generalMeanRows 105).J/2-(generalMeanRows 105).error (generalMeanGrid j.val)+
      (generalMeanRows 105).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 105).c)).2-
      (generalMeanRows 105).J/2-(generalMeanRows 105).error 4 := by
  have he : (generalMeanRows 105).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 105) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 105)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0105

/-! Kernel-checked entropy margins for general spectral rectangle 106. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0106
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5379722612) (.branch 2 (.leaf 5204284346) (.leaf 5037059542))) (.branch 5 (.branch 4 (.leaf 4877548597) (.leaf 4725288532)) (.branch 6 (.leaf 4579849786) (.leaf 4440833349)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4307868190) (.leaf 4180608948)) (.branch 10 (.leaf 4058733842) (.leaf 3941942796))) (.branch 13 (.branch 12 (.leaf 3829955727) (.leaf 3722511006)) (.branch 14 (.leaf 3619364043) (.leaf 3520286010))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3425062673) (.branch 17 (.leaf 3333493320) (.leaf 3245389784))) (.branch 20 (.branch 19 (.leaf 3160575546) (.leaf 3078884913)) (.branch 21 (.leaf 3000162259) (.leaf 2924261327)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2851044593) (.leaf 2780382666)) (.branch 25 (.leaf 2712153747) (.leaf 2646243120))) (.branch 28 (.branch 27 (.leaf 2582542687) (.leaf 2520950532)) (.branch 29 (.leaf 2461370522) (.leaf 2403711933)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2347889105) (.branch 32 (.leaf 2293821118) (.leaf 2241431501))) (.branch 35 (.branch 34 (.leaf 2190647944) (.leaf 2141402048)) (.branch 36 (.leaf 2093629079) (.leaf 2047267743)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2002259984) (.leaf 1958550777)) (.branch 40 (.leaf 1916087957) (.leaf 1874822041))) (.branch 43 (.branch 42 (.leaf 1834706072) (.leaf 1795695470)) (.branch 44 (.leaf 1757747890) (.leaf 1720823098))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1684882842) (.branch 47 (.leaf 1649890742) (.leaf 1615812183))) (.branch 50 (.branch 49 (.leaf 1582614213) (.leaf 1550265450)) (.branch 51 (.leaf 1518735993) (.leaf 1487997340)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1458022311) (.leaf 1428784975)) (.branch 55 (.leaf 1400260579) (.leaf 1372425487))) (.branch 58 (.branch 57 (.leaf 1345257117) (.leaf 1318733888)) (.branch 59 (.leaf 1292835161) (.leaf 1267541192))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1242833088) (.branch 62 (.leaf 1218692754) (.leaf 1195102859))) (.branch 65 (.branch 64 (.leaf 1172046792) (.leaf 1149508629)) (.branch 66 (.leaf 1127473093) (.leaf 1105925523)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1084851845) (.leaf 1064238541)) (.branch 70 (.leaf 1044072619) (.leaf 1024341592))) (.branch 73 (.branch 72 (.leaf 1005033449) (.leaf 986136633)) (.branch 74 (.leaf 967640019) (.leaf 949532895))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 931804940) (.branch 77 (.leaf 914446207) (.leaf 897447103))) (.branch 80 (.branch 79 (.leaf 880798377) (.leaf 864491099)) (.branch 81 (.leaf 848516651) (.leaf 832866706)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 817533221) (.leaf 802508423)) (.branch 85 (.leaf 787784793) (.leaf 773355059))) (.branch 88 (.branch 87 (.leaf 759212185) (.leaf 745349360)) (.branch 89 (.leaf 731759986) (.leaf 718437675)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 705376233) (.branch 92 (.leaf 692569658) (.leaf 680012127))) (.branch 95 (.branch 94 (.leaf 667697994) (.leaf 655621778)) (.branch 96 (.leaf 643778161) (.leaf 632161975)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 620768204) (.leaf 609591974)) (.branch 100 (.leaf 598628544) (.leaf 587873310))) (.branch 103 (.branch 102 (.leaf 577321791) (.leaf 566969629)) (.branch 104 (.leaf 556812585) (.leaf 546846532))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 537067451) (.leaf 527471429)) (.branch 108 (.leaf 518054657) (.leaf 508813421))) (.branch 111 (.branch 110 (.leaf 499744102) (.leaf 490843174)) (.branch 112 (.leaf 482107197) (.leaf 473532819)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 465116768) (.leaf 456855853)) (.branch 116 (.leaf 448746961) (.leaf 440787051))) (.branch 119 (.branch 118 (.leaf 432973158) (.leaf 425302384)) (.branch 120 (.leaf 417771901) (.leaf 410378945)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 106).prefactor = (203241157813783/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 106).cutoff/(generalMeanRows 106).c)).2 =
    (118317131924781/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 106).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 106).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 106).q*(generalMeanRows 106).c/2-2 = (691/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable054.value]
    have hcontinuation : (generalMeanRows 106).q*(generalMeanRows 106).cutoff/2-2 = (2322/1001:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable066.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 106).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 106

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 106).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 106).criticalRate j.val*(generalMeanRows 106).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 106).c*(generalMeanRows 106).criticalPoint j.val)).2-
      (generalMeanRows 106).J/2-(generalMeanRows 106).error (generalMeanGrid j.val)+
      (generalMeanRows 106).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 106).c)).2-
      (generalMeanRows 106).J/2-(generalMeanRows 106).error 4 := by
  have he : (generalMeanRows 106).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 106) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 106)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0106

/-! Kernel-checked entropy margins for general spectral rectangle 107. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0107
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5347815043) (.branch 2 (.leaf 5170443337) (.leaf 5001399925))) (.branch 5 (.branch 4 (.leaf 4840178952) (.leaf 4686311615)) (.branch 6 (.leaf 4539362918) (.leaf 4398928770)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4264633385) (.leaf 4136126946)) (.branch 10 (.leaf 4013083493) (.leaf 3895199021))) (.branch 13 (.branch 12 (.leaf 3782189757) (.leaf 3673790594)) (.branch 14 (.leaf 3569753665) (.leaf 3469847053))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3373853606) (.branch 17 (.leaf 3281569855) (.leaf 3192805024))) (.branch 20 (.branch 19 (.leaf 3107380126) (.leaf 3025127128)) (.branch 21 (.leaf 2945888187) (.leaf 2869514943)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2795867871) (.leaf 2724815684)) (.branch 25 (.leaf 2656234776) (.leaf 2590008716))) (.branch 28 (.branch 27 (.leaf 2526027768) (.leaf 2464188461)) (.branch 29 (.leaf 2404393177) (.leaf 2346549775)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2290571244) (.branch 32 (.leaf 2236375378) (.leaf 2183884470))) (.branch 35 (.branch 34 (.leaf 2133025036) (.leaf 2083727549)) (.branch 36 (.leaf 2035926200) (.leaf 1989558666)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1944565903) (.leaf 1900891944)) (.branch 40 (.leaf 1858483718) (.leaf 1817290875))) (.branch 43 (.branch 42 (.leaf 1777265626) (.leaf 1738362595)) (.branch 44 (.leaf 1700538673) (.leaf 1663752890))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1627966291) (.branch 47 (.leaf 1593141820) (.leaf 1559244211))) (.branch 50 (.branch 49 (.leaf 1526239887) (.leaf 1494096867)) (.branch 51 (.leaf 1462784674) (.leaf 1432274250)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1402537884) (.leaf 1373549130)) (.branch 55 (.leaf 1345282743) (.leaf 1317714611))) (.branch 58 (.branch 57 (.leaf 1290821697) (.leaf 1264581979)) (.branch 59 (.leaf 1238974396) (.leaf 1213978796))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1189575893) (.branch 62 (.leaf 1165747215) (.leaf 1142475067))) (.branch 65 (.branch 64 (.leaf 1119742489) (.leaf 1097533217)) (.branch 66 (.leaf 1075831649) (.leaf 1054622813)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1033892332) (.leaf 1013626397)) (.branch 70 (.leaf 993811737) (.leaf 974435594))) (.branch 73 (.branch 72 (.leaf 955485697) (.leaf 936950238)) (.branch 74 (.leaf 918817854) (.leaf 901077597))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 883718923) (.branch 77 (.leaf 866731669) (.leaf 850106035))) (.branch 80 (.branch 79 (.leaf 833832569) (.leaf 817902149)) (.branch 81 (.leaf 802305970) (.leaf 787035527)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 772082606) (.leaf 757439265)) (.branch 85 (.leaf 743097828) (.leaf 729050870))) (.branch 88 (.branch 87 (.leaf 715291205) (.leaf 701811881)) (.branch 89 (.leaf 688606164) (.leaf 675667532)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 662989667) (.branch 92 (.leaf 650566444) (.leaf 638391925))) (.branch 95 (.branch 94 (.leaf 626460350) (.leaf 614766131)) (.branch 96 (.leaf 603303844) (.leaf 592068226)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 581054163) (.leaf 570256688)) (.branch 100 (.leaf 559670977) (.leaf 549292337))) (.branch 103 (.branch 102 (.leaf 539116209) (.leaf 529138159)) (.branch 104 (.leaf 519353871) (.leaf 509759148))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 500349906) (.leaf 491122166)) (.branch 108 (.leaf 482072056) (.leaf 473195805))) (.branch 111 (.branch 110 (.leaf 464489737) (.leaf 455950273)) (.branch 112 (.leaf 447573922) (.leaf 439357283)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 431297038) (.leaf 423389953)) (.branch 116 (.leaf 415632873) (.leaf 408022718))) (.branch 119 (.branch 118 (.leaf 400556484) (.leaf 393231241)) (.branch 120 (.leaf 386044124) (.leaf 378992342)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 107).prefactor = (2573213011006617/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 107).cutoff/(generalMeanRows 107).c)).2 =
    (464757838031217/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 107).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 107).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 107).q*(generalMeanRows 107).c/2-2 = (357/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable067.value]
    have hcontinuation : (generalMeanRows 107).q*(generalMeanRows 107).cutoff/2-2 = (2322/1001:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable066.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 107).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 107

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 107).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 107).criticalRate j.val*(generalMeanRows 107).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 107).c*(generalMeanRows 107).criticalPoint j.val)).2-
      (generalMeanRows 107).J/2-(generalMeanRows 107).error (generalMeanGrid j.val)+
      (generalMeanRows 107).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 107).c)).2-
      (generalMeanRows 107).J/2-(generalMeanRows 107).error 4 := by
  have he : (generalMeanRows 107).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 107) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 107)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0107

/-! Kernel-checked entropy margins for general spectral rectangle 108. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0108
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4965228713) (.branch 2 (.leaf 4786967847) (.leaf 4617158617))) (.branch 5 (.branch 4 (.leaf 4455295847) (.leaf 4300910921)) (.branch 6 (.leaf 4153568592) (.leaf 4012864122)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3878420727) (.leaf 3749887277)) (.branch 10 (.leaf 3626936225) (.leaf 3509261735))) (.branch 13 (.branch 12 (.leaf 3396577988) (.leaf 3288617644)) (.branch 14 (.leaf 3185130446) (.leaf 3085881947))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2990652348) (.branch 17 (.leaf 2899235434) (.leaf 2811437608))) (.branch 20 (.branch 19 (.leaf 2727076994) (.leaf 2645982620)) (.branch 21 (.leaf 2567993668) (.leaf 2492958780)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2420735415) (.leaf 2351189270)) (.branch 25 (.leaf 2284193723) (.leaf 2219629340))) (.branch 28 (.branch 27 (.leaf 2157383403) (.leaf 2097349481)) (.branch 29 (.leaf 2039427026) (.leaf 1983521006)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1929541556) (.branch 32 (.leaf 1877403659) (.leaf 1827026843))) (.branch 35 (.branch 34 (.leaf 1778334911) (.leaf 1731255672)) (.branch 36 (.leaf 1685720709) (.leaf 1641665144)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1599027437) (.leaf 1557749182)) (.branch 40 (.leaf 1517774927) (.leaf 1479052002))) (.branch 43 (.branch 42 (.leaf 1441530358) (.leaf 1405162416)) (.branch 44 (.leaf 1369902928) (.leaf 1335708842))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1302539182) (.branch 47 (.leaf 1270354929) (.leaf 1239118916))) (.branch 50 (.branch 49 (.leaf 1208795720) (.leaf 1179351573)) (.branch 51 (.leaf 1150754267) (.leaf 1122973071)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1095978655) (.leaf 1069743007)) (.branch 55 (.leaf 1044239371) (.leaf 1019442178))) (.branch 58 (.branch 57 (.leaf 995326981) (.leaf 971870402)) (.branch 59 (.leaf 949050070) (.leaf 926844576))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 905233419) (.branch 62 (.leaf 884196961) (.leaf 863716384))) (.branch 65 (.branch 64 (.leaf 843773650) (.leaf 824351461)) (.branch 66 (.leaf 805433219) (.leaf 787002999)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 769045511) (.leaf 751546067)) (.branch 70 (.leaf 734490561) (.leaf 717865430))) (.branch 73 (.branch 72 (.leaf 701657638) (.leaf 685854643)) (.branch 74 (.leaf 670444380) (.leaf 655415237))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 640756032) (.branch 77 (.leaf 626455995) (.leaf 612504750))) (.branch 80 (.branch 79 (.leaf 598892297) (.leaf 585608992)) (.branch 81 (.leaf 572645537) (.leaf 559992958)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 547642597) (.leaf 535586094)) (.branch 85 (.leaf 523815377) (.leaf 512322647))) (.branch 88 (.branch 87 (.leaf 501100367) (.leaf 490141254)) (.branch 89 (.leaf 479438265) (.leaf 468984588)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 458773633) (.branch 92 (.leaf 448799022) (.leaf 439054582))) (.branch 95 (.branch 94 (.leaf 429534335) (.leaf 420232492)) (.branch 96 (.leaf 411143443) (.leaf 402261754)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 393582155) (.leaf 385099539)) (.branch 100 (.leaf 376808952) (.leaf 368705589))) (.branch 103 (.branch 102 (.leaf 360784787) (.leaf 353042022)) (.branch 104 (.leaf 345472901) (.leaf 338073161))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 330838659) (.leaf 323765374)) (.branch 108 (.leaf 316849397) (.leaf 310086930))) (.branch 111 (.branch 110 (.leaf 303474282) (.leaf 297007864)) (.branch 112 (.leaf 290684188) (.leaf 284499860)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 278451580) (.leaf 272536136)) (.branch 116 (.leaf 266750405) (.leaf 261091345))) (.branch 119 (.branch 118 (.leaf 255555998) (.leaf 250141482)) (.branch 120 (.leaf 244844991) (.leaf 239663793)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 108).prefactor = (5155557843012159/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 108).cutoff/(generalMeanRows 108).c)).2 =
    (82070940457711/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 108).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 108).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 108).q*(generalMeanRows 108).c/2-2 = (829/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable068.value]
    have hcontinuation : (generalMeanRows 108).q*(generalMeanRows 108).cutoff/2-2 = (1148/507:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable065.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 108).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 108

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 108).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 108).criticalRate j.val*(generalMeanRows 108).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 108).c*(generalMeanRows 108).criticalPoint j.val)).2-
      (generalMeanRows 108).J/2-(generalMeanRows 108).error (generalMeanGrid j.val)+
      (generalMeanRows 108).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 108).c)).2-
      (generalMeanRows 108).J/2-(generalMeanRows 108).error 4 := by
  have he : (generalMeanRows 108).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 108) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 108)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0108

/-! Kernel-checked entropy margins for general spectral rectangle 109. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0109
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4941887088) (.branch 2 (.leaf 4761854164) (.leaf 4590390868))) (.branch 5 (.branch 4 (.leaf 4426985280) (.leaf 4271162496)) (.branch 6 (.leaf 4122481398) (.leaf 3980531759)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3844931658) (.leaf 3715325151)) (.branch 10 (.leaf 3591380174) (.leaf 3472786650))) (.branch 13 (.branch 12 (.leaf 3359254769) (.leaf 3250513440)) (.branch 14 (.leaf 3146308870) (.leaf 3046403280))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2950573726) (.branch 17 (.leaf 2858611025) (.leaf 2770318774))) (.branch 20 (.branch 19 (.leaf 2685512444) (.leaf 2604018554)) (.branch 21 (.leaf 2525673910) (.leaf 2450324900)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2377826852) (.leaf 2308043435)) (.branch 25 (.leaf 2240846110) (.leaf 2176113617))) (.branch 28 (.branch 27 (.leaf 2113731505) (.leaf 2053591698)) (.branch 29 (.leaf 1995592082) (.leaf 1939636136)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1885632578) (.branch 32 (.leaf 1833495043) (.leaf 1783141776))) (.branch 35 (.branch 34 (.leaf 1734495355) (.leaf 1687482426)) (.branch 36 (.leaf 1642033458) (.leaf 1598082518)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1555567054) (.leaf 1514427697)) (.branch 40 (.leaf 1474608076) (.leaf 1436054645))) (.branch 43 (.branch 42 (.leaf 1398716516) (.leaf 1362545313)) (.branch 44 (.leaf 1327495023) (.leaf 1293521867))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1260584172) (.branch 47 (.leaf 1228642254) (.leaf 1197658310))) (.branch 50 (.branch 49 (.leaf 1167596313) (.leaf 1138421912)) (.branch 51 (.leaf 1110102346) (.leaf 1082606355)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1055904100) (.leaf 1029967088)) (.branch 55 (.leaf 1004768100) (.leaf 980281124))) (.branch 58 (.branch 57 (.leaf 956481291) (.leaf 933344819)) (.branch 59 (.leaf 910848952) (.leaf 888971910))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 867692841) (.branch 62 (.leaf 846991769) (.leaf 826849557))) (.branch 65 (.branch 64 (.leaf 807247856) (.leaf 788169075)) (.branch 66 (.leaf 769596337) (.leaf 751513448)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 733904861) (.leaf 716755646)) (.branch 70 (.leaf 700051462) (.leaf 683778526))) (.branch 73 (.branch 72 (.leaf 667923586) (.leaf 652473901)) (.branch 74 (.leaf 637417212) (.leaf 622741722))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 608436075) (.branch 77 (.leaf 594489334) (.leaf 580890964))) (.branch 80 (.branch 79 (.leaf 567630812) (.leaf 554699093)) (.branch 81 (.leaf 542086370) (.leaf 529783541)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 517781823) (.leaf 506072739)) (.branch 85 (.leaf 494648105) (.leaf 483500017))) (.branch 88 (.branch 87 (.leaf 472620840) (.leaf 462003195)) (.branch 89 (.leaf 451639950) (.leaf 441524208)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 431649299) (.branch 92 (.leaf 422008770) (.leaf 412596378))) (.branch 95 (.branch 94 (.leaf 403406077) (.leaf 394432016)) (.branch 96 (.leaf 385668527) (.leaf 377110120)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 368751474) (.leaf 360587433)) (.branch 100 (.leaf 352612999) (.leaf 344823325))) (.branch 103 (.branch 102 (.leaf 337213710) (.leaf 329779593)) (.branch 104 (.leaf 322516550) (.leaf 315420286))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 308486631) (.leaf 301711539)) (.branch 108 (.leaf 295091077) (.leaf 288621428))) (.branch 111 (.branch 110 (.leaf 282298882) (.leaf 276119833)) (.branch 112 (.leaf 270080780) (.leaf 264178315)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 258409128) (.leaf 252769998)) (.branch 116 (.leaf 247257796) (.leaf 241869473))) (.branch 119 (.branch 118 (.leaf 236602068) (.leaf 231452695)) (.branch 120 (.leaf 226418548) (.leaf 221496896)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 109).prefactor = (5223978070510759/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 109).cutoff/(generalMeanRows 109).c)).2 =
    (80451498411187/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 109).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 109).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 109).q*(generalMeanRows 109).c/2-2 = (213/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable069.value]
    have hcontinuation : (generalMeanRows 109).q*(generalMeanRows 109).cutoff/2-2 = (1148/507:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable065.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 109).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 109

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 109).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 109).criticalRate j.val*(generalMeanRows 109).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 109).c*(generalMeanRows 109).criticalPoint j.val)).2-
      (generalMeanRows 109).J/2-(generalMeanRows 109).error (generalMeanGrid j.val)+
      (generalMeanRows 109).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 109).c)).2-
      (generalMeanRows 109).J/2-(generalMeanRows 109).error 4 := by
  have he : (generalMeanRows 109).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 109) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 109)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0109

/-! Kernel-checked entropy margins for general spectral rectangle 110. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0110
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4919178722) (.branch 2 (.leaf 4737393054) (.leaf 4564295988))) (.branch 5 (.branch 4 (.leaf 4399368740) (.leaf 4242130011)) (.branch 6 (.leaf 4092132708) (.leaf 3948961022)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3812227806) (.leaf 3681572220)) (.branch 10 (.leaf 3556657606) (.leaf 3437169573))) (.branch 13 (.branch 12 (.leaf 3322814259) (.leaf 3213316755)) (.branch 14 (.leaf 3108419678) (.leaf 3007881860))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2911477166) (.branch 17 (.leaf 2818993397) (.leaf 2730231301))) (.branch 20 (.branch 19 (.leaf 2645003659) (.leaf 2563134441)) (.branch 21 (.leaf 2484458044) (.leaf 2408818572)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2336069192) (.leaf 2266071521)) (.branch 25 (.leaf 2198695074) (.leaf 2133816746))) (.branch 28 (.branch 27 (.leaf 2071320333) (.leaf 2011096093)) (.branch 29 (.leaf 1953040330) (.leaf 1897055021)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1843047452) (.branch 32 (.leaf 1790929896) (.leaf 1740619306))) (.branch 35 (.branch 34 (.leaf 1692037026) (.leaf 1645108528)) (.branch 36 (.leaf 1599763164) (.leaf 1555933935)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1513557275) (.leaf 1472572847)) (.branch 40 (.leaf 1432923358) (.leaf 1394554383))) (.branch 43 (.branch 42 (.leaf 1357414195) (.leaf 1321453617)) (.branch 44 (.leaf 1286625874) (.leaf 1252886458))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1220193002) (.branch 47 (.leaf 1188505158) (.leaf 1157784491))) (.branch 50 (.branch 49 (.leaf 1127994367) (.leaf 1099099861)) (.branch 51 (.leaf 1071067661) (.leaf 1043865980)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1017464479) (.leaf 991834185)) (.branch 55 (.leaf 966947421) (.leaf 942777738))) (.branch 58 (.branch 57 (.leaf 919299853) (.leaf 896489582)) (.branch 59 (.leaf 874323792) (.leaf 852780341))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 831838029) (.branch 62 (.leaf 811476552) (.leaf 791676456))) (.branch 65 (.branch 64 (.leaf 772419093) (.leaf 753686585)) (.branch 66 (.leaf 735461782) (.leaf 717728229)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 700470132) (.leaf 683672323)) (.branch 70 (.leaf 667320236) (.leaf 651399873))) (.branch 73 (.branch 72 (.leaf 635897778) (.leaf 620801016)) (.branch 74 (.leaf 606097142) (.leaf 591774183))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 577820616) (.branch 77 (.leaf 564225345) (.leaf 550977684))) (.branch 80 (.branch 79 (.leaf 538067337) (.leaf 525484381)) (.branch 81 (.leaf 513219253) (.leaf 501262726)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 489605902) (.leaf 478240196)) (.branch 85 (.leaf 467157319) (.leaf 456349271))) (.branch 88 (.branch 87 (.leaf 445808322) (.leaf 435527008)) (.branch 89 (.leaf 425498113) (.leaf 415714664)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 406169920) (.branch 92 (.leaf 396857359) (.leaf 387770672))) (.branch 95 (.branch 94 (.leaf 378903757) (.leaf 370250705)) (.branch 96 (.leaf 361805796) (.leaf 353563492)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 345518428) (.leaf 337665407)) (.branch 100 (.leaf 329999391) (.leaf 322515498))) (.branch 103 (.branch 102 (.leaf 315208996) (.leaf 308075293)) (.branch 104 (.leaf 301109940) (.leaf 294308615))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 287667130) (.leaf 281181416)) (.branch 108 (.leaf 274847525) (.leaf 268661624))) (.branch 111 (.branch 110 (.leaf 262619990) (.leaf 256719008)) (.branch 112 (.leaf 250955166) (.leaf 245325049)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 239825343) (.leaf 234452822)) (.branch 116 (.leaf 229204354) (.leaf 224076891))) (.branch 119 (.branch 118 (.leaf 219067471) (.leaf 214173212)) (.branch 120 (.leaf 209391311) (.leaf 204719040)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 110).prefactor = (2646653156861203/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 110).cutoff/(generalMeanRows 110).c)).2 =
    (24639082522417/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 110).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 110).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 110).q*(generalMeanRows 110).cutoff/2-2 = (1148/507:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable065.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 110).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 110

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 110).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 110).criticalRate j.val*(generalMeanRows 110).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 110).c*(generalMeanRows 110).criticalPoint j.val)).2-
      (generalMeanRows 110).J/2-(generalMeanRows 110).error (generalMeanGrid j.val)+
      (generalMeanRows 110).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 110).c)).2-
      (generalMeanRows 110).J/2-(generalMeanRows 110).error 4 := by
  have he : (generalMeanRows 110).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 110) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 110)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0110

/-! Kernel-checked entropy margins for general spectral rectangle 111. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0111
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7512015270) (.branch 2 (.leaf 7291650072) (.leaf 7080718773))) (.branch 5 (.branch 4 (.leaf 6878701587) (.leaf 6685114770)) (.branch 6 (.leaf 6499507430) (.leaf 6321458677)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6150575101) (.leaf 5986488512)) (.branch 10 (.leaf 5828853906) (.leaf 5677347654))) (.branch 13 (.branch 12 (.leaf 5531665852) (.leaf 5391522838)) (.branch 14 (.leaf 5256649853) (.leaf 5126793809))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5001716187) (.branch 17 (.leaf 4881192014) (.leaf 4765008943))) (.branch 20 (.branch 19 (.leaf 4652966397) (.leaf 4544874791)) (.branch 21 (.leaf 4440554819) (.leaf 4339836788)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4242560016) (.leaf 4148572263)) (.branch 25 (.leaf 4057729217) (.leaf 3969894007))) (.branch 28 (.branch 27 (.leaf 3884936763) (.leaf 3802734192)) (.branch 29 (.leaf 3723169202) (.leaf 3646130536)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3571512440) (.branch 32 (.leaf 3499214350) (.leaf 3429140603))) (.branch 35 (.branch 34 (.leaf 3361200163) (.leaf 3295306363)) (.branch 36 (.leaf 3231376673) (.leaf 3169332472)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3109098840) (.leaf 3050604358)) (.branch 40 (.leaf 2993780929) (.leaf 2938563600))) (.branch 43 (.branch 42 (.leaf 2884890400) (.leaf 2832702184)) (.branch 44 (.leaf 2781942494) (.leaf 2732557416))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2684495456) (.branch 47 (.leaf 2637707415) (.leaf 2592146278))) (.branch 50 (.branch 49 (.leaf 2547767103) (.leaf 2504526921)) (.branch 51 (.leaf 2462384639) (.leaf 2421300946)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2381238231) (.leaf 2342160499)) (.branch 55 (.leaf 2304033291) (.leaf 2266823617))) (.branch 58 (.branch 57 (.leaf 2230499879) (.leaf 2195031813)) (.branch 59 (.leaf 2160390419) (.leaf 2126547907))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2093477639) (.branch 62 (.leaf 2061154075) (.leaf 2029552723))) (.branch 65 (.branch 64 (.leaf 1998650092) (.leaf 1968423645)) (.branch 66 (.leaf 1938851754) (.leaf 1909913663)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1881589445) (.leaf 1853859965)) (.branch 70 (.leaf 1826706849) (.leaf 1800112442))) (.branch 73 (.branch 72 (.leaf 1774059784) (.leaf 1748532575)) (.branch 74 (.leaf 1723515145) (.leaf 1698992431))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1674949946) (.branch 77 (.leaf 1651373755) (.leaf 1628250453))) (.branch 80 (.branch 79 (.leaf 1605567139) (.leaf 1583311396)) (.branch 81 (.leaf 1561471272) (.leaf 1540035255)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1518992260) (.leaf 1498331607)) (.branch 85 (.leaf 1478043005) (.leaf 1458116537))) (.branch 88 (.branch 87 (.leaf 1438542640) (.leaf 1419312097)) (.branch 89 (.leaf 1400416016) (.leaf 1381845820)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1363593234) (.branch 92 (.leaf 1345650269) (.leaf 1328009215))) (.branch 95 (.branch 94 (.leaf 1310662628) (.leaf 1293603318)) (.branch 96 (.leaf 1276824338) (.leaf 1260318977)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1244080748) (.leaf 1228103381)) (.branch 100 (.leaf 1212380812) (.leaf 1196907177))) (.branch 103 (.branch 102 (.leaf 1181676802) (.leaf 1166684197)) (.branch 104 (.leaf 1151924049) (.leaf 1137391214))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1123080709) (.leaf 1108987710)) (.branch 108 (.leaf 1095107541) (.leaf 1081435673))) (.branch 111 (.branch 110 (.leaf 1067967713) (.leaf 1054699405)) (.branch 112 (.leaf 1041626618) (.leaf 1028745347)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1016051705) (.leaf 1003541920)) (.branch 116 (.leaf 991212331) (.leaf 979059381))) (.branch 119 (.branch 118 (.leaf 967079616) (.leaf 955269682)) (.branch 120 (.leaf 943626317) (.leaf 932146352)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 111).prefactor = (5096863777079071/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 111).cutoff/(generalMeanRows 111).c)).2 =
    (102833339119153/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 111).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 111).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 111).q*(generalMeanRows 111).cutoff/2-2 = (237/140:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable070.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 111).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 111

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 111).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 111).criticalRate j.val*(generalMeanRows 111).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 111).c*(generalMeanRows 111).criticalPoint j.val)).2-
      (generalMeanRows 111).J/2-(generalMeanRows 111).error (generalMeanGrid j.val)+
      (generalMeanRows 111).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 111).c)).2-
      (generalMeanRows 111).J/2-(generalMeanRows 111).error 4 := by
  have he : (generalMeanRows 111).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 111) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 111)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0111

/-! Kernel-checked entropy margins for general spectral rectangle 112. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0112
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7730691757) (.branch 2 (.leaf 7499597500) (.leaf 7278398424))) (.branch 5 (.branch 4 (.leaf 7066550149) (.leaf 6863546039)) (.branch 6 (.leaf 6668913855) (.leaf 6482212781)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6303030769) (.leaf 6130982178)) (.branch 10 (.leaf 5965705647) (.leaf 5806862190))) (.branch 13 (.branch 12 (.leaf 5654133474) (.leaf 5507220265)) (.branch 14 (.leaf 5365841022) (.leaf 5229730613))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5098639153) (.branch 17 (.leaf 4972330941) (.leaf 4850583488))) (.branch 20 (.branch 19 (.leaf 4733186631) (.leaf 4619941710)) (.branch 21 (.leaf 4510660823) (.leaf 4405166134)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4303289233) (.leaf 4204870551)) (.branch 25 (.leaf 4109758816) (.leaf 4017810544))) (.branch 28 (.branch 27 (.leaf 3928889577) (.leaf 3842866643)) (.branch 29 (.leaf 3759618961) (.leaf 3679029853)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3600988407) (.branch 32 (.leaf 3525389140) (.leaf 3452131699))) (.branch 35 (.branch 34 (.leaf 3381120573) (.leaf 3312264827)) (.branch 36 (.leaf 3245477855) (.leaf 3180677142)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3117784048) (.leaf 3056723600)) (.branch 40 (.leaf 2997424298) (.leaf 2939817938))) (.branch 43 (.branch 42 (.leaf 2883839436) (.leaf 2829426667)) (.branch 44 (.leaf 2776520319) (.leaf 2725063745))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2675002829) (.branch 47 (.leaf 2626285863) (.leaf 2578863423))) (.branch 50 (.branch 49 (.leaf 2532688257) (.leaf 2487715179)) (.branch 51 (.leaf 2443900968) (.leaf 2401204270)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2359585513) (.leaf 2319006815)) (.branch 55 (.leaf 2279431907) (.leaf 2240826057))) (.branch 58 (.branch 57 (.leaf 2203155992) (.leaf 2166389838)) (.branch 59 (.leaf 2130497044) (.leaf 2095448331))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2061215622) (.branch 62 (.leaf 2027771997) (.leaf 1995091632))) (.branch 65 (.branch 64 (.leaf 1963149753) (.leaf 1931922585)) (.branch 66 (.leaf 1901387311) (.leaf 1871522024)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1842305690) (.leaf 1813718105)) (.branch 70 (.leaf 1785739861) (.leaf 1758352311))) (.branch 73 (.branch 72 (.leaf 1731537531) (.leaf 1705278293)) (.branch 74 (.leaf 1679558033) (.leaf 1654360819))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1629671328) (.branch 77 (.leaf 1605474816) (.leaf 1581757096))) (.branch 80 (.branch 79 (.leaf 1558504510) (.leaf 1535703910)) (.branch 81 (.leaf 1513342636) (.leaf 1491408491)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1469889728) (.leaf 1448775023)) (.branch 85 (.leaf 1428053466) (.leaf 1407714536))) (.branch 88 (.branch 87 (.leaf 1387748090) (.leaf 1368144342)) (.branch 89 (.leaf 1348893855) (.leaf 1329987520)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1311416548) (.branch 92 (.leaf 1293172451) (.leaf 1275247035))) (.branch 95 (.branch 94 (.leaf 1257632386) (.leaf 1240320859)) (.branch 96 (.leaf 1223305064) (.leaf 1206577861)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1190132346) (.leaf 1173961845)) (.branch 100 (.leaf 1158059901) (.leaf 1142420268))) (.branch 103 (.branch 102 (.leaf 1127036900) (.leaf 1111903948)) (.branch 104 (.leaf 1097015748) (.leaf 1082366815))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1067951836) (.leaf 1053765665)) (.branch 108 (.leaf 1039803312) (.leaf 1026059943))) (.branch 111 (.branch 110 (.leaf 1012530871) (.leaf 999211548)) (.branch 112 (.leaf 986097566) (.leaf 973184646)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 960468634) (.leaf 947945501)) (.branch 116 (.leaf 935611331) (.leaf 923462324))) (.branch 119 (.branch 118 (.leaf 911494788) (.leaf 899705133)) (.branch 120 (.leaf 888089873) (.leaf 876645617)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 112).prefactor = (2672577347027949/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 112).cutoff/(generalMeanRows 112).c)).2 =
    (50020006984811/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 112).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 112).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 112).q*(generalMeanRows 112).c/2-2 = (19/40:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable046.value]
    have hcontinuation : (generalMeanRows 112).q*(generalMeanRows 112).cutoff/2-2 = (237/140:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable070.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 112).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 112

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 112).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 112).criticalRate j.val*(generalMeanRows 112).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 112).c*(generalMeanRows 112).criticalPoint j.val)).2-
      (generalMeanRows 112).J/2-(generalMeanRows 112).error (generalMeanGrid j.val)+
      (generalMeanRows 112).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 112).c)).2-
      (generalMeanRows 112).J/2-(generalMeanRows 112).error 4 := by
  have he : (generalMeanRows 112).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 112) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 112)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0112

/-! Kernel-checked entropy margins for general spectral rectangle 113. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0113
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7015412726) (.branch 2 (.leaf 6776214665) (.leaf 6547414053))) (.branch 5 (.branch 4 (.leaf 6328443632) (.leaf 6118775377)) (.branch 6 (.leaf 5917917007) (.leaf 5725408892)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5540821293) (.leaf 5363751897)) (.branch 10 (.leaf 5193823616) (.leaf 5030682595))) (.branch 13 (.branch 12 (.leaf 4873996428) (.leaf 4723452540)) (.branch 14 (.leaf 4578756726) (.leaf 4439631815))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4305816468) (.branch 17 (.leaf 4177064068) (.leaf 4053141714))) (.branch 20 (.branch 19 (.leaf 3933829298) (.leaf 3818918657)) (.branch 21 (.leaf 3708212792) (.leaf 3601525157)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3498678991) (.leaf 3399506715)) (.branch 25 (.leaf 3303849361) (.leaf 3211556054))) (.branch 28 (.branch 27 (.leaf 3122483526) (.leaf 3036495665)) (.branch 29 (.leaf 2953463099) (.leaf 2873262806)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2795777750) (.branch 32 (.leaf 2720896545) (.leaf 2648513138))) (.branch 35 (.branch 34 (.leaf 2578526514) (.leaf 2510840423)) (.branch 36 (.leaf 2445363115) (.leaf 2382007106)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2320688947) (.leaf 2261329009)) (.branch 40 (.leaf 2203851289) (.leaf 2148183215))) (.branch 43 (.branch 42 (.leaf 2094255476) (.leaf 2042001850)) (.branch 44 (.leaf 1991359050) (.leaf 1942266578))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1894666582) (.branch 47 (.leaf 1848503729) (.leaf 1803725075))) (.branch 50 (.branch 49 (.leaf 1760279956) (.leaf 1718119871)) (.branch 51 (.leaf 1677198379) (.leaf 1637471004)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1598895134) (.leaf 1561429941)) (.branch 55 (.leaf 1525036291) (.leaf 1489676665))) (.branch 58 (.branch 57 (.leaf 1455315088) (.leaf 1421917054)) (.branch 59 (.leaf 1389449458) (.leaf 1357880534))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1327179793) (.branch 62 (.leaf 1297317965) (.leaf 1268266944))) (.branch 65 (.branch 64 (.leaf 1239999736) (.leaf 1212490409)) (.branch 66 (.leaf 1185714045) (.leaf 1159646699)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1134265351) (.leaf 1109547868)) (.branch 70 (.leaf 1085472966) (.leaf 1062020172))) (.branch 73 (.branch 72 (.leaf 1039169790) (.leaf 1016902867)) (.branch 74 (.leaf 995201159) (.leaf 974047105))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 953423796) (.branch 77 (.leaf 933314946) (.leaf 913704869))) (.branch 80 (.branch 79 (.leaf 894578452) (.leaf 875921128)) (.branch 81 (.leaf 857718862) (.leaf 839958119)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 822625850) (.leaf 805709470)) (.branch 85 (.leaf 789196840) (.leaf 773076247))) (.branch 88 (.branch 87 (.leaf 757336388) (.leaf 741966353)) (.branch 89 (.leaf 726955612) (.leaf 712293994)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 697971679) (.branch 92 (.leaf 683979179) (.leaf 670307330))) (.branch 95 (.branch 94 (.leaf 656947274) (.leaf 643890451)) (.branch 96 (.leaf 631128586) (.leaf 618653677)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 606457986) (.leaf 594534028)) (.branch 100 (.leaf 582874563) (.leaf 571472583))) (.branch 103 (.branch 102 (.leaf 560321307) (.leaf 549414171)) (.branch 104 (.leaf 538744819) (.leaf 528307097))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 518095045) (.leaf 508102886)) (.branch 108 (.leaf 498325028) (.leaf 488756046))) (.branch 111 (.branch 110 (.leaf 479390687) (.leaf 470223854)) (.branch 112 (.leaf 461250608) (.leaf 452466158)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 443865856) (.leaf 435445194)) (.branch 116 (.leaf 427199798) (.leaf 419125421))) (.branch 119 (.branch 118 (.leaf 411217943) (.leaf 403473362)) (.branch 120 (.leaf 395887793) (.leaf 388457464)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 113).prefactor = (5605540966559077/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 113).cutoff/(generalMeanRows 113).c)).2 =
    (315002247538181/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 113).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 113).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 113).q*(generalMeanRows 113).c/2-2 = (139/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable026.value]
    have hcontinuation : (generalMeanRows 113).q*(generalMeanRows 113).cutoff/2-2 = (237/140:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable070.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 113).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 113

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 113).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 113).criticalRate j.val*(generalMeanRows 113).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 113).c*(generalMeanRows 113).criticalPoint j.val)).2-
      (generalMeanRows 113).J/2-(generalMeanRows 113).error (generalMeanGrid j.val)+
      (generalMeanRows 113).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 113).c)).2-
      (generalMeanRows 113).J/2-(generalMeanRows 113).error 4 := by
  have he : (generalMeanRows 113).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 113) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 113)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0113

/-! Kernel-checked entropy margins for general spectral rectangle 114. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0114
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6212438400) (.branch 2 (.leaf 6027470774) (.leaf 5850676037))) (.branch 5 (.branch 4 (.leaf 5681587066) (.leaf 5519769577)) (.branch 6 (.leaf 5364819254) (.leaf 5216359192)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5074037608) (.leaf 4937525793)) (.branch 10 (.leaf 4806516270) (.leaf 4680721131))) (.branch 13 (.branch 12 (.leaf 4559870536) (.leaf 4443711356)) (.branch 14 (.leaf 4332005933) (.leaf 4224530957))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4121076442) (.branch 17 (.leaf 4021444787) (.leaf 3925449920))) (.branch 20 (.branch 19 (.leaf 3832916508) (.leaf 3743679239)) (.branch 21 (.leaf 3657582153) (.leaf 3574478028)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3494227820) (.leaf 3416700134)) (.branch 25 (.leaf 3341770746) (.leaf 3269322151))) (.branch 28 (.branch 27 (.leaf 3199243148) (.leaf 3131428458)) (.branch 29 (.leaf 3065778360) (.leaf 3002198361)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2940598885) (.branch 32 (.leaf 2880894981) (.leaf 2823006057))) (.branch 35 (.branch 34 (.leaf 2766855624) (.leaf 2712371060)) (.branch 36 (.leaf 2659483394) (.leaf 2608127095)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2558239881) (.leaf 2509762537)) (.branch 40 (.leaf 2462638747) (.leaf 2416814932))) (.branch 43 (.branch 42 (.leaf 2372240102) (.leaf 2328865717)) (.branch 44 (.leaf 2286645550) (.leaf 2245535570))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2205493819) (.branch 47 (.leaf 2166480304) (.leaf 2128456895))) (.branch 50 (.branch 49 (.leaf 2091387225) (.leaf 2055236601)) (.branch 51 (.leaf 2019971915) (.leaf 1985561561)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1951975363) (.leaf 1919184496)) (.branch 55 (.leaf 1887161422) (.leaf 1855879823))) (.branch 58 (.branch 57 (.leaf 1825314538) (.leaf 1795441509)) (.branch 59 (.leaf 1766237723) (.leaf 1737681161))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1709750749) (.branch 62 (.leaf 1682426311) (.leaf 1655688527))) (.branch 65 (.branch 64 (.leaf 1629518889) (.leaf 1603899662)) (.branch 66 (.leaf 1578813848) (.leaf 1554245150)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1530177938) (.leaf 1506597217)) (.branch 70 (.leaf 1483488597) (.leaf 1460838266))) (.branch 73 (.branch 72 (.leaf 1438632961) (.leaf 1416859944)) (.branch 74 (.leaf 1395506973) (.leaf 1374562287))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1354014575) (.branch 77 (.leaf 1333852963) (.leaf 1314066988))) (.branch 80 (.branch 79 (.leaf 1294646583) (.leaf 1275582058)) (.branch 81 (.leaf 1256864081) (.leaf 1238483666)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1220432153) (.leaf 1202701198)) (.branch 85 (.leaf 1185282755) (.leaf 1168169064))) (.branch 88 (.branch 87 (.leaf 1151352641) (.leaf 1134826262)) (.branch 89 (.leaf 1118582955) (.leaf 1102615987)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1086918854) (.branch 92 (.leaf 1071485273) (.leaf 1056309169))) (.branch 95 (.branch 94 (.leaf 1041384670) (.leaf 1026706098)) (.branch 96 (.leaf 1012267956) (.leaf 998064928)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 984091865) (.leaf 970343783)) (.branch 100 (.leaf 956815852) (.leaf 943503392))) (.branch 103 (.branch 102 (.leaf 930401868) (.leaf 917506883)) (.branch 104 (.leaf 904814169) (.leaf 892319590))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 880019128) (.leaf 867908884)) (.branch 108 (.leaf 855985072) (.leaf 844244013))) (.branch 111 (.branch 110 (.leaf 832682135) (.leaf 821295962)) (.branch 112 (.leaf 810082117) (.leaf 799037317)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 788158365) (.leaf 777442152)) (.branch 116 (.leaf 766885651) (.leaf 756485915))) (.branch 119 (.branch 118 (.leaf 746240074) (.leaf 736145333)) (.branch 120 (.leaf 726198967) (.leaf 716398319)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 114).prefactor = (4672355818508523/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 114).cutoff/(generalMeanRows 114).c)).2 =
    (443962678536877/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 114).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 114).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 114).q*(generalMeanRows 114).c/2-2 = (41/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable058.value]
    have hcontinuation : (generalMeanRows 114).q*(generalMeanRows 114).cutoff/2-2 = (23/12:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable028.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 114).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 114

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 114).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 114).criticalRate j.val*(generalMeanRows 114).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 114).c*(generalMeanRows 114).criticalPoint j.val)).2-
      (generalMeanRows 114).J/2-(generalMeanRows 114).error (generalMeanGrid j.val)+
      (generalMeanRows 114).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 114).c)).2-
      (generalMeanRows 114).J/2-(generalMeanRows 114).error 4 := by
  have he : (generalMeanRows 114).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 114) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 114)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0114

/-! Kernel-checked entropy margins for general spectral rectangle 115. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0115
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6317755157) (.branch 2 (.leaf 6126125495) (.leaf 5942970710))) (.branch 5 (.branch 4 (.leaf 5767807254) (.leaf 5600185561)) (.branch 6 (.leaf 5439687071) (.leaf 5285921585)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5138524898) (.leaf 4997156676)) (.branch 10 (.leaf 4861498554) (.leaf 4731252412))) (.branch 13 (.branch 12 (.leaf 4606138824) (.leaf 4485895648)) (.branch 14 (.leaf 4370276753) (.leaf 4259050850))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4152000432) (.branch 17 (.leaf 4048920807) (.leaf 3949619209))) (.branch 20 (.branch 19 (.leaf 3853913983) (.leaf 3761633838)) (.branch 21 (.leaf 3672617161) (.leaf 3586711380)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3503772378) (.leaf 3423663957)) (.branch 25 (.leaf 3346257335) (.leaf 3271430683))) (.branch 28 (.branch 27 (.leaf 3199068694) (.leaf 3129062187)) (.branch 29 (.leaf 3061307733) (.leaf 2995707313)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2932167994) (.branch 32 (.leaf 2870601632) (.leaf 2810924590))) (.branch 35 (.branch 34 (.leaf 2753057479) (.leaf 2696924914)) (.branch 36 (.leaf 2642455286) (.leaf 2589580547)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2538236013) (.leaf 2488360174)) (.branch 40 (.leaf 2439894523) (.leaf 2392783384))) (.branch 43 (.branch 42 (.leaf 2346973764) (.leaf 2302415204)) (.branch 44 (.leaf 2259059645) (.leaf 2216861296))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2175776518) (.branch 47 (.leaf 2135763707) (.leaf 2096783186))) (.branch 50 (.branch 49 (.leaf 2058797108) (.leaf 2021769357)) (.branch 51 (.leaf 1985665462) (.leaf 1950452510)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1916099066) (.leaf 1882575099)) (.branch 55 (.leaf 1849851910) (.leaf 1817902066))) (.branch 58 (.branch 57 (.leaf 1786699336) (.leaf 1756218629)) (.branch 59 (.leaf 1726435941) (.leaf 1697328297))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1668873706) (.branch 62 (.leaf 1641051105) (.leaf 1613840323))) (.branch 65 (.branch 64 (.leaf 1587222029) (.leaf 1561177698)) (.branch 66 (.leaf 1535689567) (.leaf 1510740603)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1486314465) (.leaf 1462395473)) (.branch 70 (.leaf 1438968577) (.leaf 1416019324))) (.branch 73 (.branch 72 (.leaf 1393533835) (.leaf 1371498776)) (.branch 74 (.leaf 1349901329) (.leaf 1328729176))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1307970470) (.branch 77 (.leaf 1287613814) (.leaf 1267648243))) (.branch 80 (.branch 79 (.leaf 1248063204) (.leaf 1228848534)) (.branch 81 (.leaf 1209994447) (.leaf 1191491513)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1173330648) (.leaf 1155503090)) (.branch 85 (.leaf 1138000395) (.leaf 1120814413))) (.branch 88 (.branch 87 (.leaf 1103937284) (.leaf 1087361418)) (.branch 89 (.leaf 1071079490) (.leaf 1055084423)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1039369381) (.branch 92 (.leaf 1023927756) (.leaf 1008753162))) (.branch 95 (.branch 94 (.leaf 993839423) (.leaf 979180563)) (.branch 96 (.leaf 964770801) (.leaf 950604543)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 936676369) (.leaf 922981031)) (.branch 100 (.leaf 909513448) (.leaf 896268690))) (.branch 103 (.branch 102 (.leaf 883241982) (.leaf 870428692)) (.branch 104 (.leaf 857824328) (.leaf 845424530))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 833225067) (.leaf 821221832)) (.branch 108 (.leaf 809410834) (.leaf 797788200))) (.branch 111 (.branch 110 (.leaf 786350162) (.leaf 775093060)) (.branch 112 (.leaf 764013335) (.leaf 753107527)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 742372268) (.leaf 731804281)) (.branch 116 (.leaf 721400377) (.leaf 711157451))) (.branch 119 (.branch 118 (.leaf 701072478) (.leaf 691142513)) (.branch 120 (.leaf 681364685) (.leaf 671736196)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 115).prefactor = (193664209757339/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 115).cutoff/(generalMeanRows 115).c)).2 =
    (86812321510833/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 115).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 115).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 115).q*(generalMeanRows 115).c/2-2 = (43/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable048.value]
    have hcontinuation : (generalMeanRows 115).q*(generalMeanRows 115).cutoff/2-2 = (23/12:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable028.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 115).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 115

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 115).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 115).criticalRate j.val*(generalMeanRows 115).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 115).c*(generalMeanRows 115).criticalPoint j.val)).2-
      (generalMeanRows 115).J/2-(generalMeanRows 115).error (generalMeanGrid j.val)+
      (generalMeanRows 115).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 115).c)).2-
      (generalMeanRows 115).J/2-(generalMeanRows 115).error 4 := by
  have he : (generalMeanRows 115).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 115) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 115)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0115

/-! Kernel-checked entropy margins for general spectral rectangle 116. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0116
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6425742640) (.branch 2 (.leaf 6227282632) (.leaf 6037610727))) (.branch 5 (.branch 4 (.leaf 5856226320) (.leaf 5682663972)) (.branch 6 (.leaf 5516490326) (.leaf 5357301374)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5204720002) (.leaf 5058393799)) (.branch 10 (.leaf 4917993082) (.leaf 4783209116))) (.branch 13 (.branch 12 (.leaf 4653752508) (.leaf 4529351752)) (.branch 14 (.leaf 4409751902) (.leaf 4294713371))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4184010832) (.branch 17 (.leaf 4077432217) (.leaf 3974777794))) (.branch 20 (.branch 19 (.leaf 3875859332) (.leaf 3780499321)) (.branch 21 (.leaf 3688530262) (.leaf 3599794013)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3514141182) (.leaf 3431430569)) (.branch 25 (.leaf 3351528646) (.leaf 3274309081))) (.branch 28 (.branch 27 (.leaf 3199652294) (.leaf 3127445039)) (.branch 29 (.leaf 3057580027) (.leaf 2989955564)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2924475224) (.branch 32 (.leaf 2861047532) (.leaf 2799585683))) (.branch 35 (.branch 34 (.leaf 2740007267) (.leaf 2682234018)) (.branch 36 (.leaf 2626191580) (.leaf 2571809283)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2519019941) (.leaf 2467759653)) (.branch 40 (.leaf 2417967626) (.leaf 2369586002))) (.branch 43 (.branch 42 (.leaf 2322559700) (.leaf 2276836263)) (.branch 44 (.leaf 2232365722) (.leaf 2189100455))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2146995070) (.branch 47 (.leaf 2106006284) (.leaf 2066092811))) (.branch 50 (.branch 49 (.leaf 2027215261) (.leaf 1989336039)) (.branch 51 (.leaf 1952419254) (.leaf 1916430628)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1881337421) (.leaf 1847108344)) (.branch 55 (.leaf 1813713492) (.leaf 1781124272))) (.branch 58 (.branch 57 (.leaf 1749313336) (.leaf 1718254524)) (.branch 59 (.leaf 1687922799) (.leaf 1658294194))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1629345762) (.branch 62 (.leaf 1601055523) (.leaf 1573402419))) (.branch 65 (.branch 64 (.leaf 1546366266) (.leaf 1519927717)) (.branch 66 (.leaf 1494068217) (.leaf 1468769970)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1444015899) (.leaf 1419789613)) (.branch 70 (.leaf 1396075375) (.leaf 1372858073))) (.branch 73 (.branch 72 (.leaf 1350123189) (.leaf 1327856771)) (.branch 74 (.leaf 1306045407) (.leaf 1284676203))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1263736757) (.branch 77 (.leaf 1243215134) (.leaf 1223099850))) (.branch 80 (.branch 79 (.leaf 1203379849) (.leaf 1184044484)) (.branch 81 (.leaf 1165083498) (.leaf 1146487009)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1128245489) (.leaf 1110349755)) (.branch 85 (.leaf 1092790946) (.leaf 1075560517))) (.branch 88 (.branch 87 (.leaf 1058650220) (.leaf 1042052091)) (.branch 89 (.leaf 1025758441) (.leaf 1009761843)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 994055119) (.branch 92 (.leaf 978631333) (.leaf 963483778))) (.branch 95 (.branch 94 (.leaf 948605967) (.leaf 933991624)) (.branch 96 (.leaf 919634676) (.leaf 905529244)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 891669636) (.leaf 878050338)) (.branch 100 (.leaf 864666006) (.leaf 851511464))) (.branch 103 (.branch 102 (.leaf 838581690) (.leaf 825871817)) (.branch 104 (.leaf 813377122) (.leaf 801093023))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 789015073) (.leaf 777138953)) (.branch 108 (.leaf 765460470) (.leaf 753975550))) (.branch 111 (.branch 110 (.leaf 742680234) (.leaf 731570674)) (.branch 112 (.leaf 720643130) (.leaf 709893963)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 699319635) (.leaf 688916702)) (.branch 116 (.leaf 678681812) (.leaf 668611702))) (.branch 119 (.branch 118 (.leaf 658703195) (.leaf 648953195)) (.branch 120 (.leaf 639358688) (.leaf 629916735)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 116).prefactor = (5016985488396911/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 116).cutoff/(generalMeanRows 116).c)).2 =
    (212128803728773/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 116).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 116).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 116).q*(generalMeanRows 116).c/2-2 = (9/16:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable040.value]
    have hcontinuation : (generalMeanRows 116).q*(generalMeanRows 116).cutoff/2-2 = (23/12:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable028.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 116).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 116

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 116).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 116).criticalRate j.val*(generalMeanRows 116).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 116).c*(generalMeanRows 116).criticalPoint j.val)).2-
      (generalMeanRows 116).J/2-(generalMeanRows 116).error (generalMeanGrid j.val)+
      (generalMeanRows 116).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 116).c)).2-
      (generalMeanRows 116).J/2-(generalMeanRows 116).error 4 := by
  have he : (generalMeanRows 116).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 116) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 116)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0116

/-! Kernel-checked entropy margins for general spectral rectangle 117. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0117
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5971410656) (.branch 2 (.leaf 5767807456) (.leaf 5573346449))) (.branch 5 (.branch 4 (.leaf 5387510657) (.leaf 5209819291)) (.branch 6 (.leaf 5039824580) (.leaf 4877108957)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4721282529) (.leaf 4571980823)) (.branch 10 (.leaf 4428862754) (.leaf 4291608793))) (.branch 13 (.branch 12 (.leaf 4159919314) (.leaf 4033513094)) (.branch 14 (.leaf 3912125954) (.leaf 3795509520))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3683430095) (.branch 17 (.leaf 3575667627) (.leaf 3472014765))) (.branch 20 (.branch 19 (.leaf 3372275992) (.leaf 3276266834)) (.branch 21 (.leaf 3183813123) (.leaf 3094750330)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3008922936) (.leaf 2926183862)) (.branch 25 (.leaf 2846393939) (.leaf 2769421410))) (.branch 28 (.branch 27 (.leaf 2695141480) (.leaf 2623435889)) (.branch 29 (.leaf 2554192517) (.leaf 2487305023)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2422672495) (.branch 32 (.leaf 2360199143) (.leaf 2299793994))) (.branch 35 (.branch 34 (.leaf 2241370616) (.leaf 2184846865)) (.branch 36 (.leaf 2130144635) (.leaf 2077189640)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2025911193) (.leaf 1976242014)) (.branch 40 (.leaf 1928118040) (.leaf 1881478254))) (.branch 43 (.branch 42 (.leaf 1836264514) (.leaf 1792421405)) (.branch 44 (.leaf 1749896093) (.leaf 1708638185))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1668599605) (.branch 47 (.leaf 1629734468) (.leaf 1591998972))) (.branch 50 (.branch 49 (.leaf 1555351289) (.leaf 1519751460)) (.branch 51 (.leaf 1485161305) (.leaf 1451544330)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1418865641) (.leaf 1387091869)) (.branch 55 (.leaf 1356191088) (.leaf 1326132748))) (.branch 58 (.branch 57 (.leaf 1296887604) (.leaf 1268427654)) (.branch 59 (.leaf 1240726080) (.leaf 1213757186))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1187496349) (.branch 62 (.leaf 1161919963) (.leaf 1137005394))) (.branch 65 (.branch 64 (.leaf 1112730932) (.leaf 1089075750)) (.branch 66 (.leaf 1066019857) (.leaf 1043544066)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1021629950) (.leaf 1000259812)) (.branch 70 (.leaf 979416648) (.leaf 959084118))) (.branch 73 (.branch 72 (.leaf 939246514) (.leaf 919888731)) (.branch 74 (.leaf 900996241) (.leaf 882555067))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 864551758) (.branch 77 (.leaf 846973365) (.leaf 829807421))) (.branch 80 (.branch 79 (.leaf 813041917) (.leaf 796665285)) (.branch 81 (.leaf 780666376) (.leaf 765034442)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 749759124) (.leaf 734830426)) (.branch 85 (.leaf 720238709) (.leaf 705974670))) (.branch 88 (.branch 87 (.leaf 692029329) (.leaf 678394017)) (.branch 89 (.leaf 665060362) (.leaf 652020275)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 639265943) (.branch 92 (.leaf 626789813) (.leaf 614584584))) (.branch 95 (.branch 94 (.leaf 602643195) (.leaf 590958817)) (.branch 96 (.leaf 579524844) (.leaf 568334882)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 557382742) (.leaf 546662432)) (.branch 100 (.leaf 536168149) (.leaf 525894273))) (.branch 103 (.branch 102 (.leaf 515835356) (.leaf 505986121)) (.branch 104 (.leaf 496341451) (.leaf 486896385))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 477646110) (.leaf 468585961)) (.branch 108 (.leaf 459711407) (.leaf 451018054))) (.branch 111 (.branch 110 (.leaf 442501636) (.leaf 434158010)) (.branch 112 (.leaf 425983152) (.leaf 417973156)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 410124225) (.leaf 402432669)) (.branch 116 (.leaf 394894903) (.leaf 387507439))) (.branch 119 (.branch 118 (.leaf 380266889) (.leaf 373169954)) (.branch 120 (.leaf 366213428) (.leaf 359394191)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 117).prefactor = (5198718632074221/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 117).cutoff/(generalMeanRows 117).c)).2 =
    (183685116527747/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 117).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 117).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 117).q*(generalMeanRows 117).c/2-2 = (57/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable001.value]
    have hcontinuation : (generalMeanRows 117).q*(generalMeanRows 117).cutoff/2-2 = (23/12:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable028.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 117).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 117

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 117).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 117).criticalRate j.val*(generalMeanRows 117).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 117).c*(generalMeanRows 117).criticalPoint j.val)).2-
      (generalMeanRows 117).J/2-(generalMeanRows 117).error (generalMeanGrid j.val)+
      (generalMeanRows 117).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 117).c)).2-
      (generalMeanRows 117).J/2-(generalMeanRows 117).error 4 := by
  have he : (generalMeanRows 117).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 117) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 117)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0117

/-! Kernel-checked entropy margins for general spectral rectangle 118. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0118
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5910241478) (.branch 2 (.leaf 5725207862) (.leaf 5548479757))) (.branch 5 (.branch 4 (.leaf 5379576004) (.leaf 5218049571)) (.branch 6 (.leaf 5063484570) (.leaf 4915493605)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4773715396) (.leaf 4637812643)) (.branch 10 (.leaf 4507470112) (.leaf 4382392900))) (.branch 13 (.branch 12 (.leaf 4262304869) (.leaf 4146947229)) (.branch 14 (.leaf 4036077243) (.leaf 3929467057))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3826902624) (.branch 17 (.leaf 3728182727) (.leaf 3633118079))) (.branch 20 (.branch 19 (.leaf 3541530503) (.leaf 3453252174)) (.branch 21 (.leaf 3368124923) (.leaf 3285999596)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3206735465) (.leaf 3130199678)) (.branch 25 (.leaf 3056266758) (.leaf 2984818130))) (.branch 28 (.branch 27 (.leaf 2915741691) (.leaf 2848931405)) (.branch 29 (.leaf 2784286932) (.leaf 2721713278)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2661120470) (.branch 32 (.leaf 2602423258) (.leaf 2545540834))) (.branch 35 (.branch 34 (.leaf 2490396564) (.leaf 2436917752)) (.branch 36 (.leaf 2385035403) (.leaf 2334684018)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2285801383) (.leaf 2238328393)) (.branch 40 (.leaf 2192208869) (.leaf 2147389397))) (.branch 43 (.branch 42 (.leaf 2103819171) (.leaf 2061449852)) (.branch 44 (.leaf 2020235431) (.leaf 1980132099))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1941098131) (.branch 47 (.leaf 1903093770) (.leaf 1866081124))) (.branch 50 (.branch 49 (.leaf 1830024063) (.leaf 1794888130)) (.branch 51 (.leaf 1760640447) (.leaf 1727249635)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1694685737) (.leaf 1662920139)) (.branch 55 (.leaf 1631925507) (.leaf 1601675716))) (.branch 58 (.branch 57 (.leaf 1572145788) (.leaf 1543311840)) (.branch 59 (.leaf 1515151018) (.leaf 1487641456))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1460762217) (.branch 62 (.leaf 1434493254) (.leaf 1408815361))) (.branch 65 (.branch 64 (.leaf 1383710133) (.leaf 1359159927)) (.branch 66 (.leaf 1335147825) (.leaf 1311657597)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1288673669) (.leaf 1266181090)) (.branch 70 (.leaf 1244165507) (.leaf 1222613127))) (.branch 73 (.branch 72 (.leaf 1201510702) (.leaf 1180845492)) (.branch 74 (.leaf 1160605252) (.leaf 1140778198))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1121352995) (.branch 77 (.leaf 1102318731) (.leaf 1083664898))) (.branch 80 (.branch 79 (.leaf 1065381377) (.leaf 1047458413)) (.branch 81 (.leaf 1029886609) (.leaf 1012656900)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 995760544) (.leaf 979189106)) (.branch 85 (.leaf 962934445) (.leaf 946988698))) (.branch 88 (.branch 87 (.leaf 931344274) (.leaf 915993837)) (.branch 89 (.leaf 900930297) (.leaf 886146798)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 871636710) (.branch 92 (.leaf 857393620) (.leaf 843411321))) (.branch 95 (.branch 94 (.leaf 829683802) (.leaf 816205244)) (.branch 96 (.leaf 802970009) (.leaf 789972635)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 777207825) (.leaf 764670446)) (.branch 100 (.leaf 752355516) (.leaf 740258203))) (.branch 103 (.branch 102 (.leaf 728373818) (.leaf 716697807)) (.branch 104 (.leaf 705225749) (.leaf 693953348))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 682876433) (.leaf 671990944)) (.branch 108 (.leaf 661292940) (.leaf 650778585))) (.branch 111 (.branch 110 (.leaf 640444147) (.leaf 630285995)) (.branch 112 (.leaf 620300597) (.leaf 610484513)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 600834391) (.leaf 591346969)) (.branch 116 (.leaf 582019068) (.leaf 572847589))) (.branch 119 (.branch 118 (.leaf 563829511) (.leaf 554961889)) (.branch 120 (.leaf 546241852) (.leaf 537666598)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 118).prefactor = (2436595304069419/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 118).cutoff/(generalMeanRows 118).c)).2 =
    (218181552271223/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 118).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 118).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 118).q*(generalMeanRows 118).c/2-2 = (151/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable060.value]
    have hcontinuation : (generalMeanRows 118).q*(generalMeanRows 118).cutoff/2-2 = (71/35:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable023.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 118).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 118

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 118).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 118).criticalRate j.val*(generalMeanRows 118).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 118).c*(generalMeanRows 118).criticalPoint j.val)).2-
      (generalMeanRows 118).J/2-(generalMeanRows 118).error (generalMeanGrid j.val)+
      (generalMeanRows 118).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 118).c)).2-
      (generalMeanRows 118).J/2-(generalMeanRows 118).error 4 := by
  have he : (generalMeanRows 118).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 118) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 118)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0118

/-! Kernel-checked entropy margins for general spectral rectangle 119. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0119
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5376550384) (.branch 2 (.leaf 5188216485) (.leaf 5008502537))) (.branch 5 (.branch 4 (.leaf 4836913145) (.leaf 4672987880)) (.branch 6 (.leaf 4516298224) (.leaf 4366444853)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4223055197) (.leaf 4085781263)) (.branch 10 (.leaf 3954297665) (.leaf 3828299852))) (.branch 13 (.branch 12 (.leaf 3707502505) (.leaf 3591638085)) (.branch 14 (.leaf 3480455509) (.leaf 3373718952))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3271206747) (.branch 17 (.leaf 3172710381) (.leaf 3078033582))) (.branch 20 (.branch 19 (.leaf 2986991476) (.leaf 2899409809)) (.branch 21 (.leaf 2815124241) (.leaf 2733979689)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2655829721) (.leaf 2580536001)) (.branch 25 (.leaf 2507967766) (.leaf 2438001355))) (.branch 28 (.branch 27 (.leaf 2370519760) (.leaf 2305412219)) (.branch 29 (.leaf 2242573829) (.leaf 2181905194)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2123312095) (.branch 32 (.leaf 2066705176) (.leaf 2011999666))) (.branch 35 (.branch 34 (.leaf 1959115102) (.leaf 1907975083)) (.branch 36 (.leaf 1858507039) (.leaf 1810642006)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1764314424) (.leaf 1719461950)) (.branch 40 (.leaf 1676025271) (.leaf 1633947941))) (.branch 43 (.branch 42 (.leaf 1593176220) (.leaf 1553658929)) (.branch 44 (.leaf 1515347310) (.leaf 1478194891))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1442157372) (.branch 47 (.leaf 1407192501) (.leaf 1373259970))) (.branch 50 (.branch 49 (.leaf 1340321311) (.leaf 1308339801)) (.branch 51 (.leaf 1277280372) (.leaf 1247109521)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1217795234) (.leaf 1189306911)) (.branch 55 (.leaf 1161615288) (.leaf 1134692376))) (.branch 58 (.branch 57 (.leaf 1108511393) (.leaf 1083046706)) (.branch 59 (.leaf 1058273773) (.leaf 1034169088))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1010710134) (.branch 62 (.leaf 987875329) (.leaf 965643986))) (.branch 65 (.branch 64 (.leaf 943996266) (.leaf 922913139)) (.branch 66 (.leaf 902376347) (.leaf 882368364)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 862872362) (.leaf 843872181)) (.branch 70 (.leaf 825352295) (.leaf 807297784))) (.branch 73 (.branch 72 (.leaf 789694307) (.leaf 772528071)) (.branch 74 (.leaf 755785811) (.leaf 739454764))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 723522646) (.branch 77 (.leaf 707977632) (.leaf 692808332))) (.branch 80 (.branch 79 (.leaf 678003778) (.leaf 663553398)) (.branch 81 (.leaf 649447005) (.leaf 635674775)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 622227236) (.leaf 609095249)) (.branch 85 (.leaf 596269996) (.leaf 583742966))) (.branch 88 (.branch 87 (.leaf 571505942) (.leaf 559550987)) (.branch 89 (.leaf 547870436) (.leaf 536456880)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 525303161) (.branch 92 (.leaf 514402355) (.leaf 503747769))) (.branch 95 (.branch 94 (.leaf 493332927) (.leaf 483151565)) (.branch 96 (.leaf 473197620) (.leaf 463465220)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 453948684) (.leaf 444642506)) (.branch 100 (.leaf 435541354) (.leaf 426640059))) (.branch 103 (.branch 102 (.leaf 417933614) (.leaf 409417162)) (.branch 104 (.leaf 401085995) (.leaf 392935546))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 384961384) (.leaf 377159210)) (.branch 108 (.leaf 369524852) (.leaf 362054257))) (.branch 111 (.branch 110 (.leaf 354743493) (.leaf 347588740)) (.branch 112 (.leaf 340586286) (.leaf 333732525)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 327023954) (.leaf 320457167)) (.branch 116 (.leaf 314028852) (.leaf 307735789))) (.branch 119 (.branch 118 (.leaf 301574848) (.leaf 295542982)) (.branch 120 (.leaf 289637227) (.leaf 283854699)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 119).prefactor = (5029788580087083/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 119).cutoff/(generalMeanRows 119).c)).2 =
    (74768549512223/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 119).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 119).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 119).q*(generalMeanRows 119).c/2-2 = (193/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable071.value]
    have hcontinuation : (generalMeanRows 119).q*(generalMeanRows 119).cutoff/2-2 = (71/35:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable023.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 119).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 119

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 119).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 119).criticalRate j.val*(generalMeanRows 119).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 119).c*(generalMeanRows 119).criticalPoint j.val)).2-
      (generalMeanRows 119).J/2-(generalMeanRows 119).error (generalMeanGrid j.val)+
      (generalMeanRows 119).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 119).c)).2-
      (generalMeanRows 119).J/2-(generalMeanRows 119).error 4 := by
  have he : (generalMeanRows 119).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 119) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 119)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0119

/-! Kernel-checked entropy margins for general spectral rectangle 120. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0120
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5485764531) (.branch 2 (.leaf 5315271471) (.leaf 5152510854))) (.branch 5 (.branch 4 (.leaf 4997025473) (.leaf 4848390996)) (.branch 6 (.leaf 4706213099) (.leaf 4570124903)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4439784677) (.leaf 4314873781)) (.branch 10 (.leaf 4195094808) (.leaf 4080169906))) (.branch 13 (.branch 12 (.leaf 3969839264) (.leaf 3863859729)) (.branch 14 (.leaf 3762003563) (.leaf 3664057297))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3569820693) (.branch 17 (.leaf 3479105792) (.leaf 3391736046))) (.branch 20 (.branch 19 (.leaf 3307545513) (.leaf 3226378132)) (.branch 21 (.leaf 3148087041) (.leaf 3072533956)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2999588603) (.leaf 2929128183)) (.branch 25 (.leaf 2861036886) (.leaf 2795205434))) (.branch 28 (.branch 27 (.leaf 2731530668) (.leaf 2669915152)) (.branch 29 (.leaf 2610266817) (.leaf 2552498625)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2496528251) (.branch 32 (.leaf 2442277804) (.leaf 2389673547))) (.branch 35 (.branch 34 (.leaf 2338645648) (.leaf 2289127948)) (.branch 36 (.leaf 2241057739) (.leaf 2194375560)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2149025008) (.leaf 2104952553)) (.branch 40 (.leaf 2062107380) (.leaf 2020441225))) (.branch 43 (.branch 42 (.leaf 1979908232) (.leaf 1940464814)) (.branch 44 (.leaf 1902069528) (.leaf 1864682949))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1828267562) (.branch 47 (.leaf 1792787651) (.leaf 1758209203))) (.branch 50 (.branch 49 (.leaf 1724499814) (.leaf 1691628599)) (.branch 51 (.leaf 1659566110) (.leaf 1628284259)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1597756244) (.leaf 1567956483)) (.branch 55 (.leaf 1538860543) (.leaf 1510445084))) (.branch 58 (.branch 57 (.leaf 1482687802) (.leaf 1455567372)) (.branch 59 (.leaf 1429063395) (.leaf 1403156359))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1377827581) (.branch 62 (.leaf 1353059176) (.leaf 1328834009))) (.branch 65 (.branch 64 (.leaf 1305135658) (.leaf 1281948381)) (.branch 66 (.leaf 1259257081) (.leaf 1237047272)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1215305049) (.leaf 1194017061)) (.branch 70 (.leaf 1173170484) (.leaf 1152752994))) (.branch 73 (.branch 72 (.leaf 1132752743) (.leaf 1113158336)) (.branch 74 (.leaf 1093958811) (.leaf 1075143617))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1056702594) (.branch 77 (.leaf 1038625956) (.leaf 1020904273))) (.branch 80 (.branch 79 (.leaf 1003528455) (.leaf 986489735)) (.branch 81 (.leaf 969779658) (.leaf 953390059)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 937313061) (.leaf 921541051)) (.branch 85 (.leaf 906066676) (.leaf 890882830))) (.branch 88 (.branch 87 (.leaf 875982639) (.leaf 861359456)) (.branch 89 (.leaf 847006850) (.leaf 832918594)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 819088661) (.branch 92 (.leaf 805511209) (.leaf 792180582))) (.branch 95 (.branch 94 (.leaf 779091293) (.leaf 766238025)) (.branch 96 (.leaf 753615618) (.leaf 741219068)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 729043516) (.leaf 717084244)) (.branch 100 (.leaf 705336671) (.leaf 693796346))) (.branch 103 (.branch 102 (.leaf 682458943) (.leaf 671320256)) (.branch 104 (.leaf 660376197) (.leaf 649622786))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 639056153) (.leaf 628672532)) (.branch 108 (.leaf 618468255) (.leaf 608439750))) (.branch 111 (.branch 110 (.leaf 598583539) (.leaf 588896231)) (.branch 112 (.leaf 579374523) (.leaf 570015195)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 560815107) (.leaf 551771195)) (.branch 116 (.leaf 542880472) (.leaf 534140023))) (.branch 119 (.branch 118 (.leaf 525547002) (.leaf 517098631)) (.branch 120 (.leaf 508792198) (.leaf 500625054)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 120).prefactor = (293025346125431/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 120).cutoff/(generalMeanRows 120).c)).2 =
    (230511400641093/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 120).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 120).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 120).q*(generalMeanRows 120).c/2-2 = (311/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable072.value]
    have hcontinuation : (generalMeanRows 120).q*(generalMeanRows 120).cutoff/2-2 = (561/260:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable073.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 120).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 120

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 120).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 120).criticalRate j.val*(generalMeanRows 120).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 120).c*(generalMeanRows 120).criticalPoint j.val)).2-
      (generalMeanRows 120).J/2-(generalMeanRows 120).error (generalMeanGrid j.val)+
      (generalMeanRows 120).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 120).c)).2-
      (generalMeanRows 120).J/2-(generalMeanRows 120).error 4 := by
  have he : (generalMeanRows 120).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 120) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 120)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0120

/-! Kernel-checked entropy margins for general spectral rectangle 121. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0121
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5340085109) (.branch 2 (.leaf 5165464128) (.leaf 4998822031))) (.branch 5 (.branch 4 (.leaf 4839689180) (.leaf 4687629625)) (.branch 6 (.leaf 4542238167) (.leaf 4403137730)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4269977013) (.leaf 4142428376)) (.branch 10 (.leaf 4020185939) (.leaf 3902963863))) (.branch 13 (.branch 12 (.leaf 3790494796) (.leaf 3682528466)) (.branch 14 (.leaf 3578830393) (.leaf 3479180730))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3383373189) (.branch 17 (.leaf 3291214073) (.leaf 3202521382))) (.branch 20 (.branch 19 (.leaf 3117123995) (.leaf 3034860921)) (.branch 21 (.leaf 2955580604) (.leaf 2879140291)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2805405441) (.leaf 2734249187)) (.branch 25 (.leaf 2665551831) (.leaf 2599200385))) (.branch 28 (.branch 27 (.leaf 2535088136) (.leaf 2473114253)) (.branch 29 (.leaf 2413183415) (.leaf 2355205467)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2299095102) (.branch 32 (.leaf 2244771564) (.leaf 2192158371))) (.branch 35 (.branch 34 (.leaf 2141183056) (.leaf 2091776930)) (.branch 36 (.leaf 2043874854) (.leaf 1997415031)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1952338811) (.leaf 1908590507)) (.branch 40 (.leaf 1866117223) (.leaf 1824868697))) (.branch 43 (.branch 42 (.leaf 1784797147) (.leaf 1745857133)) (.branch 44 (.leaf 1708005425) (.leaf 1671200877))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1635404315) (.branch 47 (.leaf 1600578425) (.leaf 1566687651))) (.branch 50 (.branch 49 (.leaf 1533698101) (.leaf 1501577456)) (.branch 51 (.leaf 1470294882) (.leaf 1439820957)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1410127587) (.leaf 1381187944)) (.branch 55 (.leaf 1352976394) (.leaf 1325468435))) (.branch 58 (.branch 57 (.leaf 1298640641) (.leaf 1272470602)) (.branch 59 (.leaf 1246936876) (.leaf 1222018935))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1197697122) (.branch 62 (.leaf 1173952606) (.leaf 1150767338))) (.branch 65 (.branch 64 (.leaf 1128124016) (.leaf 1106006044)) (.branch 66 (.leaf 1084397501) (.leaf 1063283104)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1042648178) (.leaf 1022478627)) (.branch 70 (.leaf 1002760909) (.leaf 983482002))) (.branch 73 (.branch 72 (.leaf 964629387) (.leaf 946191019)) (.branch 74 (.leaf 928155307) (.leaf 910511092))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 893247627) (.branch 77 (.leaf 876354561) (.leaf 859821913))) (.branch 80 (.branch 79 (.leaf 843640064) (.leaf 827799736)) (.branch 81 (.leaf 812291976) (.leaf 797108146)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 782239903) (.leaf 767679191)) (.branch 85 (.leaf 753418226) (.leaf 739449484))) (.branch 88 (.branch 87 (.leaf 725765692) (.leaf 712359815)) (.branch 89 (.leaf 699225047) (.leaf 686354801)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 673742700) (.branch 92 (.leaf 661382570) (.leaf 649268428))) (.branch 95 (.branch 94 (.leaf 637394476) (.leaf 625755095)) (.branch 96 (.leaf 614344837) (.leaf 603158417)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 592190706) (.leaf 581436730)) (.branch 100 (.leaf 570891656) (.leaf 560550794))) (.branch 103 (.branch 102 (.leaf 550409587) (.leaf 540463608)) (.branch 104 (.leaf 530708554) (.leaf 521140242))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 511754605) (.leaf 502547687)) (.branch 108 (.leaf 493515639) (.leaf 484654717))) (.branch 111 (.branch 110 (.leaf 475961274) (.leaf 467431762)) (.branch 112 (.leaf 459062724) (.leaf 450850795)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 442792694) (.leaf 434885225)) (.branch 116 (.leaf 427125273) (.leaf 419509802))) (.branch 119 (.branch 118 (.leaf 412035850) (.leaf 404700529)) (.branch 120 (.leaf 397501022) (.leaf 390434581)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 121).prefactor = (4821857200164489/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 121).cutoff/(generalMeanRows 121).c)).2 =
    (435047314878927/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 121).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 121).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 121).q*(generalMeanRows 121).c/2-2 = (691/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable054.value]
    have hcontinuation : (generalMeanRows 121).q*(generalMeanRows 121).cutoff/2-2 = (561/260:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable073.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 121).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 121

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 121).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 121).criticalRate j.val*(generalMeanRows 121).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 121).c*(generalMeanRows 121).criticalPoint j.val)).2-
      (generalMeanRows 121).J/2-(generalMeanRows 121).error (generalMeanGrid j.val)+
      (generalMeanRows 121).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 121).c)).2-
      (generalMeanRows 121).J/2-(generalMeanRows 121).error 4 := by
  have he : (generalMeanRows 121).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 121) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 121)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0121

/-! Kernel-checked entropy margins for general spectral rectangle 122. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0122
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5461276245) (.branch 2 (.leaf 5288716809) (.leaf 5124067258))) (.branch 5 (.branch 4 (.leaf 4966855542) (.leaf 4816643759)) (.branch 6 (.leaf 4673025173) (.leaf 4535621550)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4404080772) (.leaf 4278074692)) (.branch 10 (.leaf 4157297200) (.leaf 4041462478))) (.branch 13 (.branch 12 (.leaf 3930303422) (.leaf 3823570205)) (.branch 14 (.leaf 3721028975) (.leaf 3622460666))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3527659919) (.branch 17 (.leaf 3436434085) (.leaf 3348602321))) (.branch 20 (.branch 19 (.leaf 3263994760) (.leaf 3182451742)) (.branch 21 (.leaf 3103823116) (.leaf 3027967590)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2954752135) (.leaf 2884051435)) (.branch 25 (.leaf 2815747374) (.leaf 2749728574))) (.branch 28 (.branch 27 (.leaf 2685889947) (.leaf 2624132300)) (.branch 29 (.leaf 2564361958) (.leaf 2506490412)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2450433998) (.branch 32 (.leaf 2396113599) (.leaf 2343454358))) (.branch 35 (.branch 34 (.leaf 2292385423) (.leaf 2242839702)) (.branch 36 (.leaf 2194753634) (.leaf 2148066982)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2102722630) (.leaf 2058666402)) (.branch 40 (.leaf 2015846889) (.leaf 1974215287))) (.branch 43 (.branch 42 (.leaf 1933725243) (.leaf 1894332721)) (.branch 44 (.leaf 1855995861) (.leaf 1818674861))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1782331856) (.branch 47 (.leaf 1746930815) (.leaf 1712437432))) (.branch 50 (.branch 49 (.leaf 1678819032) (.leaf 1646044484)) (.branch 51 (.leaf 1614084113) (.leaf 1582909618)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1552494005) (.leaf 1522811507)) (.branch 55 (.leaf 1493837526) (.leaf 1465548565))) (.branch 58 (.branch 57 (.leaf 1437922172) (.leaf 1410936885)) (.branch 59 (.leaf 1384572177) (.leaf 1358808411))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1333626792) (.branch 62 (.leaf 1309009324) (.leaf 1284938766))) (.branch 65 (.branch 64 (.leaf 1261398600) (.leaf 1238372985)) (.branch 66 (.leaf 1215846733) (.leaf 1193805267)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1172234598) (.leaf 1151121292)) (.branch 70 (.leaf 1130452441) (.leaf 1110215642))) (.branch 73 (.branch 72 (.leaf 1090398969) (.leaf 1070990951)) (.branch 74 (.leaf 1051980550) (.leaf 1033357140))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1015110490) (.branch 77 (.leaf 997230740) (.leaf 979708389))) (.branch 80 (.branch 79 (.leaf 962534276) (.leaf 945699565)) (.branch 81 (.leaf 929195728) (.leaf 913014535)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 897148036) (.leaf 881588554)) (.branch 85 (.leaf 866328667) (.leaf 851361200))) (.branch 88 (.branch 87 (.leaf 836679213) (.leaf 822275994)) (.branch 89 (.leaf 808145043) (.leaf 794280070)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 780674980) (.branch 92 (.leaf 767323869) (.leaf 754221013))) (.branch 95 (.branch 94 (.leaf 741360865) (.leaf 728738043)) (.branch 96 (.leaf 716347323) (.leaf 704183639)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 692242070) (.leaf 680517838)) (.branch 100 (.leaf 669006300) (.leaf 657702944))) (.branch 103 (.branch 102 (.leaf 646603386) (.leaf 635703360)) (.branch 104 (.leaf 624998719) (.leaf 614485427))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 604159558) (.leaf 594017287)) (.branch 108 (.leaf 584054891) (.leaf 574268745))) (.branch 111 (.branch 110 (.leaf 564655315) (.leaf 555211159)) (.branch 112 (.leaf 545932920) (.leaf 536817327)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 527861188) (.leaf 519061391)) (.branch 116 (.leaf 510414899) (.leaf 501918749))) (.branch 119 (.branch 118 (.leaf 493570046) (.leaf 485365967)) (.branch 120 (.leaf 477303754) (.leaf 469380713)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 122).prefactor = (4824746620357339/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 122).cutoff/(generalMeanRows 122).c)).2 =
    (116216975880073/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 122).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 122).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 122).q*(generalMeanRows 122).c/2-2 = (129/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable064.value]
    have hcontinuation : (generalMeanRows 122).q*(generalMeanRows 122).cutoff/2-2 = (2270/1027:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable074.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 122).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 122

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 122).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 122).criticalRate j.val*(generalMeanRows 122).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 122).c*(generalMeanRows 122).criticalPoint j.val)).2-
      (generalMeanRows 122).J/2-(generalMeanRows 122).error (generalMeanGrid j.val)+
      (generalMeanRows 122).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 122).c)).2-
      (generalMeanRows 122).J/2-(generalMeanRows 122).error 4 := by
  have he : (generalMeanRows 122).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 122) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 122)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0122

/-! Kernel-checked entropy margins for general spectral rectangle 123. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0123
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5238343031) (.branch 2 (.leaf 5064271117) (.leaf 4898243501))) (.branch 5 (.branch 4 (.leaf 4739782198) (.leaf 4588443714)) (.branch 6 (.leaf 4443816036) (.leaf 4305515941)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4173186588) (.leaf 4046495344)) (.branch 10 (.leaf 3925131844) (.leaf 3808806218))) (.branch 13 (.branch 12 (.leaf 3697247503) (.leaf 3590202190)) (.branch 14 (.leaf 3487432912) (.leaf 3388717244))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3293846609) (.branch 17 (.leaf 3202625278) (.leaf 3114869454))) (.branch 20 (.branch 19 (.leaf 3030406435) (.leaf 2949073838)) (.branch 21 (.leaf 2870718895) (.leaf 2795197797)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2722375092) (.leaf 2652123130)) (.branch 25 (.leaf 2584321549) (.leaf 2518856800))) (.branch 28 (.branch 27 (.leaf 2455621707) (.leaf 2394515059)) (.branch 29 (.leaf 2335441231) (.leaf 2278309833)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2223035385) (.branch 32 (.leaf 2169537010) (.leaf 2117738153))) (.branch 35 (.branch 34 (.leaf 2067566321) (.leaf 2018952831)) (.branch 36 (.leaf 1971832585) (.leaf 1926143858)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1881828093) (.leaf 1838829721)) (.branch 40 (.leaf 1797095982) (.leaf 1756576763))) (.branch 43 (.branch 42 (.leaf 1717224449) (.leaf 1678993772)) (.branch 44 (.leaf 1641841688) (.leaf 1605727241))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1570611454) (.branch 47 (.leaf 1536457213) (.leaf 1503229165))) (.branch 50 (.branch 49 (.leaf 1470893624) (.leaf 1439418472)) (.branch 51 (.leaf 1408773084) (.leaf 1378928237)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1349856042) (.leaf 1321529866)) (.branch 55 (.leaf 1293924272) (.leaf 1267014950))) (.branch 58 (.branch 57 (.leaf 1240778661) (.leaf 1215193180)) (.branch 59 (.leaf 1190237242) (.leaf 1165890495))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1142133451) (.branch 62 (.leaf 1118947443) (.leaf 1096314581))) (.branch 65 (.branch 64 (.leaf 1074217717) (.leaf 1052640406)) (.branch 66 (.leaf 1031566867) (.leaf 1010981957)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 990871134) (.leaf 971220431)) (.branch 70 (.leaf 952016427) (.leaf 933246219))) (.branch 73 (.branch 72 (.leaf 914897400) (.leaf 896958034)) (.branch 74 (.leaf 879416634) (.leaf 862262140))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 845483900) (.branch 77 (.leaf 829071650) (.leaf 813015500))) (.branch 80 (.branch 79 (.leaf 797305909) (.leaf 781933680)) (.branch 81 (.leaf 766889933) (.leaf 752166101)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 737753908) (.leaf 723645362)) (.branch 85 (.leaf 709832741) (.leaf 696308577))) (.branch 88 (.branch 87 (.leaf 683065653) (.leaf 670096985)) (.branch 89 (.leaf 657395817) (.leaf 644955609)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 632770028) (.branch 92 (.leaf 620832941) (.leaf 609138405))) (.branch 95 (.branch 94 (.leaf 597680661) (.leaf 586454124)) (.branch 96 (.leaf 575453381) (.leaf 564673179)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 554108419) (.leaf 543754156)) (.branch 100 (.leaf 533605584) (.leaf 523658040))) (.branch 103 (.branch 102 (.leaf 513906990) (.leaf 504348031)) (.branch 104 (.leaf 494976884) (.leaf 485789385))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 476781488) (.leaf 467949257)) (.branch 108 (.leaf 459288861) (.leaf 450796573))) (.branch 111 (.branch 110 (.leaf 442468764) (.leaf 434301901)) (.branch 112 (.leaf 426292545) (.leaf 418437343)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 410733030) (.leaf 403176425)) (.branch 116 (.leaf 395764426) (.leaf 388494009))) (.branch 119 (.branch 118 (.leaf 381362227) (.leaf 374366203)) (.branch 120 (.leaf 367503134) (.leaf 360770282)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 123).prefactor = (4890802433776187/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 123).cutoff/(generalMeanRows 123).c)).2 =
    (439115407417877/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 123).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 123).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 123).q*(generalMeanRows 123).c/2-2 = (357/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable067.value]
    have hcontinuation : (generalMeanRows 123).q*(generalMeanRows 123).cutoff/2-2 = (2270/1027:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable074.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 123).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 123

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 123).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 123).criticalRate j.val*(generalMeanRows 123).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 123).c*(generalMeanRows 123).criticalPoint j.val)).2-
      (generalMeanRows 123).J/2-(generalMeanRows 123).error (generalMeanGrid j.val)+
      (generalMeanRows 123).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 123).c)).2-
      (generalMeanRows 123).J/2-(generalMeanRows 123).error 4 := by
  have he : (generalMeanRows 123).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 123) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 123)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0123

/-! Kernel-checked entropy margins for general spectral rectangle 124. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0124
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5130781347) (.branch 2 (.leaf 4954850701) (.leaf 4787035127))) (.branch 5 (.branch 4 (.leaf 4626858596) (.leaf 4473879140)) (.branch 6 (.leaf 4327685884) (.leaf 4187896393)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4054154290) (.leaf 3926127130)) (.branch 10 (.leaf 3803504470) (.leaf 3685996136))) (.branch 13 (.branch 12 (.leaf 3573330655) (.leaf 3465253825)) (.branch 14 (.leaf 3361527422) (.leaf 3261928025))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3166245930) (.branch 17 (.leaf 3074284175) (.leaf 2985857635))) (.branch 20 (.branch 19 (.leaf 2900792195) (.leaf 2818923995)) (.branch 21 (.leaf 2740098726) (.leaf 2664170994)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2591003721) (.leaf 2520467601)) (.branch 25 (.leaf 2452440593) (.leaf 2386807454))) (.branch 28 (.branch 27 (.leaf 2323459302) (.leaf 2262293216)) (.branch 29 (.leaf 2203211865) (.leaf 2146123155)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2090939911) (.branch 32 (.leaf 2037579577) (.leaf 1985963933))) (.branch 35 (.branch 34 (.leaf 1936018840) (.leaf 1887673991)) (.branch 36 (.leaf 1840862689) (.leaf 1795521631)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1751590715) (.leaf 1709012853)) (.branch 40 (.leaf 1667733794) (.leaf 1627701969))) (.branch 43 (.branch 42 (.leaf 1588868333) (.leaf 1551186227)) (.branch 44 (.leaf 1514611243) (.leaf 1479101098))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1444615519) (.branch 47 (.leaf 1411116130) (.leaf 1378566352))) (.branch 50 (.branch 49 (.leaf 1346931302) (.leaf 1316177703)) (.branch 51 (.leaf 1286273799) (.leaf 1257189276)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1228895178) (.leaf 1201363847)) (.branch 55 (.leaf 1174568843) (.leaf 1148484891))) (.branch 58 (.branch 57 (.leaf 1123087815) (.leaf 1098354485)) (.branch 59 (.leaf 1074262759) (.leaf 1050791438))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1027920216) (.branch 62 (.leaf 1005629635) (.leaf 983901043))) (.branch 65 (.branch 64 (.leaf 962716557) (.leaf 942059019)) (.branch 66 (.leaf 921911967) (.leaf 902259597)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 883086733) (.leaf 864378796)) (.branch 70 (.leaf 846121776) (.leaf 828302207))) (.branch 73 (.branch 72 (.leaf 810907136) (.leaf 793924104)) (.branch 74 (.leaf 777341123) (.leaf 761146651))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 745329573) (.branch 77 (.leaf 729879182) (.leaf 714785162))) (.branch 80 (.branch 79 (.leaf 700037566) (.leaf 685626804)) (.branch 81 (.leaf 671543626) (.leaf 657779104)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 644324622) (.leaf 631171863)) (.branch 85 (.leaf 618312789) (.leaf 605739638))) (.branch 88 (.branch 87 (.leaf 593444908) (.leaf 581421343)) (.branch 89 (.leaf 569661931) (.leaf 558159885)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 546908639) (.branch 92 (.leaf 535901838) (.leaf 525133329))) (.branch 95 (.branch 94 (.leaf 514597152) (.leaf 504287535)) (.branch 96 (.leaf 494198882) (.leaf 484325771)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 474662945) (.leaf 465205304)) (.branch 100 (.leaf 455947903) (.leaf 446885941))) (.branch 103 (.branch 102 (.leaf 438014762) (.leaf 429329841)) (.branch 104 (.leaf 420826788) (.leaf 412501338))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 404349347) (.leaf 396366788)) (.branch 108 (.leaf 388549746) (.leaf 380894418))) (.branch 111 (.branch 110 (.leaf 373397103) (.leaf 366054202)) (.branch 112 (.leaf 358862215) (.leaf 351817735)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 344917447) (.leaf 338158124)) (.branch 116 (.leaf 331536624) (.leaf 325049889))) (.branch 119 (.branch 118 (.leaf 318694937) (.leaf 312468866)) (.branch 120 (.leaf 306368849) (.leaf 300392128)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 124).prefactor = (2445000408566259/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 124).cutoff/(generalMeanRows 124).c)).2 =
    (102432376723659/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 124).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 124).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 124).q*(generalMeanRows 124).c/2-2 = (19/25:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable075.value]
    have hcontinuation : (generalMeanRows 124).q*(generalMeanRows 124).cutoff/2-2 = (561/260:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable073.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 124).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 124

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 124).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 124).criticalRate j.val*(generalMeanRows 124).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 124).c*(generalMeanRows 124).criticalPoint j.val)).2-
      (generalMeanRows 124).J/2-(generalMeanRows 124).error (generalMeanGrid j.val)+
      (generalMeanRows 124).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 124).c)).2-
      (generalMeanRows 124).J/2-(generalMeanRows 124).error 4 := by
  have he : (generalMeanRows 124).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 124) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 124)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0124

/-! Kernel-checked entropy margins for general spectral rectangle 125. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0125
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4934475022) (.branch 2 (.leaf 4757598825) (.leaf 4588971681))) (.branch 5 (.branch 4 (.leaf 4428110781) (.leaf 4274567782)) (.branch 6 (.leaf 4127925795) (.leaf 3987796711)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3853818788) (.leaf 3725654500)) (.branch 10 (.leaf 3602988592) (.leaf 3485526321))) (.branch 13 (.branch 12 (.leaf 3372991872) (.leaf 3265126915)) (.branch 14 (.leaf 3161689300) (.leaf 3062451857))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2967201313) (.branch 17 (.leaf 2875737299) (.leaf 2787871434))) (.branch 20 (.branch 19 (.leaf 2703426493) (.leaf 2622235639)) (.branch 21 (.leaf 2544141719) (.leaf 2468996610)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2396660624) (.leaf 2327001953)) (.branch 25 (.leaf 2259896156) (.leaf 2195225688))) (.branch 28 (.branch 27 (.leaf 2132879460) (.leaf 2072752431)) (.branch 29 (.leaf 2014745233) (.leaf 1958763819)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1904719136) (.branch 32 (.leaf 1852526823) (.leaf 1802106929))) (.branch 35 (.branch 34 (.leaf 1753383645) (.leaf 1706285064)) (.branch 36 (.leaf 1660742947) (.leaf 1616692512)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1574072231) (.leaf 1532823647)) (.branch 40 (.leaf 1492891193) (.leaf 1454222031))) (.branch 43 (.branch 42 (.leaf 1416765899) (.leaf 1380474965)) (.branch 44 (.leaf 1345303696) (.leaf 1311208724))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1278148734) (.branch 47 (.leaf 1246084349) (.leaf 1214978025))) (.branch 50 (.branch 49 (.leaf 1184793954) (.leaf 1155497969)) (.branch 51 (.leaf 1127057460) (.leaf 1099441287)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1072619709) (.leaf 1046564306)) (.branch 55 (.leaf 1021247912) (.leaf 996644552))) (.branch 58 (.branch 57 (.leaf 972729379) (.leaf 949478618)) (.branch 59 (.leaf 926869510) (.leaf 904880264))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 883490005) (.branch 62 (.leaf 862678731) (.leaf 842427269))) (.branch 65 (.branch 64 (.leaf 822717236) (.leaf 803530997)) (.branch 66 (.leaf 784851632) (.leaf 766662899)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 748949204) (.leaf 731695570)) (.branch 70 (.leaf 714887606) (.leaf 698511479))) (.branch 73 (.branch 72 (.leaf 682553892) (.leaf 667002055)) (.branch 74 (.leaf 651843665) (.leaf 637066879))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 622660298) (.branch 77 (.leaf 608612945) (.leaf 594914246))) (.branch 80 (.branch 79 (.leaf 581554011) (.leaf 568522420)) (.branch 81 (.leaf 555810003) (.leaf 543407627)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 531306483) (.leaf 519498067)) (.branch 85 (.leaf 507974171) (.leaf 496726870))) (.branch 88 (.branch 87 (.leaf 485748509) (.leaf 475031693)) (.branch 89 (.leaf 464569274) (.leaf 454354343)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 444380219) (.branch 92 (.leaf 434640440) (.leaf 425128754))) (.branch 95 (.branch 94 (.leaf 415839112) (.leaf 406765658)) (.branch 96 (.leaf 397902723) (.leaf 389244814)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 380786613) (.leaf 372522967)) (.branch 100 (.leaf 364448879) (.leaf 356559509))) (.branch 103 (.branch 102 (.leaf 348850162) (.leaf 341316283)) (.branch 104 (.leaf 333953456) (.leaf 326757396))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 319723944) (.leaf 312849061)) (.branch 108 (.leaf 306128829) (.leaf 299559441))) (.branch 111 (.branch 110 (.leaf 293137200) (.leaf 286858515)) (.branch 112 (.leaf 280719895) (.leaf 274717950)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 268849383) (.leaf 263110988)) (.branch 116 (.leaf 257499650) (.leaf 252012337))) (.branch 119 (.branch 118 (.leaf 246646102) (.leaf 241398075)) (.branch 120 (.leaf 236265467) (.leaf 231245561)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 125).prefactor = (4959107455679313/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 125).cutoff/(generalMeanRows 125).c)).2 =
    (192518447152133/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 125).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 125).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 125).q*(generalMeanRows 125).c/2-2 = (829/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable068.value]
    have hcontinuation : (generalMeanRows 125).q*(generalMeanRows 125).cutoff/2-2 = (561/260:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable073.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 125).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 125

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 125).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 125).criticalRate j.val*(generalMeanRows 125).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 125).c*(generalMeanRows 125).criticalPoint j.val)).2-
      (generalMeanRows 125).J/2-(generalMeanRows 125).error (generalMeanGrid j.val)+
      (generalMeanRows 125).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 125).c)).2-
      (generalMeanRows 125).J/2-(generalMeanRows 125).error 4 := by
  have he : (generalMeanRows 125).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 125) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 125)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0125

/-! Kernel-checked entropy margins for general spectral rectangle 126. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0126
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5120656556) (.branch 2 (.leaf 4945006331) (.leaf 4777526176))) (.branch 5 (.branch 4 (.leaf 4617731727) (.leaf 4465173517)) (.branch 6 (.leaf 4319433922) (.leaf 4180124447)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4046883285) (.leaf 3919373124)) (.branch 10 (.leaf 3797279178) (.leaf 3680307401))) (.branch 13 (.branch 12 (.leaf 3568182877) (.leaf 3460648350)) (.branch 14 (.leaf 3357462902) (.leaf 3258400734))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3163250065) (.branch 17 (.leaf 3071812116) (.leaf 2983900188))) (.branch 20 (.branch 19 (.leaf 2899338814) (.leaf 2817962973)) (.branch 21 (.leaf 2739617382) (.leaf 2664155829)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2591440567) (.leaf 2521341750)) (.branch 25 (.leaf 2453736918) (.leaf 2388510511))) (.branch 28 (.branch 27 (.leaf 2325553430) (.leaf 2264762619)) (.branch 29 (.leaf 2206040685) (.leaf 2149295545)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2094440091) (.branch 32 (.leaf 2041391887) (.leaf 1990072880))) (.branch 35 (.branch 34 (.leaf 1940409136) (.leaf 1892330590)) (.branch 36 (.leaf 1845770818) (.leaf 1800666816)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1756958800) (.leaf 1714590020)) (.branch 40 (.leaf 1673506580) (.leaf 1633657276))) (.branch 43 (.branch 42 (.leaf 1594993438) (.leaf 1557468791)) (.branch 44 (.leaf 1521039313) (.leaf 1485663112))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1451300308) (.branch 47 (.leaf 1417912918) (.leaf 1385464752))) (.branch 50 (.branch 49 (.leaf 1353921317) (.leaf 1323249720)) (.branch 51 (.leaf 1293418587) (.leaf 1264397975)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1236159302) (.leaf 1208675266)) (.branch 55 (.leaf 1181919788) (.leaf 1155867937))) (.branch 58 (.branch 57 (.leaf 1130495877) (.leaf 1105780809)) (.branch 59 (.leaf 1081700914) (.leaf 1058235306))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1035363985) (.branch 62 (.leaf 1013067789) (.leaf 991328355))) (.branch 65 (.branch 64 (.leaf 970128074) (.leaf 949450060)) (.branch 66 (.leaf 929278111) (.leaf 909596674)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 890390816) (.leaf 871646192)) (.branch 70 (.leaf 853349018) (.leaf 835486043))) (.branch 73 (.branch 72 (.leaf 818044524) (.leaf 801012204)) (.branch 74 (.leaf 784377286) (.leaf 768128413))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 752254648) (.branch 77 (.leaf 736745454) (.leaf 721590677))) (.branch 80 (.branch 79 (.leaf 706780527) (.leaf 692305563)) (.branch 81 (.leaf 678156676) (.leaf 664325075)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 650802274) (.leaf 637580079)) (.branch 85 (.leaf 624650571) (.leaf 612006100))) (.branch 88 (.branch 87 (.leaf 599639269) (.leaf 587542927)) (.branch 89 (.leaf 575710155) (.leaf 564134261)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 552808764) (.branch 92 (.leaf 541727392) (.leaf 530884070))) (.branch 95 (.branch 94 (.leaf 520272912) (.leaf 509888215)) (.branch 96 (.leaf 499724450) (.leaf 489776258)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 480038438) (.leaf 470505948)) (.branch 100 (.leaf 461173893) (.leaf 452037523))) (.branch 103 (.branch 102 (.leaf 443092225) (.leaf 434333519)) (.branch 104 (.leaf 425757055) (.leaf 417358604))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 409134058) (.leaf 401079423)) (.branch 108 (.leaf 393190815) (.leaf 385464456))) (.branch 111 (.branch 110 (.leaf 377896674) (.leaf 370483894)) (.branch 112 (.leaf 363222636) (.leaf 356109515)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 349141234) (.leaf 342314582)) (.branch 116 (.leaf 335626435) (.leaf 329073745))) (.branch 119 (.branch 118 (.leaf 322653546) (.leaf 316362947)) (.branch 120 (.leaf 310199128) (.leaf 304159343)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 126).prefactor = (4957762620176619/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 126).cutoff/(generalMeanRows 126).c)).2 =
    (52788536137687/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 126).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 126).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 126).q*(generalMeanRows 126).c/2-2 = (19/25:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable075.value]
    have hcontinuation : (generalMeanRows 126).q*(generalMeanRows 126).cutoff/2-2 = (2270/1027:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable074.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 126).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 126

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 126).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 126).criticalRate j.val*(generalMeanRows 126).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 126).c*(generalMeanRows 126).criticalPoint j.val)).2-
      (generalMeanRows 126).J/2-(generalMeanRows 126).error (generalMeanGrid j.val)+
      (generalMeanRows 126).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 126).c)).2-
      (generalMeanRows 126).J/2-(generalMeanRows 126).error 4 := by
  have he : (generalMeanRows 126).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 126) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 126)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0126

/-! Kernel-checked entropy margins for general spectral rectangle 127. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0127
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5190763685) (.branch 2 (.leaf 5012708625) (.leaf 4842935492))) (.branch 5 (.branch 4 (.leaf 4680953291) (.leaf 4526306399)) (.branch 6 (.leaf 4378571477) (.leaf 4237354711)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4102289338) (.leaf 3973033430)) (.branch 10 (.leaf 3849267891) (.leaf 3730694648))) (.branch 13 (.branch 12 (.leaf 3617035022) (.leaf 3508028235)) (.branch 14 (.leaf 3403430071) (.leaf 3303011639))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3206558258) (.branch 17 (.leaf 3113868428) (.leaf 3024752894))) (.branch 20 (.branch 19 (.leaf 2939033786) (.leaf 2856543826)) (.branch 21 (.leaf 2777125602) (.leaf 2700630901)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2626920091) (.leaf 2555861548)) (.branch 25 (.leaf 2487331135) (.leaf 2421211711))) (.branch 28 (.branch 27 (.leaf 2357392682) (.leaf 2295769581)) (.branch 29 (.leaf 2236243683) (.leaf 2178721643)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2123115161) (.branch 32 (.leaf 2069340671) (.leaf 2017319053))) (.branch 35 (.branch 34 (.leaf 1966975361) (.leaf 1918238570)) (.branch 36 (.leaf 1871041346) (.leaf 1825319823)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1781013398) (.leaf 1738064546)) (.branch 40 (.leaf 1696418631) (.leaf 1656023748))) (.branch 43 (.branch 42 (.leaf 1616830562) (.leaf 1578792163)) (.branch 44 (.leaf 1541863927) (.leaf 1506003390))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1471170123) (.branch 47 (.leaf 1437325625) (.leaf 1404433210))) (.branch 50 (.branch 49 (.leaf 1372457912) (.leaf 1341366389)) (.branch 51 (.leaf 1311126836) (.leaf 1281708902)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1253083612) (.leaf 1225223291)) (.branch 55 (.leaf 1198101502) (.leaf 1171692974))) (.branch 58 (.branch 57 (.leaf 1145973545) (.leaf 1120920101)) (.branch 59 (.leaf 1096510527) (.leaf 1072723651))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1049539198) (.branch 62 (.leaf 1026937744) (.leaf 1004900674))) (.branch 65 (.branch 64 (.leaf 983410139) (.leaf 962449022)) (.branch 66 (.leaf 942000898) (.leaf 922050001)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 902581195) (.leaf 883579938)) (.branch 70 (.leaf 865032256) (.leaf 846924718))) (.branch 73 (.branch 72 (.leaf 829244407) (.leaf 811978897)) (.branch 74 (.leaf 795116229) (.leaf 778644892))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 762553799) (.branch 77 (.leaf 746832268) (.leaf 731470006))) (.branch 80 (.branch 79 (.leaf 716457090) (.leaf 701783948)) (.branch 81 (.leaf 687441348) (.leaf 673420378)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 659712436) (.leaf 646309215)) (.branch 85 (.leaf 633202689) (.leaf 620385101))) (.branch 88 (.branch 87 (.leaf 607848956) (.leaf 595587002)) (.branch 89 (.leaf 583592228) (.leaf 571857847)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 560377293) (.branch 92 (.leaf 549144205) (.leaf 538152427))) (.branch 95 (.branch 94 (.leaf 527395991) (.leaf 516869117)) (.branch 96 (.leaf 506566199) (.leaf 496481806)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 486610665) (.leaf 476947665)) (.branch 100 (.leaf 467487845) (.leaf 458226388))) (.branch 103 (.branch 102 (.leaf 449158619) (.leaf 440279998)) (.branch 104 (.leaf 431586113) (.leaf 423072679))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 414735530) (.leaf 406570618)) (.branch 108 (.leaf 398574007) (.leaf 390741867))) (.branch 111 (.branch 110 (.leaf 383070474) (.leaf 375556205)) (.branch 112 (.leaf 368195533) (.leaf 360985025)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 353921341) (.leaf 347001226)) (.branch 116 (.leaf 340221511) (.leaf 333579108))) (.branch 119 (.branch 118 (.leaf 327071010) (.leaf 320694286)) (.branch 120 (.leaf 314446078) (.leaf 308323601)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 127).prefactor = (5025639561368001/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 127).cutoff/(generalMeanRows 127).c)).2 =
    (52788536137687/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 127).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 127).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 127).q*(generalMeanRows 127).c/2-2 = (19/25:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable075.value]
    have hcontinuation : (generalMeanRows 127).q*(generalMeanRows 127).cutoff/2-2 = (2270/1027:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable074.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 127).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 127

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 127).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 127).criticalRate j.val*(generalMeanRows 127).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 127).c*(generalMeanRows 127).criticalPoint j.val)).2-
      (generalMeanRows 127).J/2-(generalMeanRows 127).error (generalMeanGrid j.val)+
      (generalMeanRows 127).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 127).c)).2-
      (generalMeanRows 127).J/2-(generalMeanRows 127).error 4 := by
  have he : (generalMeanRows 127).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 127) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 127)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0127

/-! Kernel-checked entropy margins for general spectral rectangle 128. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0128
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5281364298) (.branch 2 (.leaf 5112238450) (.leaf 4950854357))) (.branch 5 (.branch 4 (.leaf 4796750770) (.leaf 4649499829)) (.branch 6 (.leaf 4508704145) (.leaf 4373994195)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4245025983) (.leaf 4121478944)) (.branch 10 (.leaf 4003054054) (.leaf 3889472116))) (.branch 13 (.branch 12 (.leaf 3780472220) (.leaf 3675810338)) (.branch 14 (.leaf 3575258046) (.leaf 3478601365))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3385639702) (.branch 17 (.leaf 3296184875) (.leaf 3210060233))) (.branch 20 (.branch 19 (.leaf 3127099837) (.leaf 3047147715)) (.branch 21 (.leaf 2970057173) (.leaf 2895690167)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2823916713) (.leaf 2754614352)) (.branch 25 (.leaf 2687667654) (.leaf 2622967755))) (.branch 28 (.branch 27 (.leaf 2560411933) (.leaf 2499903212)) (.branch 29 (.leaf 2441349995) (.leaf 2384665726)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2329768572) (.branch 32 (.leaf 2276581132) (.leaf 2225030160))) (.branch 35 (.branch 34 (.leaf 2175046313) (.leaf 2126563913)) (.branch 36 (.leaf 2079520724) (.leaf 2033857751)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1989519038) (.leaf 1946451500)) (.branch 40 (.leaf 1904604742) (.leaf 1863930913))) (.branch 43 (.branch 42 (.leaf 1824384551) (.leaf 1785922448)) (.branch 44 (.leaf 1748503522) (.leaf 1712088693))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1676640775) (.branch 47 (.leaf 1642124363) (.leaf 1608505738))) (.branch 50 (.branch 49 (.leaf 1575752771) (.leaf 1543834839)) (.branch 51 (.leaf 1512722738) (.leaf 1482388605)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1452805851) (.leaf 1423949087)) (.branch 55 (.leaf 1395794062) (.leaf 1368317600))) (.branch 58 (.branch 57 (.leaf 1341497548) (.leaf 1315312717)) (.branch 59 (.leaf 1289742833) (.leaf 1264768491))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1240371109) (.branch 62 (.leaf 1216532885) (.leaf 1193236757))) (.branch 65 (.branch 64 (.leaf 1170466369) (.leaf 1148206031)) (.branch 66 (.leaf 1126440685) (.leaf 1105155879)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1084337732) (.leaf 1063972908)) (.branch 70 (.leaf 1044048590) (.leaf 1024552452))) (.branch 73 (.branch 72 (.leaf 1005472638) (.leaf 986797738)) (.branch 74 (.leaf 968516768) (.leaf 950619150))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 933094690) (.branch 77 (.leaf 915933564) (.leaf 899126300))) (.branch 80 (.branch 79 (.leaf 882663759) (.leaf 866537123)) (.branch 81 (.leaf 850737879) (.leaf 835257807)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 820088963) (.leaf 805223673)) (.branch 85 (.leaf 790654514) (.leaf 776374310))) (.branch 88 (.branch 87 (.leaf 762376116) (.leaf 748653211)) (.branch 89 (.leaf 735199087) (.leaf 722007442)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 709072169) (.branch 92 (.leaf 696387350) (.leaf 683947246))) (.branch 95 (.branch 94 (.leaf 671746293) (.leaf 659779092)) (.branch 96 (.leaf 648040403) (.leaf 636525140)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 625228364) (.leaf 614145278)) (.branch 100 (.leaf 603271219) (.leaf 592601658))) (.branch 103 (.branch 102 (.leaf 582132189) (.leaf 571858528)) (.branch 104 (.leaf 561776509) (.leaf 551882077))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 542171287) (.leaf 532640296)) (.branch 108 (.leaf 523285365) (.leaf 514102848))) (.branch 111 (.branch 110 (.leaf 505089197) (.leaf 496240952)) (.branch 112 (.leaf 487554742) (.leaf 479027279)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 470655359) (.leaf 462435854)) (.branch 116 (.leaf 454365714) (.leaf 446441964))) (.branch 119 (.branch 118 (.leaf 438661699) (.leaf 431022084)) (.branch 120 (.leaf 423520351) (.leaf 416153795)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 128).prefactor = (4769753592239139/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 128).cutoff/(generalMeanRows 128).c)).2 =
    (228659234859217/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 128).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 128).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 128).q*(generalMeanRows 128).c/2-2 = (271/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable076.value]
    have hcontinuation : (generalMeanRows 128).q*(generalMeanRows 128).cutoff/2-2 = (223/100:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable077.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 128).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 128

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 128).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 128).criticalRate j.val*(generalMeanRows 128).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 128).c*(generalMeanRows 128).criticalPoint j.val)).2-
      (generalMeanRows 128).J/2-(generalMeanRows 128).error (generalMeanGrid j.val)+
      (generalMeanRows 128).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 128).c)).2-
      (generalMeanRows 128).J/2-(generalMeanRows 128).error 4 := by
  have he : (generalMeanRows 128).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 128) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 128)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0128

/-! Kernel-checked entropy margins for general spectral rectangle 129. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0129
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5351588233) (.branch 2 (.leaf 5180213594) (.leaf 5016683649))) (.branch 5 (.branch 4 (.leaf 4860531015) (.leaf 4711322145)) (.branch 6 (.leaf 4568654364) (.leaf 4432153236)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4301470191) (.leaf 4176280403)) (.branch 10 (.leaf 4056280870) (.leaf 3941188684))) (.branch 13 (.branch 12 (.leaf 3830739466) (.leaf 3724685941)) (.branch 14 (.leaf 3622796650) (.leaf 3524854769))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3430657036) (.branch 17 (.leaf 3340012768) (.leaf 3252742965))) (.branch 20 (.branch 19 (.leaf 3168679482) (.leaf 3087664272)) (.branch 21 (.leaf 3009548693) (.leaf 2934192862)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2861465068) (.leaf 2791241225)) (.branch 25 (.leaf 2723404366) (.leaf 2657844182))) (.branch 28 (.branch 27 (.leaf 2594456583) (.leaf 2533143305)) (.branch 29 (.leaf 2473811532) (.leaf 2416373557)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2360746461) (.branch 32 (.leaf 2306851811) (.leaf 2254615389))) (.branch 35 (.branch 34 (.leaf 2203966929) (.leaf 2154839880)) (.branch 36 (.leaf 2107171180) (.leaf 2060901046)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2015972782) (.leaf 1972332593)) (.branch 40 (.leaf 1929929418) (.leaf 1888714767))) (.branch 43 (.branch 42 (.leaf 1848642575) (.leaf 1809669059)) (.branch 44 (.leaf 1771752590) (.leaf 1734853570))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1698934316) (.branch 47 (.leaf 1663958955) (.leaf 1629893318))) (.branch 50 (.branch 49 (.leaf 1596704850) (.leaf 1564362520)) (.branch 51 (.leaf 1532836734) (.leaf 1502099262)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1472123160) (.leaf 1442882700)) (.branch 55 (.leaf 1414353310) (.leaf 1386511506))) (.branch 58 (.branch 57 (.leaf 1359334840) (.leaf 1332801841)) (.branch 59 (.leaf 1306891965) (.leaf 1281585551))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1256863768) (.branch 62 (.leaf 1232708577) (.leaf 1209102692))) (.branch 65 (.branch 64 (.leaf 1186029536) (.leaf 1163473212)) (.branch 66 (.leaf 1141418462) (.leaf 1119850641)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1098755685) (.leaf 1078120079)) (.branch 70 (.leaf 1057930836) (.leaf 1038175467))) (.branch 73 (.branch 72 (.leaf 1018841957) (.leaf 999918745)) (.branch 74 (.leaf 981394701) (.leaf 963259106))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 945501632) (.branch 77 (.leaf 928112323) (.leaf 911081580))) (.branch 80 (.branch 79 (.leaf 894400144) (.leaf 878059079)) (.branch 81 (.leaf 862049760) (.leaf 846363856)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 830993319) (.leaf 815930371)) (.branch 85 (.leaf 801167493) (.leaf 786697412))) (.branch 88 (.branch 87 (.leaf 772513090) (.leaf 758607717)) (.branch 89 (.leaf 744974700) (.leaf 731607651)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 718500384) (.branch 92 (.leaf 705646900) (.leaf 693041386))) (.branch 95 (.branch 94 (.leaf 680678202) (.leaf 668551879)) (.branch 96 (.leaf 656657106) (.leaf 644988729)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 633541746) (.leaf 622311292)) (.branch 100 (.leaf 611292646) (.leaf 600481216))) (.branch 103 (.branch 102 (.leaf 589872539) (.leaf 579462275)) (.branch 104 (.leaf 569246200) (.leaf 559220206))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 549380296) (.leaf 539722576)) (.branch 108 (.leaf 530243256) (.leaf 520938643))) (.branch 111 (.branch 110 (.leaf 511805142) (.leaf 502839246)) (.branch 112 (.leaf 494037539) (.leaf 485396690)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 476913452) (.leaf 468584656)) (.branch 116 (.leaf 460407211) (.leaf 452378103))) (.branch 119 (.branch 118 (.leaf 444494388) (.leaf 436753192)) (.branch 120 (.leaf 429151711) (.leaf 421687206)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 129).prefactor = (302073429287381/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 129).cutoff/(generalMeanRows 129).c)).2 =
    (228659234859217/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 129).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 129).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 129).q*(generalMeanRows 129).c/2-2 = (271/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable076.value]
    have hcontinuation : (generalMeanRows 129).q*(generalMeanRows 129).cutoff/2-2 = (223/100:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable077.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 129).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 129

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 129).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 129).criticalRate j.val*(generalMeanRows 129).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 129).c*(generalMeanRows 129).criticalPoint j.val)).2-
      (generalMeanRows 129).J/2-(generalMeanRows 129).error (generalMeanGrid j.val)+
      (generalMeanRows 129).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 129).c)).2-
      (generalMeanRows 129).J/2-(generalMeanRows 129).error 4 := by
  have he : (generalMeanRows 129).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 129) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 129)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0129

/-! Kernel-checked entropy margins for general spectral rectangle 130. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0130
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5203884046) (.branch 2 (.leaf 5028924302) (.leaf 4862046675))) (.branch 5 (.branch 4 (.leaf 4702771539) (.leaf 4550653896)) (.branch 6 (.leaf 4405280350) (.leaf 4266266405)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4133254046) (.leaf 4005909559)) (.branch 10 (.leaf 3883921570) (.leaf 3766999281))) (.branch 13 (.branch 12 (.leaf 3654870859) (.leaf 3547281988)) (.branch 14 (.leaf 3443994544) (.leaf 3344785392))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3249445286) (.branch 17 (.leaf 3157777867) (.leaf 3069598741))) (.branch 20 (.branch 19 (.leaf 2984734638) (.leaf 2903022636)) (.branch 21 (.leaf 2824309450) (.leaf 2748450775)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2675310685) (.leaf 2604761071)) (.branch 25 (.leaf 2536681127) (.leaf 2470956876))) (.branch 28 (.branch 27 (.leaf 2407480724) (.leaf 2346151054)) (.branch 29 (.leaf 2286871845) (.leaf 2229552320)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2174106618) (.branch 32 (.leaf 2120453494) (.leaf 2068516026))) (.branch 35 (.branch 34 (.leaf 2018221362) (.leaf 1969500466)) (.branch 36 (.leaf 1922287892) (.leaf 1876521572)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1832142611) (.leaf 1789095104)) (.branch 40 (.leaf 1747325962) (.leaf 1706784746))) (.branch 43 (.branch 42 (.leaf 1667423516) (.leaf 1629196687)) (.branch 44 (.leaf 1592060898) (.leaf 1555974881))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1520899351) (.branch 47 (.leaf 1486796888) (.leaf 1453631836))) (.branch 50 (.branch 49 (.leaf 1421370211) (.leaf 1389979600)) (.branch 51 (.leaf 1359429085) (.leaf 1329689154)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1300731632) (.leaf 1272529605)) (.branch 55 (.leaf 1245057358) (.leaf 1218290305))) (.branch 58 (.branch 57 (.leaf 1192204935) (.leaf 1166778755)) (.branch 59 (.leaf 1141990236) (.leaf 1117818764))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1094244596) (.branch 62 (.leaf 1071248809) (.leaf 1048813265))) (.branch 65 (.branch 64 (.leaf 1026920570) (.leaf 1005554034)) (.branch 66 (.leaf 984697641) (.leaf 964336011)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 944454373) (.leaf 925038532)) (.branch 70 (.leaf 906074844) (.leaf 887550188))) (.branch 73 (.branch 72 (.leaf 869451940) (.leaf 851767955)) (.branch 74 (.leaf 834486536) (.leaf 817596422))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 801086759) (.branch 77 (.leaf 784947090) (.leaf 769167331))) (.branch 80 (.branch 79 (.leaf 753737756) (.leaf 738648980)) (.branch 81 (.leaf 723891947) (.leaf 709457911)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 695338425) (.leaf 681525329)) (.branch 85 (.leaf 668010733) (.leaf 654787012))) (.branch 88 (.branch 87 (.leaf 641846788) (.leaf 629182927)) (.branch 89 (.leaf 616788520) (.leaf 604656881)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 592781535) (.branch 92 (.leaf 581156209) (.leaf 569774825))) (.branch 95 (.branch 94 (.leaf 558631491) (.leaf 547720495)) (.branch 96 (.leaf 537036295) (.leaf 526573518)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 516326947) (.leaf 506291518)) (.branch 100 (.leaf 496462317) (.leaf 486834568))) (.branch 103 (.branch 102 (.leaf 477403633) (.leaf 468165005)) (.branch 104 (.leaf 459114304) (.leaf 450247271))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 441559765) (.leaf 433047757)) (.branch 108 (.leaf 424707330) (.leaf 416534670))) (.branch 111 (.branch 110 (.leaf 408526064) (.leaf 400677901)) (.branch 112 (.leaf 392986662) (.leaf 385448920)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 378061338) (.leaf 370820662)) (.branch 116 (.leaf 363723725) (.leaf 356767437))) (.branch 119 (.branch 118 (.leaf 349948787) (.leaf 343264839)) (.branch 120 (.leaf 336712729) (.leaf 330289664)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 130).prefactor = (2481279243487107/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 130).cutoff/(generalMeanRows 130).c)).2 =
    (432420918096707/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 130).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 130).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 130).q*(generalMeanRows 130).c/2-2 = (149/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable078.value]
    have hcontinuation : (generalMeanRows 130).q*(generalMeanRows 130).cutoff/2-2 = (223/100:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable077.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 130).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 130

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 130).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 130).criticalRate j.val*(generalMeanRows 130).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 130).c*(generalMeanRows 130).criticalPoint j.val)).2-
      (generalMeanRows 130).J/2-(generalMeanRows 130).error (generalMeanGrid j.val)+
      (generalMeanRows 130).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 130).c)).2-
      (generalMeanRows 130).J/2-(generalMeanRows 130).error 4 := by
  have he : (generalMeanRows 130).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 130) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 130)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0130

/-! Kernel-checked entropy margins for general spectral rectangle 131. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0131
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5310744673) (.branch 2 (.leaf 5138024557) (.leaf 4973294197))) (.branch 5 (.branch 4 (.leaf 4816073139) (.leaf 4665915932)) (.branch 6 (.leaf 4522409060) (.leaf 4385168210)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4253835817) (.leaf 4128078860)) (.branch 10 (.leaf 4007586870) (.leaf 3892070142))) (.branch 13 (.branch 12 (.leaf 3781258104) (.leaf 3674897843)) (.branch 14 (.leaf 3572752767) (.leaf 3474601380))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3380236167) (.branch 17 (.leaf 3289462581) (.leaf 3202098102))) (.branch 20 (.branch 19 (.leaf 3117971390) (.leaf 3036921493)) (.branch 21 (.leaf 2958797130) (.leaf 2883456023)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2810764287) (.leaf 2740595864)) (.branch 25 (.leaf 2672832001) (.leaf 2607360767))) (.branch 28 (.branch 27 (.leaf 2544076608) (.leaf 2482879930)) (.branch 29 (.leaf 2423676719) (.leaf 2366378183)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2310900420) (.branch 32 (.leaf 2257164115) (.leaf 2205094249))) (.branch 35 (.branch 34 (.leaf 2154619837) (.leaf 2105673680)) (.branch 36 (.leaf 2058192130) (.leaf 2012114880)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1967384759) (.leaf 1923947549)) (.branch 40 (.leaf 1881751805) (.leaf 1840748694))) (.branch 43 (.branch 42 (.leaf 1800891841) (.leaf 1762137188)) (.branch 44 (.leaf 1724442857) (.leaf 1687769025))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1652077809) (.branch 47 (.leaf 1617333155) (.leaf 1583500732))) (.branch 50 (.branch 49 (.leaf 1550547838) (.leaf 1518443309)) (.branch 51 (.leaf 1487157434) (.leaf 1456661872)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1426929580) (.leaf 1397934744)) (.branch 55 (.leaf 1369652706) (.leaf 1342059908))) (.branch 58 (.branch 57 (.leaf 1315133831) (.leaf 1288852940)) (.branch 59 (.leaf 1263196632) (.leaf 1238145185))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1213679718) (.branch 62 (.leaf 1189782139) (.leaf 1166435112))) (.branch 65 (.branch 64 (.leaf 1143622015) (.leaf 1121326904)) (.branch 66 (.leaf 1099534477) (.leaf 1078230045)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1057399500) (.leaf 1037029287)) (.branch 70 (.leaf 1017106376) (.leaf 997618234))) (.branch 73 (.branch 72 (.leaf 978552808) (.leaf 959898493)) (.branch 74 (.leaf 941644118) (.leaf 923778922))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 906292535) (.branch 77 (.leaf 889174959) (.leaf 872416553))) (.branch 80 (.branch 79 (.leaf 856008015) (.leaf 839940366)) (.branch 81 (.leaf 824204939) (.leaf 808793359)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 793697534) (.leaf 778909645)) (.branch 85 (.leaf 764422126) (.leaf 750227662))) (.branch 88 (.branch 87 (.leaf 736319171) (.leaf 722689800)) (.branch 89 (.leaf 709332910) (.leaf 696242071)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 683411051) (.branch 92 (.leaf 670833810) (.leaf 658504490))) (.branch 95 (.branch 94 (.leaf 646417408) (.leaf 634567051)) (.branch 96 (.leaf 622948066) (.leaf 611555258)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 600383578) (.leaf 589428123)) (.branch 100 (.leaf 578684129) (.leaf 568146963))) (.branch 103 (.branch 102 (.leaf 557812122) (.leaf 547675224)) (.branch 104 (.leaf 537732007) (.leaf 527978323))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 518410137) (.leaf 509023516)) (.branch 108 (.leaf 499814634) (.leaf 490779760))) (.branch 111 (.branch 110 (.leaf 481915262) (.leaf 473217600)) (.branch 112 (.leaf 464683321) (.leaf 456309061)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 448091538) (.leaf 440027552)) (.branch 116 (.leaf 432113980) (.leaf 424347775))) (.branch 119 (.branch 118 (.leaf 416725963) (.leaf 409245642)) (.branch 120 (.leaf 401903977) (.leaf 394698202)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 131).prefactor = (4955029358518013/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 131).cutoff/(generalMeanRows 131).c)).2 =
    (461529002254777/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 131).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 131).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 131).q*(generalMeanRows 131).c/2-2 = (7/10:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable043.value]
    have hcontinuation : (generalMeanRows 131).q*(generalMeanRows 131).cutoff/2-2 = (902/395:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable079.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 131).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 131

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 131).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 131).criticalRate j.val*(generalMeanRows 131).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 131).c*(generalMeanRows 131).criticalPoint j.val)).2-
      (generalMeanRows 131).J/2-(generalMeanRows 131).error (generalMeanGrid j.val)+
      (generalMeanRows 131).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 131).c)).2-
      (generalMeanRows 131).J/2-(generalMeanRows 131).error 4 := by
  have he : (generalMeanRows 131).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 131) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 131)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0131

/-! Kernel-checked entropy margins for general spectral rectangle 132. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0132
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5186058434) (.branch 2 (.leaf 5011811344) (.leaf 4845675386))) (.branch 5 (.branch 4 (.leaf 4687164092) (.leaf 4535826365)) (.branch 6 (.leaf 4391243390) (.leaf 4253025868)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4120811535) (.leaf 3994262933)) (.branch 10 (.leaf 3873065408) (.leaf 3756925288))) (.branch 13 (.branch 12 (.leaf 3645568247) (.leaf 3538737812)) (.branch 14 (.leaf 3436194009) (.leaf 3337712130))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3243081605) (.branch 17 (.leaf 3152104976) (.leaf 3064596951))) (.branch 20 (.branch 19 (.leaf 2980383543) (.leaf 2899301277)) (.branch 21 (.leaf 2821196460) (.leaf 2745924508)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2673349331) (.leaf 2603342761)) (.branch 25 (.leaf 2535784022) (.leaf 2470559248))) (.branch 28 (.branch 27 (.leaf 2407561025) (.leaf 2346687979)) (.branch 29 (.leaf 2287844387) (.leaf 2230939813)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2175888781) (.branch 32 (.leaf 2122610459) (.leaf 2071028373))) (.branch 35 (.branch 34 (.leaf 2021070137) (.leaf 1972667205)) (.branch 36 (.leaf 1925754634) (.leaf 1880270869)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1836157539) (.leaf 1793359269)) (.branch 40 (.leaf 1751823501) (.leaf 1711500329))) (.branch 43 (.branch 42 (.leaf 1672342347) (.leaf 1634304499)) (.branch 44 (.leaf 1597343947) (.leaf 1561419946))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1526493719) (.branch 47 (.leaf 1492528353) (.leaf 1459488688))) (.branch 50 (.branch 49 (.leaf 1427341223) (.leaf 1396054024)) (.branch 51 (.leaf 1365596636) (.leaf 1335940002)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1307056389) (.leaf 1278919313)) (.branch 55 (.leaf 1251503476) (.leaf 1224784700))) (.branch 58 (.branch 57 (.leaf 1198739867) (.leaf 1173346867)) (.branch 59 (.leaf 1148584539) (.leaf 1124432628))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1100871733) (.branch 62 (.leaf 1077883267) (.leaf 1055449413))) (.branch 65 (.branch 64 (.leaf 1033553086) (.leaf 1012177894)) (.branch 66 (.leaf 991308108) (.leaf 970928625)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 951024937) (.leaf 931583106)) (.branch 70 (.leaf 912589730) (.leaf 894031923))) (.branch 73 (.branch 72 (.leaf 875897288) (.leaf 858173891)) (.branch 74 (.leaf 840850243) (.leaf 823915278))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 807358333) (.branch 77 (.leaf 791169128) (.leaf 775337751))) (.branch 80 (.branch 79 (.leaf 759854640) (.leaf 744710568)) (.branch 81 (.leaf 729896624) (.leaf 715404206)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 701225002) (.leaf 687350978)) (.branch 85 (.leaf 673774368) (.leaf 660487661))) (.branch 88 (.branch 87 (.leaf 647483591) (.leaf 634755126)) (.branch 89 (.leaf 622295457) (.leaf 610097992)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 598156344) (.branch 92 (.leaf 586464323) (.leaf 575015931))) (.branch 95 (.branch 94 (.leaf 563805351) (.leaf 552826940)) (.branch 96 (.leaf 542075225) (.leaf 531544894)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 521230788) (.leaf 511127901)) (.branch 100 (.leaf 501231368) (.leaf 491536464))) (.branch 103 (.branch 102 (.leaf 482038596) (.leaf 472733299)) (.branch 104 (.leaf 463616235) (.leaf 454683180))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 445930028) (.leaf 437352784)) (.branch 108 (.leaf 428947559) (.leaf 420710567))) (.branch 111 (.branch 110 (.leaf 412638123) (.leaf 404726637)) (.branch 112 (.leaf 396972612) (.leaf 389372642)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 381923407) (.leaf 374621672)) (.branch 116 (.leaf 367464283) (.leaf 360448164))) (.branch 119 (.branch 118 (.leaf 353570316) (.leaf 346827815)) (.branch 120 (.leaf 340217806) (.leaf 333737506)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 132).prefactor = (1003782245482211/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 132).cutoff/(generalMeanRows 132).c)).2 =
    (27812481268973/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 132).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 132).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 132).q*(generalMeanRows 132).c/2-2 = (149/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable078.value]
    have hcontinuation : (generalMeanRows 132).q*(generalMeanRows 132).cutoff/2-2 = (902/395:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable079.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 132).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 132

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 132).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 132).criticalRate j.val*(generalMeanRows 132).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 132).c*(generalMeanRows 132).criticalPoint j.val)).2-
      (generalMeanRows 132).J/2-(generalMeanRows 132).error (generalMeanGrid j.val)+
      (generalMeanRows 132).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 132).c)).2-
      (generalMeanRows 132).J/2-(generalMeanRows 132).error 4 := by
  have he : (generalMeanRows 132).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 132) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 132)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0132

/-! Kernel-checked entropy margins for general spectral rectangle 133. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0133
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5161777078) (.branch 2 (.leaf 4988277572) (.leaf 4822823779))) (.branch 5 (.branch 4 (.leaf 4664935712) (.leaf 4514168156)) (.branch 6 (.leaf 4370107635) (.leaf 4232369693)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4100596461) (.leaf 3974454466)) (.branch 10 (.leaf 3853632665) (.leaf 3737840659))) (.branch 13 (.branch 12 (.leaf 3626807085) (.leaf 3520278151)) (.branch 14 (.leaf 3418016306) (.leaf 3319799032))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3225417736) (.branch 17 (.leaf 3134676740) (.leaf 3047392357))) (.branch 20 (.branch 19 (.leaf 2963392045) (.leaf 2882513623)) (.branch 21 (.leaf 2804604561) (.leaf 2729521315)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2657128726) (.leaf 2587299453)) (.branch 25 (.leaf 2519913459) (.leaf 2454857531))) (.branch 28 (.branch 27 (.leaf 2392024836) (.leaf 2331314510)) (.branch 29 (.leaf 2272631276) (.leaf 2215885095)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2160990830) (.branch 32 (.leaf 2107867947) (.leaf 2056440225))) (.branch 35 (.branch 34 (.leaf 2006635499) (.leaf 1958385405)) (.branch 36 (.leaf 1911625155) (.leaf 1866293322)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1822331640) (.leaf 1779684814)) (.branch 40 (.leaf 1738300351) (.leaf 1698128392))) (.branch 43 (.branch 42 (.leaf 1659121560) (.leaf 1621234819)) (.branch 44 (.leaf 1584425339) (.leaf 1548652369))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1513877123) (.branch 47 (.leaf 1480062665) (.leaf 1447173813))) (.branch 50 (.branch 49 (.leaf 1415177032) (.leaf 1384040352)) (.branch 51 (.leaf 1353733279) (.leaf 1324226713)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1295492875) (.leaf 1267505235)) (.branch 55 (.leaf 1240238446) (.leaf 1213668281))) (.branch 58 (.branch 57 (.leaf 1187771572) (.leaf 1162526157)) (.branch 59 (.leaf 1137910829) (.leaf 1113905281))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1090490064) (.branch 62 (.leaf 1067646543) (.leaf 1045356855))) (.branch 65 (.branch 64 (.leaf 1023603869) (.leaf 1002371151)) (.branch 66 (.leaf 981642927) (.leaf 961404054)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 941639986) (.leaf 922336746)) (.branch 70 (.leaf 903480897) (.leaf 885059518))) (.branch 73 (.branch 72 (.leaf 867060181) (.leaf 849470921)) (.branch 74 (.leaf 832280221) (.leaf 815476988))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 799050534) (.branch 77 (.leaf 782990555) (.leaf 767287120))) (.branch 80 (.branch 79 (.leaf 751930645) (.leaf 736911884)) (.branch 81 (.leaf 722221913) (.leaf 707852112)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 693794157) (.leaf 680040003)) (.branch 85 (.leaf 666581872) (.leaf 653412246))) (.branch 88 (.branch 87 (.leaf 640523851) (.leaf 627909647)) (.branch 89 (.leaf 615562822) (.leaf 603476779)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 591645129) (.branch 92 (.leaf 580061681) (.leaf 568720437))) (.branch 95 (.branch 94 (.leaf 557615578) (.leaf 546741467)) (.branch 96 (.leaf 536092629) (.leaf 525663758)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 515449700) (.leaf 505445452)) (.branch 100 (.leaf 495646156) (.leaf 486047093))) (.branch 103 (.branch 102 (.leaf 476643679) (.leaf 467431455)) (.branch 104 (.leaf 458406091) (.leaf 449563374))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 440899206) (.leaf 432409603)) (.branch 108 (.leaf 424090685) (.leaf 415938679))) (.branch 111 (.branch 110 (.leaf 407949910) (.leaf 400120799)) (.branch 112 (.leaf 392447863) (.leaf 384927707)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 377557023) (.leaf 370332591)) (.branch 116 (.leaf 363251267) (.leaf 356309992))) (.branch 119 (.branch 118 (.leaf 349505777) (.leaf 342835714)) (.branch 120 (.leaf 336296960) (.leaf 329886747)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 133).prefactor = (2479427123626523/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 133).cutoff/(generalMeanRows 133).c)).2 =
    (219345265555151/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 133).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 133).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 133).q*(generalMeanRows 133).c/2-2 = (149/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable078.value]
    have hcontinuation : (generalMeanRows 133).q*(generalMeanRows 133).cutoff/2-2 = (598/265:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable080.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 133).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 133

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 133).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 133).criticalRate j.val*(generalMeanRows 133).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 133).c*(generalMeanRows 133).criticalPoint j.val)).2-
      (generalMeanRows 133).J/2-(generalMeanRows 133).error (generalMeanGrid j.val)+
      (generalMeanRows 133).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 133).c)).2-
      (generalMeanRows 133).J/2-(generalMeanRows 133).error 4 := by
  have he : (generalMeanRows 133).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 133) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 133)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0133

/-! Kernel-checked entropy margins for general spectral rectangle 134. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0134
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5195456203) (.branch 2 (.leaf 5020824661) (.leaf 4854291330))) (.branch 5 (.branch 4 (.leaf 4695373088) (.leaf 4543621817)) (.branch 6 (.leaf 4398621342) (.leaf 4259984699)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4127351684) (.leaf 4000386649)) (.branch 10 (.leaf 3878776520) (.leaf 3762229004))) (.branch 13 (.branch 12 (.leaf 3650470968) (.leaf 3543246962)) (.branch 14 (.leaf 3440317888) (.leaf 3341459775))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3246462667) (.branch 17 (.leaf 3155129612) (.leaf 3067275724))) (.branch 20 (.branch 19 (.leaf 2982727334) (.leaf 2901321203)) (.branch 21 (.leaf 2822903806) (.leaf 2747330664)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2674465734) (.leaf 2604180845)) (.branch 25 (.leaf 2536355177) (.leaf 2470874777))) (.branch 28 (.branch 27 (.leaf 2407632117) (.leaf 2346525673)) (.branch 29 (.leaf 2287459548) (.leaf 2230343114)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2175090679) (.branch 32 (.leaf 2121621184) (.leaf 2069857912))) (.branch 35 (.branch 34 (.leaf 2019728224) (.leaf 1971163312)) (.branch 36 (.leaf 1924097964) (.leaf 1878470354)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1834221834) (.leaf 1791296750)) (.branch 40 (.leaf 1749642266) (.leaf 1709208196))) (.branch 43 (.branch 42 (.leaf 1669946856) (.leaf 1631812915)) (.branch 44 (.leaf 1594763263) (.leaf 1558756885))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1523754740) (.branch 47 (.leaf 1489719653) (.leaf 1456616209))) (.branch 50 (.branch 49 (.leaf 1424410659) (.leaf 1393070821)) (.branch 51 (.leaf 1362566003) (.leaf 1332866915)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1303945597) (.leaf 1275775346)) (.branch 55 (.leaf 1248330649) (.leaf 1221587120))) (.branch 58 (.branch 57 (.leaf 1195521443) (.leaf 1170111309)) (.branch 59 (.leaf 1145335373) (.leaf 1121173195))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1097605201) (.branch 62 (.leaf 1074612633) (.leaf 1052177511))) (.branch 65 (.branch 64 (.leaf 1030282593) (.leaf 1008911337)) (.branch 66 (.leaf 988047867) (.leaf 967676942)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 947783919) (.leaf 928354730)) (.branch 70 (.leaf 909375852) (.leaf 890834280))) (.branch 73 (.branch 72 (.leaf 872717502) (.leaf 855013477)) (.branch 74 (.leaf 837710612) (.leaf 820797743))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 804264111) (.branch 77 (.leaf 788099346) (.leaf 772293450))) (.branch 80 (.branch 79 (.leaf 756836778) (.leaf 741720024)) (.branch 81 (.leaf 726934205) (.leaf 712470645)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 698320966) (.leaf 684477070)) (.branch 85 (.leaf 670931129) (.leaf 657675575))) (.branch 88 (.branch 87 (.leaf 644703086) (.leaf 632006578)) (.branch 89 (.leaf 619579194) (.leaf 607414293)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 595505445) (.branch 92 (.leaf 583846418) (.leaf 572431175))) (.branch 95 (.branch 94 (.leaf 561253861) (.leaf 550308799)) (.branch 96 (.leaf 539590481) (.leaf 529093564)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 518812862) (.leaf 508743339)) (.branch 100 (.leaf 498880106) (.leaf 489218412))) (.branch 103 (.branch 102 (.leaf 479753643) (.leaf 470481312)) (.branch 104 (.leaf 461397060) (.leaf 452496646))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 443775948) (.leaf 435230952)) (.branch 108 (.leaf 426857756) (.leaf 418652561))) (.branch 111 (.branch 110 (.leaf 410611667) (.leaf 402731473)) (.branch 112 (.leaf 395008473) (.leaf 387439250)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 380020475) (.leaf 372748905)) (.branch 116 (.leaf 365621378) (.leaf 358634813))) (.branch 119 (.branch 118 (.leaf 351786203) (.leaf 345072619)) (.branch 120 (.leaf 338491202) (.leaf 332039164)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 134).prefactor = (4991209358180991/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 134).cutoff/(generalMeanRows 134).c)).2 =
    (219345265555151/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 134).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 134).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 134).q*(generalMeanRows 134).c/2-2 = (149/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable078.value]
    have hcontinuation : (generalMeanRows 134).q*(generalMeanRows 134).cutoff/2-2 = (598/265:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable080.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 134).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 134

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 134).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 134).criticalRate j.val*(generalMeanRows 134).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 134).c*(generalMeanRows 134).criticalPoint j.val)).2-
      (generalMeanRows 134).J/2-(generalMeanRows 134).error (generalMeanGrid j.val)+
      (generalMeanRows 134).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 134).c)).2-
      (generalMeanRows 134).J/2-(generalMeanRows 134).error 4 := by
  have he : (generalMeanRows 134).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 134) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 134)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0134

/-! Kernel-checked entropy margins for general spectral rectangle 135. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0135
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5054292894) (.branch 2 (.leaf 4879058979) (.leaf 4711976834))) (.branch 5 (.branch 4 (.leaf 4552563663) (.leaf 4400371464)) (.branch 6 (.leaf 4254983992) (.leaf 4116014042)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3983101018) (.leaf 3855908749)) (.branch 10 (.leaf 3734123516) (.leaf 3617452279))) (.branch 13 (.branch 12 (.leaf 3505621060) (.leaf 3398373490)) (.branch 14 (.leaf 3295469477) (.leaf 3196683997))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3101805991) (.branch 17 (.leaf 3010637359) (.leaf 2922992033))) (.branch 20 (.branch 19 (.leaf 2838695131) (.leaf 2757582181)) (.branch 21 (.leaf 2679498404) (.leaf 2604298058)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2531843830) (.leaf 2462006273)) (.branch 25 (.leaf 2394663293) (.leaf 2329699668))) (.branch 28 (.branch 27 (.leaf 2267006603) (.leaf 2206481323)) (.branch 29 (.leaf 2148026686) (.leaf 2091550838)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2036966873) (.branch 32 (.leaf 1984192536) (.leaf 1933149934))) (.branch 35 (.branch 34 (.leaf 1883765274) (.leaf 1835968611)) (.branch 36 (.leaf 1789693622) (.leaf 1744877390)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1701460201) (.leaf 1659385359)) (.branch 40 (.leaf 1618599010) (.leaf 1579049977))) (.branch 43 (.branch 42 (.leaf 1540689605) (.leaf 1503471623)) (.branch 44 (.leaf 1467352002) (.leaf 1432288835))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1398242212) (.branch 47 (.leaf 1365174117) (.leaf 1333048318))) (.branch 50 (.branch 49 (.leaf 1301830270) (.leaf 1271487024)) (.branch 51 (.leaf 1241987142) (.leaf 1213300613)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1185398780) (.leaf 1158254263)) (.branch 55 (.leaf 1131840898) (.leaf 1106133668))) (.branch 58 (.branch 57 (.leaf 1081108647) (.leaf 1056742942)) (.branch 59 (.leaf 1033014638) (.leaf 1009902750))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 987387179) (.branch 62 (.leaf 965448659) (.leaf 944068723))) (.branch 65 (.branch 64 (.leaf 923229660) (.leaf 902914477)) (.branch 66 (.leaf 883106865) (.leaf 863791165)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 844952337) (.leaf 826575929)) (.branch 70 (.leaf 808648052) (.leaf 791155347))) (.branch 73 (.branch 72 (.leaf 774084967) (.leaf 757424548)) (.branch 74 (.leaf 741162190) (.leaf 725286433))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 709786237) (.branch 77 (.leaf 694650965) (.leaf 679870362))) (.branch 80 (.branch 79 (.leaf 665434541) (.leaf 651333963)) (.branch 81 (.leaf 637559424) (.leaf 624102040)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 610953233) (.leaf 598104717)) (.branch 85 (.leaf 585548486) (.leaf 573276802))) (.branch 88 (.branch 87 (.leaf 561282184) (.leaf 549557398)) (.branch 89 (.leaf 538095443) (.leaf 526889548)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 515933155) (.branch 92 (.leaf 505219917) (.leaf 494743685))) (.branch 95 (.branch 94 (.leaf 484498502) (.leaf 474478595)) (.branch 96 (.leaf 464678369) (.leaf 455092397)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 445715418) (.leaf 436542326)) (.branch 100 (.leaf 427568168) (.leaf 418788136))) (.branch 103 (.branch 102 (.leaf 410197561) (.leaf 401791910)) (.branch 104 (.leaf 393566781) (.leaf 385517895))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 377641096) (.leaf 369932344)) (.branch 108 (.leaf 362387710) (.leaf 355003376))) (.branch 111 (.branch 110 (.leaf 347775626) (.leaf 340700847)) (.branch 112 (.leaf 333775523) (.leaf 326996232)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 320359643) (.leaf 313862515)) (.branch 116 (.leaf 307501690) (.leaf 301274093))) (.branch 119 (.branch 118 (.leaf 295176731) (.leaf 289206684)) (.branch 120 (.leaf 283361110) (.leaf 277637239)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 135).prefactor = (2497720998470379/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 135).cutoff/(generalMeanRows 135).c)).2 =
    (416160397224929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 135).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 135).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 135).q*(generalMeanRows 135).c/2-2 = (79/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable007.value]
    have hcontinuation : (generalMeanRows 135).q*(generalMeanRows 135).cutoff/2-2 = (223/100:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable077.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 135).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 135

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 135).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 135).criticalRate j.val*(generalMeanRows 135).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 135).c*(generalMeanRows 135).criticalPoint j.val)).2-
      (generalMeanRows 135).J/2-(generalMeanRows 135).error (generalMeanGrid j.val)+
      (generalMeanRows 135).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 135).c)).2-
      (generalMeanRows 135).J/2-(generalMeanRows 135).error 4 := by
  have he : (generalMeanRows 135).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 135) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 135)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0135

/-! Kernel-checked entropy margins for general spectral rectangle 136. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0136
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4998346309) (.branch 2 (.leaf 4822454477) (.leaf 4654775732))) (.branch 5 (.branch 4 (.leaf 4494824035) (.leaf 4342148346)) (.branch 6 (.leaf 4196329565) (.leaf 4056977804)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3923729942) (.leaf 3796247425)) (.branch 10 (.leaf 3674214285) (.leaf 3557335356))) (.branch 13 (.branch 12 (.leaf 3445334651) (.leaf 3337953896)) (.branch 14 (.leaf 3234951193) (.leaf 3136099805))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3041187047) (.branch 17 (.leaf 2950013272) (.leaf 2862390940))) (.branch 20 (.branch 19 (.leaf 2778143770) (.leaf 2697105957)) (.branch 21 (.leaf 2619121450) (.leaf 2544043295)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2471733022) (.leaf 2402060079)) (.branch 25 (.leaf 2334901318) (.leaf 2270140508))) (.branch 28 (.branch 27 (.leaf 2207667891) (.leaf 2147379769)) (.branch 29 (.leaf 2089178120) (.leaf 2032970242)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1978668424) (.branch 32 (.leaf 1926189636) (.leaf 1875455243))) (.branch 35 (.branch 34 (.leaf 1826390741) (.leaf 1778925505)) (.branch 36 (.leaf 1732992558) (.leaf 1688528358)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1645472589) (.leaf 1603767981)) (.branch 40 (.leaf 1563360127) (.leaf 1524197318))) (.branch 43 (.branch 42 (.leaf 1486230395) (.leaf 1449412595)) (.branch 44 (.leaf 1413699423) (.leaf 1379048521))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1345419551) (.branch 47 (.leaf 1312774081) (.leaf 1281075482))) (.branch 50 (.branch 49 (.leaf 1250288829) (.leaf 1220380808)) (.branch 51 (.leaf 1191319628) (.leaf 1163074944)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1135617774) (.leaf 1108920431)) (.branch 55 (.leaf 1082956451) (.leaf 1057700535))) (.branch 58 (.branch 57 (.leaf 1033128483) (.leaf 1009217138)) (.branch 59 (.leaf 985944336) (.leaf 963288853))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 941230357) (.branch 62 (.leaf 919749362) (.leaf 898827190))) (.branch 65 (.branch 64 (.leaf 878445927) (.leaf 858588387)) (.branch 66 (.leaf 839238076) (.leaf 820379158)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 801996423) (.leaf 784075258)) (.branch 70 (.leaf 766601617) (.leaf 749561996))) (.branch 73 (.branch 72 (.leaf 732943405) (.leaf 716733348)) (.branch 74 (.leaf 700919795) (.leaf 685491164))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 670436300) (.branch 77 (.leaf 655744454) (.leaf 641405267))) (.branch 80 (.branch 79 (.leaf 627408751) (.leaf 613745272)) (.branch 81 (.leaf 600405537) (.leaf 587380577)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 574661731) (.leaf 562240638)) (.branch 85 (.leaf 550109220) (.leaf 538259671))) (.branch 88 (.branch 87 (.leaf 526684445) (.leaf 515376248)) (.branch 89 (.leaf 504328022) (.leaf 493532943)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 482984403) (.branch 92 (.leaf 472676008) (.leaf 462601566))) (.branch 95 (.branch 94 (.leaf 452755079) (.leaf 443130738)) (.branch 96 (.leaf 433722912) (.leaf 424526142)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 415535139) (.leaf 406744768)) (.branch 100 (.leaf 398150053) (.leaf 389746164))) (.branch 103 (.branch 102 (.leaf 381528411) (.leaf 373492245)) (.branch 104 (.leaf 365633247) (.leaf 357947126))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 350429713) (.leaf 343076958)) (.branch 108 (.leaf 335884925) (.leaf 328849789))) (.branch 111 (.branch 110 (.leaf 321967829) (.leaf 315235430)) (.branch 112 (.leaf 308649073) (.leaf 302205337)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 295900893) (.leaf 289732500)) (.branch 116 (.leaf 283697006) (.leaf 277791340))) (.branch 119 (.branch 118 (.leaf 272012515) (.leaf 266357619)) (.branch 120 (.leaf 260823819) (.leaf 255408353)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 136).prefactor = (2514271701814721/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 136).cutoff/(generalMeanRows 136).c)).2 =
    (204064112763831/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 136).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 136).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 136).q*(generalMeanRows 136).c/2-2 = (13/16:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable042.value]
    have hcontinuation : (generalMeanRows 136).q*(generalMeanRows 136).cutoff/2-2 = (223/100:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable077.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 136).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 136

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 136).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 136).criticalRate j.val*(generalMeanRows 136).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 136).c*(generalMeanRows 136).criticalPoint j.val)).2-
      (generalMeanRows 136).J/2-(generalMeanRows 136).error (generalMeanGrid j.val)+
      (generalMeanRows 136).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 136).c)).2-
      (generalMeanRows 136).J/2-(generalMeanRows 136).error 4 := by
  have he : (generalMeanRows 136).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 136) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 136)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0136

/-! Kernel-checked entropy margins for general spectral rectangle 137. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0137
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5135883325) (.branch 2 (.leaf 4960532171) (.leaf 4793340487))) (.branch 5 (.branch 4 (.leaf 4633822026) (.leaf 4481525743)) (.branch 6 (.leaf 4336032711) (.leaf 4196953378)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4063925101) (.leaf 3936609935)) (.branch 10 (.leaf 3814692633) (.leaf 3697878847))) (.branch 13 (.branch 12 (.leaf 3585893499) (.leaf 3478479297)) (.branch 14 (.leaf 3375395393) (.leaf 3276416155))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3181330049) (.branch 17 (.leaf 3089938619) (.leaf 3002055549))) (.branch 20 (.branch 19 (.leaf 2917505807) (.leaf 2836124854)) (.branch 21 (.leaf 2757757923) (.leaf 2682259350)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2609491961) (.leaf 2539326501)) (.branch 25 (.leaf 2471641114) (.leaf 2406320858))) (.branch 28 (.branch 27 (.leaf 2343257252) (.leaf 2282347865)) (.branch 29 (.leaf 2223495928) (.leaf 2166609977)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2111603518) (.branch 32 (.leaf 2058394722) (.leaf 2006906134))) (.branch 35 (.branch 34 (.leaf 1957064407) (.leaf 1908800051)) (.branch 36 (.leaf 1862047201) (.leaf 1816743400)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1772829399) (.leaf 1730248961)) (.branch 40 (.leaf 1688948692) (.leaf 1648877870))) (.branch 43 (.branch 42 (.leaf 1609988295) (.leaf 1572234138)) (.branch 44 (.leaf 1535571812) (.leaf 1499959842))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1465358744) (.branch 47 (.leaf 1431730919) (.leaf 1399040543))) (.branch 50 (.branch 49 (.leaf 1367253470) (.leaf 1336337142)) (.branch 51 (.leaf 1306260499) (.leaf 1276993902)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1248509053) (.leaf 1220778922)) (.branch 55 (.leaf 1193777686) (.leaf 1167480656))) (.branch 58 (.branch 57 (.leaf 1141864226) (.leaf 1116905810)) (.branch 59 (.leaf 1092583794) (.leaf 1068877480))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1045767047) (.branch 62 (.leaf 1023233498) (.leaf 1001258624))) (.branch 65 (.branch 64 (.leaf 979824963) (.leaf 958915762)) (.branch 66 (.leaf 938514941) (.leaf 918607063)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 899177298) (.leaf 880211399)) (.branch 70 (.leaf 861695669) (.leaf 843616937))) (.branch 73 (.branch 72 (.leaf 825962532) (.leaf 808720261)) (.branch 74 (.leaf 791878385) (.leaf 775425599))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 759351009) (.branch 77 (.leaf 743644118) (.leaf 728294805))) (.branch 80 (.branch 79 (.leaf 713293307) (.leaf 698630205)) (.branch 81 (.leaf 684296409) (.leaf 670283140)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 656581922) (.leaf 643184563)) (.branch 85 (.leaf 630083147) (.leaf 617270020))) (.branch 88 (.branch 87 (.leaf 604737780) (.leaf 592479265)) (.branch 89 (.leaf 580487546) (.leaf 568755912)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 557277868) (.branch 92 (.leaf 546047120) (.leaf 535057570))) (.branch 95 (.branch 94 (.leaf 524303308) (.leaf 513778605)) (.branch 96 (.leaf 503477904) (.leaf 493395813)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 483527104) (.leaf 473866699)) (.branch 100 (.leaf 464409671) (.leaf 455151232))) (.branch 103 (.branch 102 (.leaf 446086735) (.leaf 437211663)) (.branch 104 (.leaf 428521626) (.leaf 420012358))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 411679710) (.leaf 403519649)) (.branch 108 (.leaf 395528250) (.leaf 387701695))) (.branch 111 (.branch 110 (.leaf 380036270) (.leaf 372528357)) (.branch 112 (.leaf 365174437) (.leaf 357971081)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 350914951) (.leaf 344002796)) (.branch 116 (.leaf 337231445) (.leaf 330597812))) (.branch 119 (.branch 118 (.leaf 324098888) (.leaf 317731740)) (.branch 120 (.leaf 311493506) (.leaf 305381400)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 137).prefactor = (1255943894247023/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 137).cutoff/(generalMeanRows 137).c)).2 =
    (215263610235571/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 137).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 137).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 137).q*(generalMeanRows 137).c/2-2 = (307/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable081.value]
    have hcontinuation : (generalMeanRows 137).q*(generalMeanRows 137).cutoff/2-2 = (598/265:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable080.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 137).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 137

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 137).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 137).criticalRate j.val*(generalMeanRows 137).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 137).c*(generalMeanRows 137).criticalPoint j.val)).2-
      (generalMeanRows 137).J/2-(generalMeanRows 137).error (generalMeanGrid j.val)+
      (generalMeanRows 137).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 137).c)).2-
      (generalMeanRows 137).J/2-(generalMeanRows 137).error 4 := by
  have he : (generalMeanRows 137).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 137) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 137)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0137

/-! Kernel-checked entropy margins for general spectral rectangle 138. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0138
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5077498505) (.branch 2 (.leaf 4901465898) (.leaf 4733653958))) (.branch 5 (.branch 4 (.leaf 4573573263) (.leaf 4420769786)) (.branch 6 (.leaf 4274821805) (.leaf 4135337138)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4001950664) (.leaf 3874322099)) (.branch 10 (.leaf 3752133990) (.leaf 3635089904))) (.branch 13 (.branch 12 (.leaf 3522912787) (.leaf 3415343476)) (.branch 14 (.leaf 3312139349) (.leaf 3213073087))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3117931556) (.branch 17 (.leaf 3026514778) (.leaf 2938634987))) (.branch 20 (.branch 19 (.leaf 2854115770) (.leaf 2772791273)) (.branch 21 (.leaf 2694505474) (.leaf 2619111510)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2546471064) (.leaf 2476453788)) (.branch 25 (.leaf 2408936781) (.leaf 2343804101))) (.branch 28 (.branch 27 (.leaf 2280946312) (.leaf 2220260066)) (.branch 29 (.leaf 2161647717) (.leaf 2105016962)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2050280502) (.branch 32 (.leaf 1997355735) (.leaf 1946164467))) (.branch 35 (.branch 34 (.leaf 1896632640) (.leaf 1848690083)) (.branch 36 (.leaf 1802270278) (.leaf 1757310140)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1713749816) (.leaf 1671532493)) (.branch 40 (.leaf 1630604218) (.leaf 1590913738))) (.branch 43 (.branch 42 (.leaf 1552412339) (.leaf 1515053699)) (.branch 44 (.leaf 1478793758) (.leaf 1443590586))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1409404263) (.branch 47 (.leaf 1376196769) (.leaf 1343931875))) (.branch 50 (.branch 49 (.leaf 1312575048) (.leaf 1282093358)) (.branch 51 (.leaf 1252455387) (.leaf 1223631151)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1195592020) (.leaf 1168310648)) (.branch 55 (.leaf 1141760906) (.leaf 1115917811))) (.branch 58 (.branch 57 (.leaf 1090757477) (.leaf 1066257046)) (.branch 59 (.leaf 1042394643) (.leaf 1019149324))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 996501025) (.branch 62 (.leaf 974430521) (.leaf 952919383))) (.branch 65 (.branch 64 (.leaf 931949936) (.leaf 911505225)) (.branch 66 (.leaf 891568975) (.leaf 872125562)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 853159979) (.leaf 834657806)) (.branch 70 (.leaf 816605184) (.leaf 798988783))) (.branch 73 (.branch 72 (.leaf 781795783) (.leaf 765013848)) (.branch 74 (.leaf 748631100) (.leaf 732636104))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 717017841) (.branch 77 (.leaf 701765693) (.leaf 686869425))) (.branch 80 (.branch 79 (.leaf 672319166) (.leaf 658105393)) (.branch 81 (.leaf 644218916) (.leaf 630650865)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 617392671) (.leaf 604436060)) (.branch 85 (.leaf 591773033) (.leaf 579395862))) (.branch 88 (.branch 87 (.leaf 567297070) (.leaf 555469428)) (.branch 89 (.leaf 543905942) (.leaf 532599840)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 521544567) (.branch 92 (.leaf 510733778) (.leaf 500161322))) (.branch 95 (.branch 94 (.leaf 489821242) (.leaf 479707763)) (.branch 96 (.leaf 469815286) (.leaf 460138382)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 450671784) (.leaf 441410382)) (.branch 100 (.leaf 432349215) (.leaf 423483470))) (.branch 103 (.branch 102 (.leaf 414808471) (.leaf 406319677)) (.branch 104 (.leaf 398012677) (.leaf 389883185))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 381927034) (.leaf 374140174)) (.branch 108 (.leaf 366518667) (.leaf 359058684))) (.branch 111 (.branch 110 (.leaf 351756497) (.leaf 344608484)) (.branch 112 (.leaf 337611115) (.leaf 330760958)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 324054669) (.leaf 317488995)) (.branch 116 (.leaf 311060765) (.leaf 304766892))) (.branch 119 (.branch 118 (.leaf 298604368) (.leaf 292570263)) (.branch 120 (.leaf 286661720) (.leaf 280875956)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 138).prefactor = (2528277140546549/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 138).cutoff/(generalMeanRows 138).c)).2 =
    (105607502559631/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 138).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 138).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 138).q*(generalMeanRows 138).c/2-2 = (79/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable007.value]
    have hcontinuation : (generalMeanRows 138).q*(generalMeanRows 138).cutoff/2-2 = (598/265:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable080.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 138).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 138

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 138).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 138).criticalRate j.val*(generalMeanRows 138).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 138).c*(generalMeanRows 138).criticalPoint j.val)).2-
      (generalMeanRows 138).J/2-(generalMeanRows 138).error (generalMeanGrid j.val)+
      (generalMeanRows 138).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 138).c)).2-
      (generalMeanRows 138).J/2-(generalMeanRows 138).error 4 := by
  have he : (generalMeanRows 138).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 138) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 138)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0138

/-! Kernel-checked entropy margins for general spectral rectangle 139. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0139
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4943517301) (.branch 2 (.leaf 4767002588) (.leaf 4598762153))) (.branch 5 (.branch 4 (.leaf 4438306666) (.leaf 4285182000)) (.branch 6 (.leaf 4138966158) (.leaf 3999266528)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3865717426) (.leaf 3737977879)) (.branch 10 (.leaf 3615729640) (.leaf 3498675388))) (.branch 13 (.branch 12 (.leaf 3386537097) (.leaf 3279054563)) (.branch 14 (.leaf 3175984060) (.leaf 3077097117))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2982179402) (.branch 17 (.leaf 2891029703) (.leaf 2803458995))) (.branch 20 (.branch 19 (.leaf 2719289582) (.leaf 2638354311)) (.branch 21 (.leaf 2560495850) (.leaf 2485566022)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2413425189) (.leaf 2343941690)) (.branch 25 (.leaf 2276991313) (.leaf 2212456814))) (.branch 28 (.branch 27 (.leaf 2150227467) (.leaf 2090198648)) (.branch 29 (.leaf 2032271449) (.leaf 1976352324)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1922352752) (.branch 32 (.leaf 1870188927) (.leaf 1819781474))) (.branch 35 (.branch 34 (.leaf 1771055180) (.leaf 1723938739)) (.branch 36 (.leaf 1678364524) (.leaf 1634268370)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1591589365) (.leaf 1550269666)) (.branch 40 (.leaf 1510254317) (.leaf 1471491086))) (.branch 43 (.branch 42 (.leaf 1433930309) (.leaf 1397524743)) (.branch 44 (.leaf 1362229429) (.leaf 1328001567))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1294800394) (.branch 47 (.leaf 1262587071) (.leaf 1231324581))) (.branch 50 (.branch 49 (.leaf 1200977624) (.leaf 1171512528)) (.branch 51 (.leaf 1142897161) (.leaf 1115100847)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1088094292) (.leaf 1061849505)) (.branch 55 (.leaf 1036339737) (.leaf 1011539410))) (.branch 58 (.branch 57 (.leaf 987424060) (.leaf 963970279)) (.branch 59 (.leaf 941155660) (.leaf 918958747))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 897358987) (.branch 62 (.leaf 876336683) (.leaf 855872955))) (.branch 65 (.branch 64 (.leaf 835949695) (.leaf 816549534)) (.branch 66 (.leaf 797655801) (.leaf 779252493)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 761324239) (.leaf 743856273)) (.branch 70 (.leaf 726834406) (.leaf 710244994))) (.branch 73 (.branch 72 (.leaf 694074916) (.leaf 678311549)) (.branch 74 (.leaf 662942746) (.leaf 647956812))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 633342484) (.branch 77 (.leaf 619088912) (.leaf 605185640))) (.branch 80 (.branch 79 (.leaf 591622589) (.leaf 578390040)) (.branch 81 (.leaf 565478618) (.leaf 552879276)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 540583283) (.leaf 528582210)) (.branch 85 (.leaf 516867913) (.leaf 505432527))) (.branch 88 (.branch 87 (.leaf 494268452) (.leaf 483368339)) (.branch 89 (.leaf 472725083) (.leaf 462331814)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 452181882) (.branch 92 (.leaf 442268854) (.leaf 432586503))) (.branch 95 (.branch 94 (.leaf 423128797) (.leaf 413889898)) (.branch 96 (.leaf 404864146) (.leaf 396046059)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 387430324) (.leaf 379011789)) (.branch 100 (.leaf 370785458) (.leaf 362746485))) (.branch 103 (.branch 102 (.leaf 354890170) (.leaf 347211950)) (.branch 104 (.leaf 339707398) (.leaf 332372216))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 325202229) (.leaf 318193384)) (.branch 108 (.leaf 311341743) (.leaf 304643479))) (.branch 111 (.branch 110 (.leaf 298094874) (.leaf 291692315)) (.branch 112 (.leaf 285432286) (.leaf 279311372)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 273326250) (.leaf 267473689)) (.branch 116 (.leaf 261750543) (.leaf 256153753))) (.branch 119 (.branch 118 (.leaf 250680342) (.leaf 245327412)) (.branch 120 (.leaf 240092142) (.leaf 234971784)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 139).prefactor = (1265466037723521/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 139).cutoff/(generalMeanRows 139).c)).2 =
    (50020006984811/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 139).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 139).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 139).q*(generalMeanRows 139).c/2-2 = (167/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable082.value]
    have hcontinuation : (generalMeanRows 139).q*(generalMeanRows 139).cutoff/2-2 = (223/100:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable077.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 139).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 139

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 139).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 139).criticalRate j.val*(generalMeanRows 139).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 139).c*(generalMeanRows 139).criticalPoint j.val)).2-
      (generalMeanRows 139).J/2-(generalMeanRows 139).error (generalMeanGrid j.val)+
      (generalMeanRows 139).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 139).c)).2-
      (generalMeanRows 139).J/2-(generalMeanRows 139).error 4 := by
  have he : (generalMeanRows 139).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 139) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 139)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0139

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock01 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 1 i) := by
  fin_cases i
  · exact EntropyRow0070.numerical
  · exact EntropyRow0071.numerical
  · exact EntropyRow0072.numerical
  · exact EntropyRow0073.numerical
  · exact EntropyRow0074.numerical
  · exact EntropyRow0075.numerical
  · exact EntropyRow0076.numerical
  · exact EntropyRow0077.numerical
  · exact EntropyRow0078.numerical
  · exact EntropyRow0079.numerical
  · exact EntropyRow0080.numerical
  · exact EntropyRow0081.numerical
  · exact EntropyRow0082.numerical
  · exact EntropyRow0083.numerical
  · exact EntropyRow0084.numerical
  · exact EntropyRow0085.numerical
  · exact EntropyRow0086.numerical
  · exact EntropyRow0087.numerical
  · exact EntropyRow0088.numerical
  · exact EntropyRow0089.numerical
  · exact EntropyRow0090.numerical
  · exact EntropyRow0091.numerical
  · exact EntropyRow0092.numerical
  · exact EntropyRow0093.numerical
  · exact EntropyRow0094.numerical
  · exact EntropyRow0095.numerical
  · exact EntropyRow0096.numerical
  · exact EntropyRow0097.numerical
  · exact EntropyRow0098.numerical
  · exact EntropyRow0099.numerical
  · exact EntropyRow0100.numerical
  · exact EntropyRow0101.numerical
  · exact EntropyRow0102.numerical
  · exact EntropyRow0103.numerical
  · exact EntropyRow0104.numerical
  · exact EntropyRow0105.numerical
  · exact EntropyRow0106.numerical
  · exact EntropyRow0107.numerical
  · exact EntropyRow0108.numerical
  · exact EntropyRow0109.numerical
  · exact EntropyRow0110.numerical
  · exact EntropyRow0111.numerical
  · exact EntropyRow0112.numerical
  · exact EntropyRow0113.numerical
  · exact EntropyRow0114.numerical
  · exact EntropyRow0115.numerical
  · exact EntropyRow0116.numerical
  · exact EntropyRow0117.numerical
  · exact EntropyRow0118.numerical
  · exact EntropyRow0119.numerical
  · exact EntropyRow0120.numerical
  · exact EntropyRow0121.numerical
  · exact EntropyRow0122.numerical
  · exact EntropyRow0123.numerical
  · exact EntropyRow0124.numerical
  · exact EntropyRow0125.numerical
  · exact EntropyRow0126.numerical
  · exact EntropyRow0127.numerical
  · exact EntropyRow0128.numerical
  · exact EntropyRow0129.numerical
  · exact EntropyRow0130.numerical
  · exact EntropyRow0131.numerical
  · exact EntropyRow0132.numerical
  · exact EntropyRow0133.numerical
  · exact EntropyRow0134.numerical
  · exact EntropyRow0135.numerical
  · exact EntropyRow0136.numerical
  · exact EntropyRow0137.numerical
  · exact EntropyRow0138.numerical
  · exact EntropyRow0139.numerical
end SingularValueBounds.KL.Certificates
