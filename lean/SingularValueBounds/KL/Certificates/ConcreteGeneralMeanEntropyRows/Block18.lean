import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block02
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block03
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block04
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block05
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block06
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block07
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block15
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block18
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block19
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block20
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block21
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block23
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block24
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block25
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block26
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block27
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 1260. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1260
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4606706777) (.branch 2 (.leaf 4477381629) (.leaf 4352418067))) (.branch 5 (.branch 4 (.leaf 4231608328) (.leaf 4114759962)) (.branch 6 (.leaf 4001694231) (.leaf 3892244720)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3786256124) (.leaf 3683583182)) (.branch 10 (.leaf 3584089741) (.leaf 3487647929))) (.branch 13 (.branch 12 (.leaf 3394137428) (.leaf 3303444825)) (.branch 14 (.leaf 3215463035) (.leaf 3130090793))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3047232190) (.branch 17 (.leaf 2966796266) (.leaf 2888696637))) (.branch 20 (.branch 19 (.leaf 2812851168) (.leaf 2739181666)) (.branch 21 (.leaf 2667613613) (.leaf 2598075916)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2530500687) (.leaf 2464823033)) (.branch 25 (.leaf 2400980871) (.leaf 2338914760))) (.branch 28 (.branch 27 (.leaf 2278567741) (.leaf 2219885191)) (.branch 29 (.leaf 2162814695) (.leaf 2107305921)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2053310504) (.branch 32 (.leaf 2000781946) (.leaf 1949675514))) (.branch 35 (.branch 34 (.leaf 1899948154) (.leaf 1851558403)) (.branch 36 (.leaf 1804466312) (.leaf 1758633375)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1714022454) (.leaf 1670597725)) (.branch 40 (.leaf 1628324606) (.leaf 1587169713))) (.branch 43 (.branch 42 (.leaf 1547100797) (.leaf 1508086699)) (.branch 44 (.leaf 1470097303) (.leaf 1433103491))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1397077100) (.branch 47 (.leaf 1361990885) (.leaf 1327818480))) (.branch 50 (.branch 49 (.leaf 1294534365) (.leaf 1262113829)) (.branch 51 (.leaf 1230532940) (.leaf 1199768517)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1169798097) (.leaf 1140599911)) (.branch 55 (.leaf 1112152859) (.leaf 1084436483))) (.branch 58 (.branch 57 (.leaf 1057430943) (.leaf 1031116997)) (.branch 59 (.leaf 1005475978) (.leaf 980489777))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 956140817) (.branch 62 (.leaf 932412040) (.leaf 909286887))) (.branch 65 (.branch 64 (.leaf 886749282) (.leaf 864783615)) (.branch 66 (.leaf 843374725) (.leaf 822507888)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 802168800) (.leaf 782343565)) (.branch 70 (.leaf 763018682) (.leaf 744181028))) (.branch 73 (.branch 72 (.leaf 725817853) (.leaf 707916763)) (.branch 74 (.leaf 690465708) (.leaf 673452977))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 656867181) (.branch 77 (.leaf 640697246) (.leaf 624932404))) (.branch 80 (.branch 79 (.leaf 609562183) (.leaf 594576395)) (.branch 81 (.leaf 579965134) (.leaf 565718761)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 551827899) (.leaf 538283425)) (.branch 85 (.leaf 525076462) (.leaf 512198372))) (.branch 88 (.branch 87 (.leaf 499640749) (.leaf 487395413)) (.branch 89 (.leaf 475454401) (.leaf 463809963)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 452454556) (.branch 92 (.leaf 441380836) (.leaf 430581654))) (.branch 95 (.branch 94 (.leaf 420050051) (.leaf 409779249)) (.branch 96 (.leaf 399762652) (.leaf 389993833)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 380466537) (.leaf 371174672)) (.branch 100 (.leaf 362112304) (.leaf 353273655))) (.branch 103 (.branch 102 (.leaf 344653097) (.leaf 336245149)) (.branch 104 (.leaf 328044471) (.leaf 320045862))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 312244256) (.leaf 304634718)) (.branch 108 (.leaf 297212439) (.leaf 289972736))) (.branch 111 (.branch 110 (.leaf 282911044) (.leaf 276022919)) (.branch 112 (.leaf 269304026) (.leaf 262750146)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 256357165) (.leaf 250121075)) (.branch 116 (.leaf 244037970) (.leaf 238104045))) (.branch 119 (.branch 118 (.leaf 232315591) (.leaf 226668992)) (.branch 120 (.leaf 221160727) (.leaf 215787361)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1260).prefactor = (259696115473323/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1260).cutoff/(generalMeanRows 1260).c)).2 =
    (68583946722501/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1260).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1260).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1260).q*(generalMeanRows 1260).c/2-2 = (1547/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable423.value]
    have hcontinuation : (generalMeanRows 1260).q*(generalMeanRows 1260).cutoff/2-2 = (3424/497:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable424.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1260).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1260

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1260).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1260).criticalRate j.val*(generalMeanRows 1260).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1260).c*(generalMeanRows 1260).criticalPoint j.val)).2-
      (generalMeanRows 1260).J/2-(generalMeanRows 1260).error (generalMeanGrid j.val)+
      (generalMeanRows 1260).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1260).c)).2-
      (generalMeanRows 1260).J/2-(generalMeanRows 1260).error 4 := by
  have he : (generalMeanRows 1260).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1260) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1260)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1260

/-! Kernel-checked entropy margins for general spectral rectangle 1261. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1261
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5050748953) (.branch 2 (.leaf 4915985784) (.leaf 4785624738))) (.branch 5 (.branch 4 (.leaf 4659456635) (.leaf 4537287919)) (.branch 6 (.leaf 4418939017) (.leaf 4304242902)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4193043849) (.leaf 4085196333)) (.branch 10 (.leaf 3980564073) (.leaf 3879019178))) (.branch 13 (.branch 12 (.leaf 3780441404) (.leaf 3684717484)) (.branch 14 (.leaf 3591740542) (.leaf 3501409567))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3413628945) (.branch 17 (.leaf 3328308035) (.leaf 3245360798))) (.branch 20 (.branch 19 (.leaf 3164705451) (.leaf 3086264168)) (.branch 21 (.leaf 3009962795) (.leaf 2935730607)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2863500074) (.leaf 2793206656)) (.branch 25 (.leaf 2724788615) (.leaf 2658186838))) (.branch 28 (.branch 27 (.leaf 2593344681) (.leaf 2530207822)) (.branch 29 (.leaf 2468724130) (.leaf 2408843534)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2350517919) (.branch 32 (.leaf 2293701013) (.leaf 2238348290))) (.branch 35 (.branch 34 (.leaf 2184416883) (.leaf 2131865496)) (.branch 36 (.leaf 2080654329) (.leaf 2030745000)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1982100481) (.leaf 1934685033)) (.branch 40 (.leaf 1888464145) (.leaf 1843404479))) (.branch 43 (.branch 42 (.leaf 1799473817) (.leaf 1756641010)) (.branch 44 (.leaf 1714875937) (.leaf 1674149454))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1634433359) (.branch 47 (.leaf 1595700347) (.leaf 1557923979))) (.branch 50 (.branch 49 (.leaf 1521078643) (.leaf 1485139524)) (.branch 51 (.leaf 1450082571) (.leaf 1415884467)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1382522603) (.leaf 1349975050)) (.branch 55 (.leaf 1318220533) (.leaf 1287238408))) (.branch 58 (.branch 57 (.leaf 1257008639) (.leaf 1227511776)) (.branch 59 (.leaf 1198728934) (.leaf 1170641773))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1143232477) (.branch 62 (.leaf 1116483743) (.leaf 1090378753))) (.branch 65 (.branch 64 (.leaf 1064901167) (.leaf 1040035101)) (.branch 66 (.leaf 1015765115) (.leaf 992076198)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 968953751) (.leaf 946383580)) (.branch 70 (.leaf 924351874) (.leaf 902845203))) (.branch 73 (.branch 72 (.leaf 881850497) (.leaf 861355042)) (.branch 74 (.leaf 841346463) (.leaf 821812717))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 802742084) (.branch 77 (.leaf 784123152) (.leaf 765944812))) (.branch 80 (.branch 79 (.leaf 748196250) (.leaf 730866932)) (.branch 81 (.leaf 713946605) (.leaf 697425278)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 681293223) (.leaf 665540965)) (.branch 85 (.leaf 650159271) (.leaf 635139148))) (.branch 88 (.branch 87 (.leaf 620471834) (.leaf 606148790)) (.branch 89 (.leaf 592161697) (.leaf 578502448)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 565163140) (.branch 92 (.leaf 552136072) (.leaf 539413738))) (.branch 95 (.branch 94 (.leaf 526988820) (.leaf 514854186)) (.branch 96 (.leaf 503002883) (.leaf 491428129)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 480123317) (.leaf 469082000)) (.branch 100 (.leaf 458297893) (.leaf 447764870))) (.branch 103 (.branch 102 (.leaf 437476953) (.leaf 427428315)) (.branch 104 (.leaf 417613270) (.leaf 408026275))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 398661923) (.leaf 389514938)) (.branch 108 (.leaf 380580176) (.leaf 371852617))) (.branch 111 (.branch 110 (.leaf 363327366) (.leaf 354999646)) (.branch 112 (.leaf 346864795) (.leaf 338918269)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 331155630) (.leaf 323572551)) (.branch 116 (.leaf 316164807) (.leaf 308928278))) (.branch 119 (.branch 118 (.leaf 301858942) (.leaf 294952875)) (.branch 120 (.leaf 288206247) (.leaf 281615320)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1261).prefactor = (171247932004741/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1261).cutoff/(generalMeanRows 1261).c)).2 =
    (223468762853337/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1261).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1261).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1261).q*(generalMeanRows 1261).c/2-2 = (1453/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable401.value]
    have hcontinuation : (generalMeanRows 1261).q*(generalMeanRows 1261).cutoff/2-2 = (3424/497:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable424.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1261).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1261

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1261).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1261).criticalRate j.val*(generalMeanRows 1261).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1261).c*(generalMeanRows 1261).criticalPoint j.val)).2-
      (generalMeanRows 1261).J/2-(generalMeanRows 1261).error (generalMeanGrid j.val)+
      (generalMeanRows 1261).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1261).c)).2-
      (generalMeanRows 1261).J/2-(generalMeanRows 1261).error 4 := by
  have he : (generalMeanRows 1261).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1261) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1261)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1261

/-! Kernel-checked entropy margins for general spectral rectangle 1262. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1262
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5271702797) (.branch 2 (.leaf 5133979542) (.leaf 5000698087))) (.branch 5 (.branch 4 (.leaf 4871647416) (.leaf 4746632367)) (.branch 6 (.leaf 4625471956) (.leaf 4507997920)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4394053445) (.leaf 4283492050)) (.branch 10 (.leaf 4176176606) (.leaf 4071978480))) (.branch 13 (.branch 12 (.leaf 3970776763) (.leaf 3872457607)) (.branch 14 (.leaf 3776913614) (.leaf 3684043310))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3593750668) (.branch 17 (.leaf 3505944677) (.leaf 3420538965))) (.branch 20 (.branch 19 (.leaf 3337451449) (.leaf 3256604030)) (.branch 21 (.leaf 3177922309) (.leaf 3101335333)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3026775363) (.leaf 2954177669)) (.branch 25 (.leaf 2883480330) (.leaf 2814624067))) (.branch 28 (.branch 27 (.leaf 2747552077) (.leaf 2682209887)) (.branch 29 (.leaf 2618545221) (.leaf 2556507869)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2496049582) (.branch 32 (.leaf 2437123953) (.leaf 2379686331))) (.branch 35 (.branch 34 (.leaf 2323693719) (.leaf 2269104697)) (.branch 36 (.leaf 2215879336) (.leaf 2163979131)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2113366927) (.leaf 2064006859)) (.branch 40 (.leaf 2015864288) (.leaf 1968905747))) (.branch 43 (.branch 42 (.leaf 1923098889) (.leaf 1878412434)) (.branch 44 (.leaf 1834816126) (.leaf 1792280688))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1750777779) (.branch 47 (.leaf 1710279956) (.leaf 1670760639))) (.branch 50 (.branch 49 (.leaf 1632194075) (.leaf 1594555301)) (.branch 51 (.leaf 1557820120) (.leaf 1521965068)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1486967382) (.leaf 1452804982)) (.branch 55 (.leaf 1419456438) (.leaf 1386900950))) (.branch 58 (.branch 57 (.leaf 1355118322) (.leaf 1324088945)) (.branch 59 (.leaf 1293793772) (.leaf 1264214299))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1235332546) (.branch 62 (.leaf 1207131042) (.leaf 1179592804))) (.branch 65 (.branch 64 (.leaf 1152701321) (.leaf 1126440540)) (.branch 66 (.leaf 1100794849) (.leaf 1075749064)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1051288415) (.leaf 1027398531)) (.branch 70 (.leaf 1004065429) (.leaf 981275502))) (.branch 73 (.branch 72 (.leaf 959015504) (.leaf 937272544)) (.branch 74 (.leaf 916034071) (.leaf 895287864))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 875022024) (.branch 77 (.leaf 855224962) (.leaf 835885391))) (.branch 80 (.branch 79 (.leaf 816992318) (.leaf 798535032)) (.branch 81 (.leaf 780503099) (.leaf 762886353)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 745674887) (.leaf 728859047)) (.branch 85 (.leaf 712429424) (.leaf 696376848))) (.branch 88 (.branch 87 (.leaf 680692380) (.leaf 665367305)) (.branch 89 (.leaf 650393128) (.leaf 635761567)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 621464545) (.branch 92 (.leaf 607494188) (.leaf 593842815))) (.branch 95 (.branch 94 (.leaf 580502938) (.leaf 567467253)) (.branch 96 (.leaf 554728634) (.leaf 542280133)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 530114971) (.leaf 518226536)) (.branch 100 (.leaf 506608376) (.leaf 495254196))) (.branch 103 (.branch 102 (.leaf 484157857) (.leaf 473313366)) (.branch 104 (.leaf 462714875) (.leaf 452356681))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 442233215) (.leaf 432339043)) (.branch 108 (.leaf 422668862) (.leaf 413217497))) (.branch 111 (.branch 110 (.leaf 403979896) (.leaf 394951129)) (.branch 112 (.leaf 386126381) (.leaf 377500956)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 369070267) (.leaf 360829836)) (.branch 116 (.leaf 352775292) (.leaf 344902368))) (.branch 119 (.branch 118 (.leaf 337206898) (.leaf 329684813)) (.branch 120 (.leaf 322332143) (.leaf 315145008)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1262).prefactor = (4358662973475683/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1262).cutoff/(generalMeanRows 1262).c)).2 =
    (225091489808171/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1262).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1262).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1262).q*(generalMeanRows 1262).cutoff/2-2 = (3424/497:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable424.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1262).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1262

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1262).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1262).criticalRate j.val*(generalMeanRows 1262).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1262).c*(generalMeanRows 1262).criticalPoint j.val)).2-
      (generalMeanRows 1262).J/2-(generalMeanRows 1262).error (generalMeanGrid j.val)+
      (generalMeanRows 1262).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1262).c)).2-
      (generalMeanRows 1262).J/2-(generalMeanRows 1262).error 4 := by
  have he : (generalMeanRows 1262).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1262) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1262)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1262

/-! Kernel-checked entropy margins for general spectral rectangle 1263. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1263
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5755108037) (.branch 2 (.leaf 5594671831) (.leaf 5439710030))) (.branch 5 (.branch 4 (.leaf 5289950921) (.leaf 5145143724)) (.branch 6 (.leaf 5005056384) (.leaf 4869473634)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4738195312) (.leaf 4611034869)) (.branch 10 (.leaf 4487818062) (.leaf 4368381808))) (.branch 13 (.branch 12 (.leaf 4252573155) (.leaf 4140248385)) (.branch 14 (.leaf 4031272208) (.leaf 3925517049))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3822862410) (.branch 17 (.leaf 3723194300) (.leaf 3626404725))) (.branch 20 (.branch 19 (.leaf 3532391227) (.leaf 3441056474)) (.branch 21 (.leaf 3352307884) (.leaf 3266057291)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3182220639) (.leaf 3100717706)) (.branch 25 (.leaf 3021471851) (.leaf 2944409785))) (.branch 28 (.branch 27 (.leaf 2869461359) (.leaf 2796559376)) (.branch 29 (.leaf 2725639416) (.leaf 2656639667)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2589500783) (.branch 32 (.leaf 2524165747) (.leaf 2460579740))) (.branch 35 (.branch 34 (.leaf 2398690026) (.leaf 2338445845)) (.branch 36 (.leaf 2279798311) (.leaf 2222700315)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2167106443) (.leaf 2112972893)) (.branch 40 (.leaf 2060257396) (.leaf 2008919147))) (.branch 43 (.branch 42 (.leaf 1958918741) (.leaf 1910218105)) (.branch 44 (.leaf 1862780443) (.leaf 1816570179))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1771552907) (.branch 47 (.leaf 1727695341) (.leaf 1684965266))) (.branch 50 (.branch 49 (.leaf 1643331500) (.leaf 1602763848)) (.branch 51 (.leaf 1563233065) (.leaf 1524710816)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1487169647) (.leaf 1450582944)) (.branch 55 (.leaf 1414924909) (.leaf 1380170522))) (.branch 58 (.branch 57 (.leaf 1346295519) (.leaf 1313276362)) (.branch 59 (.leaf 1281090209) (.leaf 1249714899))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1219128917) (.branch 62 (.leaf 1189311379) (.leaf 1160242007))) (.branch 65 (.branch 64 (.leaf 1131901111) (.leaf 1104269566)) (.branch 66 (.leaf 1077328794) (.leaf 1051060747)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1025447888) (.leaf 1000473176)) (.branch 70 (.leaf 976120049) (.leaf 952372408))) (.branch 73 (.branch 72 (.leaf 929214601) (.leaf 906631415)) (.branch 74 (.leaf 884608054) (.leaf 863130132))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 842183655) (.branch 77 (.leaf 821755015) (.leaf 801830975))) (.branch 80 (.branch 79 (.leaf 782398655) (.leaf 763445527)) (.branch 81 (.leaf 744959400) (.leaf 726928410)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 709341015) (.leaf 692185979)) (.branch 85 (.leaf 675452366) (.leaf 659129534))) (.branch 88 (.branch 87 (.leaf 643207120) (.leaf 627675038)) (.branch 89 (.leaf 612523468) (.leaf 597742848)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 583323869) (.branch 92 (.leaf 569257464) (.leaf 555534806))) (.branch 95 (.branch 94 (.leaf 542147298) (.leaf 529086564)) (.branch 96 (.leaf 516344451) (.leaf 503913014)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 491784514) (.leaf 479951415)) (.branch 100 (.leaf 468406373) (.leaf 457142234))) (.branch 103 (.branch 102 (.leaf 446152028) (.leaf 435428964)) (.branch 104 (.leaf 424966426) (.leaf 414757966))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 404797301) (.leaf 395078310)) (.branch 108 (.leaf 385595025) (.leaf 376341633))) (.branch 111 (.branch 110 (.leaf 367312467) (.leaf 358502004)) (.branch 112 (.leaf 349904861) (.leaf 341515791)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 333329680) (.leaf 325341544)) (.branch 116 (.leaf 317546522) (.leaf 309939877))) (.branch 119 (.branch 118 (.leaf 302516992) (.leaf 295273365)) (.branch 120 (.leaf 288204607) (.leaf 281306439)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1263).prefactor = (651334832719799/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1263).cutoff/(generalMeanRows 1263).c)).2 =
    (494945733859273/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1263).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1263).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1263).q*(generalMeanRows 1263).cutoff/2-2 = (422/71:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable421.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1263).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1263

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1263).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1263).criticalRate j.val*(generalMeanRows 1263).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1263).c*(generalMeanRows 1263).criticalPoint j.val)).2-
      (generalMeanRows 1263).J/2-(generalMeanRows 1263).error (generalMeanGrid j.val)+
      (generalMeanRows 1263).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1263).c)).2-
      (generalMeanRows 1263).J/2-(generalMeanRows 1263).error 4 := by
  have he : (generalMeanRows 1263).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1263) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1263)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1263

/-! Kernel-checked entropy margins for general spectral rectangle 1264. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1264
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5565821237) (.branch 2 (.leaf 5421963998) (.leaf 5282716949))) (.branch 5 (.branch 4 (.leaf 5147861065) (.leaf 5017193821)) (.branch 6 (.leaf 4890527454) (.leaf 4767687433)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4648511141) (.leaf 4532846705)) (.branch 10 (.leaf 4420551982) (.leaf 4311493653))) (.branch 13 (.branch 12 (.leaf 4205546435) (.leaf 4102592374)) (.branch 14 (.leaf 4002520223) (.leaf 3905224884))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3810606913) (.branch 17 (.leaf 3718572077) (.leaf 3629030951))) (.branch 20 (.branch 19 (.leaf 3541898566) (.leaf 3457094080)) (.branch 21 (.leaf 3374540490) (.leaf 3294164365)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3215895606) (.leaf 3139667230)) (.branch 25 (.leaf 3065415167) (.leaf 2993078079))) (.branch 28 (.branch 27 (.leaf 2922597195) (.leaf 2853916155)) (.branch 29 (.leaf 2786980871) (.leaf 2721739399)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2658141815) (.branch 32 (.leaf 2596140109) (.leaf 2535688079))) (.branch 35 (.branch 34 (.leaf 2476741239) (.leaf 2419256730)) (.branch 36 (.leaf 2363193237) (.leaf 2308510913)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2255171311) (.leaf 2203137309)) (.branch 40 (.leaf 2152373060) (.leaf 2102843921))) (.branch 43 (.branch 42 (.leaf 2054516409) (.leaf 2007358141)) (.branch 44 (.leaf 1961337793) (.leaf 1916425050))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1872590564) (.branch 47 (.leaf 1829805914) (.leaf 1788043569))) (.branch 50 (.branch 49 (.leaf 1747276851) (.leaf 1707479900)) (.branch 51 (.leaf 1668627643) (.leaf 1630695764)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1593660674) (.leaf 1557499482)) (.branch 55 (.leaf 1522189973) (.leaf 1487710579))) (.branch 58 (.branch 57 (.leaf 1454040358) (.leaf 1421158970)) (.branch 59 (.leaf 1389046657) (.leaf 1357684221))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1327053005) (.branch 62 (.leaf 1297134875) (.leaf 1267912202))) (.branch 65 (.branch 64 (.leaf 1239367844) (.leaf 1211485131)) (.branch 66 (.leaf 1184247848) (.leaf 1157640223)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1131646909) (.leaf 1106252971)) (.branch 70 (.leaf 1081443877) (.leaf 1057205480))) (.branch 73 (.branch 72 (.leaf 1033524007) (.leaf 1010386051)) (.branch 74 (.leaf 987778556) (.leaf 965688807))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 944104421) (.branch 77 (.leaf 923013336) (.leaf 902403801))) (.branch 80 (.branch 79 (.leaf 882264367) (.leaf 862583881)) (.branch 81 (.leaf 843351472) (.leaf 824556547)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 806188780) (.leaf 788238108)) (.branch 85 (.leaf 770694720) (.leaf 753549053))) (.branch 88 (.branch 87 (.leaf 736791781) (.leaf 720413811)) (.branch 89 (.leaf 704406279) (.leaf 688760537)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 673468153) (.branch 92 (.leaf 658520903) (.leaf 643910764))) (.branch 95 (.branch 94 (.leaf 629629912) (.leaf 615670711)) (.branch 96 (.leaf 602025716) (.leaf 588687659)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 575649451) (.leaf 562904174)) (.branch 100 (.leaf 550445078) (.leaf 538265574))) (.branch 103 (.branch 102 (.leaf 526359235) (.leaf 514719784)) (.branch 104 (.leaf 503341099) (.leaf 492217202))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 481342258) (.leaf 470710571)) (.branch 108 (.leaf 460316582) (.leaf 450154862))) (.branch 111 (.branch 110 (.leaf 440220113) (.leaf 430507160)) (.branch 112 (.leaf 421010952) (.leaf 411726557)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 402649159) (.leaf 393774055)) (.branch 116 (.leaf 385096653) (.leaf 376612468))) (.branch 119 (.branch 118 (.leaf 368317121) (.leaf 360206334)) (.branch 120 (.leaf 352275931) (.leaf 344521832)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1264).prefactor = (4544908671170569/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1264).cutoff/(generalMeanRows 1264).c)).2 =
    (141192385920063/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1264).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1264).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1264).q*(generalMeanRows 1264).cutoff/2-2 = (3424/497:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable424.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1264).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1264

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1264).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1264).criticalRate j.val*(generalMeanRows 1264).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1264).c*(generalMeanRows 1264).criticalPoint j.val)).2-
      (generalMeanRows 1264).J/2-(generalMeanRows 1264).error (generalMeanGrid j.val)+
      (generalMeanRows 1264).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1264).c)).2-
      (generalMeanRows 1264).J/2-(generalMeanRows 1264).error 4 := by
  have he : (generalMeanRows 1264).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1264) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1264)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1264

/-! Kernel-checked entropy margins for general spectral rectangle 1265. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1265
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6411957257) (.branch 2 (.leaf 6238700917) (.leaf 6071244727))) (.branch 5 (.branch 4 (.leaf 5909300975) (.leaf 5752604298)) (.branch 6 (.leaf 5600909309) (.leaf 5453988525)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5311630556) (.leaf 5173638507)) (.branch 10 (.leaf 5039828580) (.leaf 4910028837))) (.branch 13 (.branch 12 (.leaf 4784078112) (.leaf 4661825035)) (.branch 14 (.leaf 4543127182) (.leaf 4427850306))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4315867654) (.branch 17 (.leaf 4207059363) (.leaf 4101311909))) (.branch 20 (.branch 19 (.leaf 3998517622) (.leaf 3898574240)) (.branch 21 (.leaf 3801384516) (.leaf 3706855858)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3614900005) (.leaf 3525432728)) (.branch 25 (.leaf 3438373570) (.leaf 3353645594))) (.branch 28 (.branch 27 (.leaf 3271175166) (.leaf 3190891747)) (.branch 29 (.leaf 3112727711) (.leaf 3036618170)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2962500818) (.branch 32 (.leaf 2890315788) (.leaf 2820005512))) (.branch 35 (.branch 34 (.leaf 2751514606) (.leaf 2684789746)) (.branch 36 (.leaf 2619779569) (.leaf 2556434570)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2494707013) (.leaf 2434550842)) (.branch 40 (.leaf 2375921603) (.leaf 2318776370))) (.branch 43 (.branch 42 (.leaf 2263073672) (.leaf 2208773432)) (.branch 44 (.leaf 2155836900) (.leaf 2104226599))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2053906271) (.branch 47 (.leaf 2004840821) (.leaf 1956996274))) (.branch 50 (.branch 49 (.leaf 1910339728) (.leaf 1864839307)) (.branch 51 (.leaf 1820464126) (.leaf 1777184249)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1734970651) (.leaf 1693795189)) (.branch 55 (.leaf 1653630561) (.leaf 1614450283))) (.branch 58 (.branch 57 (.leaf 1576228651) (.leaf 1538940718)) (.branch 59 (.leaf 1502562268) (.leaf 1467069785))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1432440430) (.branch 62 (.leaf 1398652023) (.leaf 1365683012))) (.branch 65 (.branch 64 (.leaf 1333512458) (.leaf 1302120011)) (.branch 66 (.leaf 1271485891) (.leaf 1241590872)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1212416260) (.leaf 1183943876)) (.branch 70 (.leaf 1156156044) (.leaf 1129035568))) (.branch 73 (.branch 72 (.leaf 1102565723) (.leaf 1076730238)) (.branch 74 (.leaf 1051513280) (.leaf 1026899442))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1002873731) (.branch 77 (.leaf 979421555) (.leaf 956528709))) (.branch 80 (.branch 79 (.leaf 934181363) (.leaf 912366056)) (.branch 81 (.leaf 891069679) (.leaf 870279467)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 849982991) (.leaf 830168142)) (.branch 85 (.leaf 810823131) (.leaf 791936470))) (.branch 88 (.branch 87 (.leaf 773496972) (.leaf 755493734)) (.branch 89 (.leaf 737916137) (.leaf 720753833)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 703996739) (.branch 92 (.leaf 687635027) (.leaf 671659123))) (.branch 95 (.branch 94 (.leaf 656059693) (.leaf 640827641)) (.branch 96 (.leaf 625954101) (.leaf 611430428)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 597248199) (.leaf 583399199)) (.branch 100 (.leaf 569875420) (.leaf 556669056))) (.branch 103 (.branch 102 (.leaf 543772493) (.leaf 531178308)) (.branch 104 (.leaf 518879264) (.leaf 506868302))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 495138538) (.leaf 483683260)) (.branch 108 (.leaf 472495921) (.leaf 461570135))) (.branch 111 (.branch 110 (.leaf 450899673) (.leaf 440478461)) (.branch 112 (.leaf 430300572) (.leaf 420360226)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 410651783) (.leaf 401169744)) (.branch 116 (.leaf 391908740) (.leaf 382863536))) (.branch 119 (.branch 118 (.leaf 374029023) (.leaf 365400218)) (.branch 120 (.leaf 356972258) (.leaf 348740396)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1265).prefactor = (5588760063486649/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1265).cutoff/(generalMeanRows 1265).c)).2 =
    (501080780155179/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1265).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1265).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1265).q*(generalMeanRows 1265).c/2-2 = (229/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable063.value]
    have hcontinuation : (generalMeanRows 1265).q*(generalMeanRows 1265).cutoff/2-2 = (422/71:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable421.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1265).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1265

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1265).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1265).criticalRate j.val*(generalMeanRows 1265).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1265).c*(generalMeanRows 1265).criticalPoint j.val)).2-
      (generalMeanRows 1265).J/2-(generalMeanRows 1265).error (generalMeanGrid j.val)+
      (generalMeanRows 1265).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1265).c)).2-
      (generalMeanRows 1265).J/2-(generalMeanRows 1265).error 4 := by
  have he : (generalMeanRows 1265).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1265) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1265)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1265

/-! Kernel-checked entropy margins for general spectral rectangle 1266. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1266
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7075687059) (.branch 2 (.leaf 6894599159) (.leaf 6719384842))) (.branch 5 (.branch 4 (.leaf 6549752389) (.leaf 6385433070)) (.branch 6 (.leaf 6226178688) (.leaf 6071759425)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5921961964) (.leaf 5776587837)) (.branch 10 (.leaf 5635451979) (.leaf 5498381442))) (.branch 13 (.branch 12 (.leaf 5365214271) (.leaf 5235798503)) (.branch 14 (.leaf 5109991275) (.leaf 4987658045))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4868671878) (.branch 17 (.leaf 4752912825) (.leaf 4640267361))) (.branch 20 (.branch 19 (.leaf 4530627876) (.leaf 4423892228)) (.branch 21 (.leaf 4319963330) (.leaf 4218748788)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4120160561) (.leaf 4024114663)) (.branch 25 (.leaf 3930530890) (.leaf 3839332569))) (.branch 28 (.branch 27 (.leaf 3750446331) (.leaf 3663801902)) (.branch 29 (.leaf 3579331916) (.leaf 3496971741)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3416659314) (.branch 32 (.leaf 3338334999) (.leaf 3261941451))) (.branch 35 (.branch 34 (.leaf 3187423488) (.leaf 3114727975)) (.branch 36 (.leaf 3043803720) (.leaf 2974601373)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2907073332) (.leaf 2841173657)) (.branch 40 (.leaf 2776857991) (.leaf 2714083486))) (.branch 43 (.branch 42 (.leaf 2652808730) (.leaf 2592993682)) (.branch 44 (.leaf 2534599612) (.leaf 2477589044))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2421925697) (.branch 47 (.leaf 2367574442) (.leaf 2314501244))) (.branch 50 (.branch 49 (.leaf 2262673126) (.leaf 2212058121)) (.branch 51 (.leaf 2162625231) (.leaf 2114344393)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2067186439) (.leaf 2021123063)) (.branch 55 (.leaf 1976126790) (.leaf 1932170943))) (.branch 58 (.branch 57 (.leaf 1889229612) (.leaf 1847277631)) (.branch 59 (.leaf 1806290549) (.leaf 1766244602))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1727116694) (.branch 62 (.leaf 1688884370) (.leaf 1651525795))) (.branch 65 (.branch 64 (.leaf 1615019736) (.leaf 1579345535)) (.branch 66 (.leaf 1544483099) (.leaf 1510412872)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1477115827) (.leaf 1444573441)) (.branch 70 (.leaf 1412767683) (.leaf 1381680998))) (.branch 73 (.branch 72 (.leaf 1351296293) (.leaf 1321596919)) (.branch 74 (.leaf 1292566661) (.leaf 1264189726))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1236450724) (.branch 77 (.leaf 1209334662) (.leaf 1182826929))) (.branch 80 (.branch 79 (.leaf 1156913288) (.leaf 1131579859)) (.branch 81 (.leaf 1106813116) (.leaf 1082599870)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1058927265) (.leaf 1035782765)) (.branch 85 (.leaf 1013154144) (.leaf 991029482))) (.branch 88 (.branch 87 (.leaf 969397152) (.leaf 948245814)) (.branch 89 (.leaf 927564406) (.leaf 907342136)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 887568478) (.branch 92 (.leaf 868233159) (.leaf 849326158))) (.branch 95 (.branch 94 (.leaf 830837694) (.leaf 812758225)) (.branch 96 (.leaf 795078437) (.leaf 777789239)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 760881759) (.leaf 744347338)) (.branch 100 (.leaf 728177520) (.leaf 712364054))) (.branch 103 (.branch 102 (.leaf 696898883) (.leaf 681774141)) (.branch 104 (.leaf 666982147) (.leaf 652515404))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 638366588) (.leaf 624528550)) (.branch 108 (.leaf 610994306) (.leaf 597757038))) (.branch 111 (.branch 110 (.leaf 584810085) (.leaf 572146943)) (.branch 112 (.leaf 559761259) (.leaf 547646828)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 535797587) (.leaf 524207616)) (.branch 116 (.leaf 512871130) (.leaf 501782479))) (.branch 119 (.branch 118 (.leaf 490936143) (.leaf 480326728)) (.branch 120 (.leaf 469948965) (.leaf 459797707)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1266).prefactor = (5787967070728149/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1266).cutoff/(generalMeanRows 1266).c)).2 =
    (204590465995887/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1266).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1266).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1266).q*(generalMeanRows 1266).c/2-2 = (107/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable344.value]
    have hcontinuation : (generalMeanRows 1266).q*(generalMeanRows 1266).cutoff/2-2 = (422/71:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable421.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1266).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1266

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1266).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1266).criticalRate j.val*(generalMeanRows 1266).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1266).c*(generalMeanRows 1266).criticalPoint j.val)).2-
      (generalMeanRows 1266).J/2-(generalMeanRows 1266).error (generalMeanGrid j.val)+
      (generalMeanRows 1266).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1266).c)).2-
      (generalMeanRows 1266).J/2-(generalMeanRows 1266).error 4 := by
  have he : (generalMeanRows 1266).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1266) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1266)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1266

/-! Kernel-checked entropy margins for general spectral rectangle 1267. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1267
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7726624716) (.branch 2 (.leaf 7542123302) (.leaf 7363386935))) (.branch 5 (.branch 4 (.leaf 7190127690) (.leaf 7022080760)) (.branch 6 (.leaf 6859001951) (.leaf 6700665507)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6546862201) (.leaf 6397397663)) (.branch 10 (.leaf 6252090911) (.leaf 6110773057))) (.branch 13 (.branch 12 (.leaf 5973286165) (.leaf 5839482237)) (.branch 14 (.leaf 5709222321) (.leaf 5582375712))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5458819243) (.branch 17 (.leaf 5338436656) (.leaf 5221118029))) (.branch 20 (.branch 19 (.leaf 5106759276) (.leaf 4995261688)) (.branch 21 (.leaf 4886531526) (.leaf 4780479649)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4677021182) (.leaf 4576075214)) (.branch 25 (.leaf 4477564524) (.leaf 4381415331))) (.branch 28 (.branch 27 (.leaf 4287557071) (.leaf 4195922185)) (.branch 29 (.leaf 4106445935) (.leaf 4019066227)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3933723455) (.branch 32 (.leaf 3850360356) (.leaf 3768921872))) (.branch 35 (.branch 34 (.leaf 3689355030) (.leaf 3611608825)) (.branch 36 (.leaf 3535634117) (.leaf 3461383532)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3388811367) (.leaf 3317873515)) (.branch 40 (.leaf 3248527376) (.leaf 3180731791))) (.branch 43 (.branch 42 (.leaf 3114446970) (.leaf 3049634429)) (.branch 44 (.leaf 2986256932) (.leaf 2924278431))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2863664017) (.branch 47 (.leaf 2804379869) (.leaf 2746393209))) (.branch 50 (.branch 49 (.leaf 2689672256) (.leaf 2634186186)) (.branch 51 (.leaf 2579905093) (.leaf 2526799954)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2474842591) (.leaf 2424005641)) (.branch 55 (.leaf 2374262523) (.leaf 2325587409))) (.branch 58 (.branch 57 (.leaf 2277955198) (.leaf 2231341486)) (.branch 59 (.leaf 2185722543) (.leaf 2141075289))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2097377271) (.branch 62 (.leaf 2054606638) (.leaf 2012742126))) (.branch 65 (.branch 64 (.leaf 1971763034) (.leaf 1931649207)) (.branch 66 (.leaf 1892381017) (.leaf 1853939344)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1816305565) (.leaf 1779461531)) (.branch 70 (.leaf 1743389558) (.leaf 1708072409))) (.branch 73 (.branch 72 (.leaf 1673493281) (.leaf 1639635791)) (.branch 74 (.leaf 1606483965) (.leaf 1574022224))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1542235371) (.branch 77 (.leaf 1511108585) (.leaf 1480627402))) (.branch 80 (.branch 79 (.leaf 1450777713) (.leaf 1421545745)) (.branch 81 (.leaf 1392918061) (.leaf 1364881542)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1337423382) (.leaf 1310531080)) (.branch 85 (.leaf 1284192429) (.leaf 1258395508))) (.branch 88 (.branch 87 (.leaf 1233128679) (.leaf 1208380573)) (.branch 89 (.leaf 1184140084) (.leaf 1160396367)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1137138824) (.branch 92 (.leaf 1114357103) (.leaf 1092041088))) (.branch 95 (.branch 94 (.leaf 1070180894) (.leaf 1048766863)) (.branch 96 (.leaf 1027789554) (.leaf 1007239741)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 987108406) (.leaf 967386734)) (.branch 100 (.leaf 948066107) (.leaf 929138102))) (.branch 103 (.branch 102 (.leaf 910594481) (.leaf 892427192)) (.branch 104 (.leaf 874628360) (.leaf 857190286))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 840105439) (.leaf 823366455)) (.branch 108 (.leaf 806966134) (.leaf 790897429))) (.branch 111 (.branch 110 (.leaf 775153453) (.leaf 759727465)) (.branch 112 (.leaf 744612874) (.leaf 729803229)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 715292223) (.leaf 701073683)) (.branch 116 (.leaf 687141569) (.leaf 673489974))) (.branch 119 (.branch 118 (.leaf 660113116) (.leaf 647005338)) (.branch 120 (.leaf 634161105) (.leaf 621574999)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1267).prefactor = (1463983749141779/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1267).cutoff/(generalMeanRows 1267).c)).2 =
    (524242815992299/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1267).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1267).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1267).q*(generalMeanRows 1267).cutoff/2-2 = (422/71:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable421.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1267).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1267

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1267).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1267).criticalRate j.val*(generalMeanRows 1267).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1267).c*(generalMeanRows 1267).criticalPoint j.val)).2-
      (generalMeanRows 1267).J/2-(generalMeanRows 1267).error (generalMeanGrid j.val)+
      (generalMeanRows 1267).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1267).c)).2-
      (generalMeanRows 1267).J/2-(generalMeanRows 1267).error 4 := by
  have he : (generalMeanRows 1267).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1267) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1267)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1267

/-! Kernel-checked entropy margins for general spectral rectangle 1268. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1268
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5179999930) (.branch 2 (.leaf 5027377795) (.leaf 4880069582))) (.branch 5 (.branch 4 (.leaf 4737820938) (.leaf 4600396023)) (.branch 6 (.leaf 4467575598) (.leaf 4339155363)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4214944498) (.leaf 4094764386)) (.branch 10 (.leaf 3978447491) (.leaf 3865836365))) (.branch 13 (.branch 12 (.leaf 3756782769) (.leaf 3651146896)) (.branch 14 (.leaf 3548796680) (.leaf 3449607174))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3353459996) (.branch 17 (.leaf 3260242838) (.leaf 3169849014))) (.branch 20 (.branch 19 (.leaf 3082177063) (.leaf 2997130377)) (.branch 21 (.leaf 2914616880) (.leaf 2834548722)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2756842010) (.leaf 2681416557)) (.branch 25 (.leaf 2608195654) (.leaf 2537105863))) (.branch 28 (.branch 27 (.leaf 2468076825) (.leaf 2401041082)) (.branch 29 (.leaf 2335933916) (.leaf 2272693198)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2211259247) (.branch 32 (.leaf 2151574706) (.leaf 2093584418))) (.branch 35 (.branch 34 (.leaf 2037235315) (.leaf 1982476316)) (.branch 36 (.leaf 1929258229) (.leaf 1877533660)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1827256929) (.leaf 1778383991)) (.branch 40 (.leaf 1730872361) (.leaf 1684681043))) (.branch 43 (.branch 42 (.leaf 1639770468) (.leaf 1596102425)) (.branch 44 (.leaf 1553640011) (.leaf 1512347570))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1472190641) (.branch 47 (.leaf 1433135914) (.leaf 1395151177))) (.branch 50 (.branch 49 (.leaf 1358205275) (.leaf 1322268069)) (.branch 51 (.leaf 1287310393) (.leaf 1253304021)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1220221625) (.leaf 1188036746)) (.branch 55 (.leaf 1156723761) (.leaf 1126257846))) (.branch 58 (.branch 57 (.leaf 1096614957) (.leaf 1067771791)) (.branch 59 (.leaf 1039705767) (.leaf 1012394996))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 985818258) (.branch 62 (.leaf 959954979) (.leaf 934785207))) (.branch 65 (.branch 64 (.leaf 910289591) (.leaf 886449360)) (.branch 66 (.leaf 863246308) (.leaf 840662765)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 818681589) (.leaf 797286142)) (.branch 70 (.leaf 776460278) (.leaf 756188322))) (.branch 73 (.branch 72 (.leaf 736455059) (.leaf 717245715)) (.branch 74 (.leaf 698545946) (.leaf 680341824))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 662619822) (.branch 77 (.leaf 645366802) (.leaf 628570002))) (.branch 80 (.branch 79 (.leaf 612217027) (.leaf 596295834)) (.branch 81 (.leaf 580794724) (.leaf 565702328)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 551007601) (.leaf 536699808)) (.branch 85 (.leaf 522768518) (.leaf 509203593))) (.branch 88 (.branch 87 (.leaf 495995179) (.leaf 483133696)) (.branch 89 (.leaf 470609836) (.leaf 458414546)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 446539027) (.branch 92 (.leaf 434974724) (.leaf 423713319))) (.branch 95 (.branch 94 (.leaf 412746725) (.leaf 402067076)) (.branch 96 (.leaf 391666725) (.leaf 381538235)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 371674373) (.leaf 362068104)) (.branch 100 (.leaf 352712586) (.leaf 343601166))) (.branch 103 (.branch 102 (.leaf 334727369) (.leaf 326084899)) (.branch 104 (.leaf 317667631) (.leaf 309469608))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 301485031) (.leaf 293708262)) (.branch 108 (.leaf 286133815) (.leaf 278756350))) (.branch 111 (.branch 110 (.leaf 271570674) (.leaf 264571733)) (.branch 112 (.leaf 257754610) (.leaf 251114520)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 244646805) (.leaf 238346936)) (.branch 116 (.leaf 232210502) (.leaf 226233213))) (.branch 119 (.branch 118 (.leaf 220410891) (.leaf 214739472)) (.branch 120 (.leaf 209215001) (.leaf 203833627)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1268).prefactor = (4971241770317151/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1268).cutoff/(generalMeanRows 1268).c)).2 =
    (1077734676171639/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1268).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1268).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1268).q*(generalMeanRows 1268).cutoff/2-2 = (3424/497:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable424.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1268).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1268

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1268).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1268).criticalRate j.val*(generalMeanRows 1268).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1268).c*(generalMeanRows 1268).criticalPoint j.val)).2-
      (generalMeanRows 1268).J/2-(generalMeanRows 1268).error (generalMeanGrid j.val)+
      (generalMeanRows 1268).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1268).c)).2-
      (generalMeanRows 1268).J/2-(generalMeanRows 1268).error 4 := by
  have he : (generalMeanRows 1268).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1268) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1268)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1268

/-! Kernel-checked entropy margins for general spectral rectangle 1269. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1269
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6042758408) (.branch 2 (.leaf 5881526623) (.leaf 5725561574))) (.branch 5 (.branch 4 (.leaf 5574612997) (.leaf 5428449321)) (.branch 6 (.leaf 5286855702) (.leaf 5149632308)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5016592828) (.leaf 4887563155)) (.branch 10 (.leaf 4762380242) (.leaf 4640891079))) (.branch 13 (.branch 12 (.leaf 4522951803) (.leaf 4408426902)) (.branch 14 (.leaf 4297188508) (.leaf 4189115773))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4084094300) (.branch 17 (.leaf 3982015648) (.leaf 3882776877))) (.branch 20 (.branch 19 (.leaf 3786280145) (.leaf 3692432335)) (.branch 21 (.leaf 3601144733) (.leaf 3512332720)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3425915505) (.leaf 3341815870)) (.branch 25 (.leaf 3259959952) (.leaf 3180277027))) (.branch 28 (.branch 27 (.leaf 3102699326) (.leaf 3027161860)) (.branch 29 (.leaf 2953602254) (.leaf 2881960608)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2812179353) (.branch 32 (.leaf 2744203129) (.leaf 2677978667))) (.branch 35 (.branch 34 (.leaf 2613454679) (.leaf 2550581759)) (.branch 36 (.leaf 2489312289) (.leaf 2429600350)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2371401640) (.leaf 2314673400)) (.branch 40 (.leaf 2259374342) (.leaf 2205464580))) (.branch 43 (.branch 42 (.leaf 2152905566) (.leaf 2101660038)) (.branch 44 (.leaf 2051691954) (.leaf 2002966448))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1955449779) (.branch 47 (.leaf 1909109278) (.leaf 1863913314))) (.branch 50 (.branch 49 (.leaf 1819831246) (.leaf 1776833383)) (.branch 51 (.leaf 1734890950) (.leaf 1693976051)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1654061638) (.leaf 1615121472)) (.branch 55 (.leaf 1577130101) (.leaf 1540062827))) (.branch 58 (.branch 57 (.leaf 1503895678) (.leaf 1468605384)) (.branch 59 (.leaf 1434169351) (.leaf 1400565635))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1367772924) (.branch 62 (.leaf 1335770514) (.leaf 1304538285))) (.branch 65 (.branch 64 (.leaf 1274056687) (.leaf 1244306718)) (.branch 66 (.leaf 1215269903) (.leaf 1186928284)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1159264395) (.leaf 1132261252)) (.branch 70 (.leaf 1105902335) (.leaf 1080171572))) (.branch 73 (.branch 72 (.leaf 1055053331) (.leaf 1030532396)) (.branch 74 (.leaf 1006593964) (.leaf 983223628))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 960407362) (.branch 77 (.leaf 938131515) (.leaf 916382797))) (.branch 80 (.branch 79 (.leaf 895148268) (.leaf 874415328)) (.branch 81 (.leaf 854171705) (.leaf 834405451)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 815104926) (.leaf 796258792)) (.branch 85 (.leaf 777856004) (.leaf 759885803))) (.branch 88 (.branch 87 (.leaf 742337706) (.leaf 725201496)) (.branch 89 (.leaf 708467221) (.leaf 692125180)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 676165920) (.branch 92 (.leaf 660580227) (.leaf 645359120))) (.branch 95 (.branch 94 (.leaf 630493844) (.leaf 615975867)) (.branch 96 (.leaf 601796867) (.leaf 587948736)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 574423563) (.leaf 561213638)) (.branch 100 (.leaf 548311443) (.leaf 535709646))) (.branch 103 (.branch 102 (.leaf 523401096) (.leaf 511378820)) (.branch 104 (.leaf 499636019) (.leaf 488166058))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 476962468) (.leaf 466018938)) (.branch 108 (.leaf 455329314) (.leaf 444887590))) (.branch 111 (.branch 110 (.leaf 434687908) (.leaf 424724553)) (.branch 112 (.leaf 414991950) (.leaf 405484660)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 396197374) (.leaf 387124914)) (.branch 116 (.leaf 378262227) (.leaf 369604383))) (.branch 119 (.branch 118 (.leaf 361146570) (.leaf 352884093)) (.branch 120 (.leaf 344812371) (.leaf 336926931)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1269).prefactor = (1280515388255433/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1269).cutoff/(generalMeanRows 1269).c)).2 =
    (223468762853337/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1269).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1269).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1269).q*(generalMeanRows 1269).c/2-2 = (1453/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable401.value]
    have hcontinuation : (generalMeanRows 1269).q*(generalMeanRows 1269).cutoff/2-2 = (3424/497:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable424.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1269).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1269

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1269).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1269).criticalRate j.val*(generalMeanRows 1269).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1269).c*(generalMeanRows 1269).criticalPoint j.val)).2-
      (generalMeanRows 1269).J/2-(generalMeanRows 1269).error (generalMeanGrid j.val)+
      (generalMeanRows 1269).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1269).c)).2-
      (generalMeanRows 1269).J/2-(generalMeanRows 1269).error 4 := by
  have he : (generalMeanRows 1269).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1269) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1269)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1269

/-! Kernel-checked entropy margins for general spectral rectangle 1270. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1270
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7922034790) (.branch 2 (.leaf 7723812442) (.leaf 7531939291))) (.branch 5 (.branch 4 (.leaf 7346099572) (.leaf 7166002561)) (.branch 6 (.leaf 6991379877) (.leaf 6821983143)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6657581927) (.leaf 6497961942)) (.branch 10 (.leaf 6342923461) (.leaf 6192279925))) (.branch 13 (.branch 12 (.leaf 6045856705) (.leaf 5903490015)) (.branch 14 (.leaf 5765025941) (.leaf 5630319585))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5499234295) (.branch 17 (.leaf 5371640981) (.leaf 5247417506))) (.branch 20 (.branch 19 (.leaf 5126448134) (.leaf 5008623037)) (.branch 21 (.leaf 4893837852) (.leaf 4781993280)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4672994727) (.leaf 4566751968)) (.branch 25 (.leaf 4463178859) (.leaf 4362193058))) (.branch 28 (.branch 27 (.leaf 4263715785) (.leaf 4167671590)) (.branch 29 (.leaf 4073988153) (.leaf 3982596092)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3893428790) (.branch 32 (.leaf 3806422236) (.leaf 3721514877))) (.branch 35 (.branch 34 (.leaf 3638647485) (.leaf 3557763028)) (.branch 36 (.leaf 3478806556) (.leaf 3401725096)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3326467547) (.leaf 3252984588)) (.branch 40 (.leaf 3181228596) (.leaf 3111153559))) (.branch 43 (.branch 42 (.leaf 3042715003) (.leaf 2975869924)) (.branch 44 (.leaf 2910576718) (.leaf 2846795119))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2784486144) (.branch 47 (.leaf 2723612034) (.leaf 2664136205))) (.branch 50 (.branch 49 (.leaf 2606023200) (.leaf 2549238641)) (.branch 51 (.leaf 2493749186) (.leaf 2439522489)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2386527160) (.leaf 2334732730)) (.branch 55 (.leaf 2284109616) (.leaf 2234629084))) (.branch 58 (.branch 57 (.leaf 2186263223) (.leaf 2138984913)) (.branch 59 (.leaf 2092767796) (.leaf 2047586249))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2003415358) (.branch 62 (.leaf 1960230896) (.leaf 1918009297))) (.branch 65 (.branch 64 (.leaf 1876727633) (.leaf 1836363596)) (.branch 66 (.leaf 1796895474) (.leaf 1758302133)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1720562999) (.leaf 1683658038)) (.branch 70 (.leaf 1647567741) (.leaf 1612273106))) (.branch 73 (.branch 72 (.leaf 1577755624) (.leaf 1543997260)) (.branch 74 (.leaf 1510980444) (.leaf 1478688050))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1447103392) (.branch 77 (.leaf 1416210199) (.leaf 1385992615))) (.branch 80 (.branch 79 (.leaf 1356435176) (.leaf 1327522807)) (.branch 81 (.leaf 1299240806) (.leaf 1271574833)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1244510904) (.leaf 1218035376)) (.branch 85 (.leaf 1192134939) (.leaf 1166796610))) (.branch 88 (.branch 87 (.leaf 1142007719) (.leaf 1117755902)) (.branch 89 (.leaf 1094029095) (.leaf 1070815522)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1048103691) (.branch 92 (.leaf 1025882382) (.leaf 1004140645))) (.branch 95 (.branch 94 (.leaf 982867788) (.leaf 962053373)) (.branch 96 (.leaf 941687207) (.leaf 921759340)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 902260053) (.leaf 883179855)) (.branch 100 (.leaf 864509478) (.leaf 846239870))) (.branch 103 (.branch 102 (.leaf 828362187) (.leaf 810867793)) (.branch 104 (.leaf 793748252) (.leaf 776995320))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 760600947) (.leaf 744557264)) (.branch 108 (.leaf 728856585) (.leaf 713491401))) (.branch 111 (.branch 110 (.leaf 698454372) (.leaf 683738328)) (.branch 112 (.leaf 669336261) (.leaf 655241322)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 641446818) (.leaf 627946209)) (.branch 116 (.leaf 614733100) (.leaf 601801243))) (.branch 119 (.branch 118 (.leaf 589144530) (.leaf 576756990)) (.branch 120 (.leaf 564632787) (.leaf 552766215)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1270).prefactor = (3158802862005693/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1270).cutoff/(generalMeanRows 1270).c)).2 =
    (1031391198625297/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1270).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1270).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1270).q*(generalMeanRows 1270).c/2-2 = (104/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable387.value]
    have hcontinuation : (generalMeanRows 1270).q*(generalMeanRows 1270).cutoff/2-2 = (422/71:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable421.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1270).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1270

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1270).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1270).criticalRate j.val*(generalMeanRows 1270).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1270).c*(generalMeanRows 1270).criticalPoint j.val)).2-
      (generalMeanRows 1270).J/2-(generalMeanRows 1270).error (generalMeanGrid j.val)+
      (generalMeanRows 1270).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1270).c)).2-
      (generalMeanRows 1270).J/2-(generalMeanRows 1270).error 4 := by
  have he : (generalMeanRows 1270).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1270) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1270)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1270

/-! Kernel-checked entropy margins for general spectral rectangle 1271. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1271
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4702626235) (.branch 2 (.leaf 4565348831) (.leaf 4432824336))) (.branch 5 (.branch 4 (.leaf 4304825117) (.leaf 4181140179)) (.branch 6 (.leaf 4061573444) (.leaf 3945942253)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3834076052) (.leaf 3725815240)) (.branch 10 (.leaf 3621010158) (.leaf 3519520195))) (.branch 13 (.branch 12 (.leaf 3421212997) (.leaf 3325963766)) (.branch 14 (.leaf 3233654637) (.leaf 3144174118))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3057416596) (.branch 17 (.leaf 2973281891) (.leaf 2891674848))) (.branch 20 (.branch 19 (.leaf 2812504985) (.leaf 2735686156)) (.branch 21 (.leaf 2661136262) (.leaf 2588776978)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2518533510) (.leaf 2450334373)) (.branch 25 (.leaf 2384111181) (.leaf 2319798467))) (.branch 28 (.branch 27 (.leaf 2257333509) (.leaf 2196656167)) (.branch 29 (.leaf 2137708746) (.leaf 2080435855)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2024784285) (.branch 32 (.leaf 1970702893) (.leaf 1918142498))) (.branch 35 (.branch 34 (.leaf 1867055776) (.leaf 1817397170)) (.branch 36 (.leaf 1769122808) (.leaf 1722190412)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1676559235) (.leaf 1632189977)) (.branch 40 (.leaf 1589044731) (.leaf 1547086913))) (.branch 43 (.branch 42 (.leaf 1506281203) (.leaf 1466593497)) (.branch 44 (.leaf 1427990846) (.leaf 1390441414))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1353914427) (.branch 47 (.leaf 1318380131) (.leaf 1283809753))) (.branch 50 (.branch 49 (.leaf 1250175456) (.leaf 1217450308)) (.branch 51 (.leaf 1185608241) (.leaf 1154624022)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1124473220) (.leaf 1095132172)) (.branch 55 (.leaf 1066577959) (.leaf 1038788378))) (.branch 58 (.branch 57 (.leaf 1011741911) (.leaf 985417706)) (.branch 59 (.leaf 959795550) (.leaf 934855845))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 910579589) (.branch 62 (.leaf 886948355) (.leaf 863944269))) (.branch 65 (.branch 64 (.leaf 841549992) (.leaf 819748701)) (.branch 66 (.leaf 798524073) (.leaf 777860269)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 757741912) (.leaf 738154080)) (.branch 70 (.leaf 719082285) (.leaf 700512460))) (.branch 73 (.branch 72 (.leaf 682430947) (.leaf 664824483)) (.branch 74 (.leaf 647680186) (.leaf 630985544))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 614728404) (.branch 77 (.leaf 598896960) (.leaf 583479740))) (.branch 80 (.branch 79 (.leaf 568465599) (.leaf 553843708)) (.branch 81 (.leaf 539603541) (.leaf 525734870)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 512227755) (.leaf 499072532)) (.branch 85 (.leaf 486259810) (.leaf 473780456))) (.branch 88 (.branch 87 (.leaf 461625594) (.leaf 449786592)) (.branch 89 (.leaf 438255060) (.leaf 427022837)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 416081987) (.branch 92 (.leaf 405424795) (.leaf 395043755))) (.branch 95 (.branch 94 (.leaf 384931569) (.leaf 375081137)) (.branch 96 (.leaf 365485554) (.leaf 356138103)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 347032250) (.leaf 338161639)) (.branch 100 (.leaf 329520084) (.leaf 321101570))) (.branch 103 (.branch 102 (.leaf 312900243) (.leaf 304910407)) (.branch 104 (.leaf 297126521) (.leaf 289543191))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 282155171) (.leaf 274957352)) (.branch 108 (.leaf 267944767) (.leaf 261112577))) (.branch 111 (.branch 110 (.leaf 254456077) (.leaf 247970685)) (.branch 112 (.leaf 241651942) (.leaf 235495508)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 229497159) (.leaf 223652783)) (.branch 116 (.leaf 217958377) (.leaf 212410045))) (.branch 119 (.branch 118 (.leaf 207003993) (.leaf 201736531)) (.branch 120 (.leaf 196604062) (.leaf 191603087)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1271).prefactor = (4457252492064499/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1271).cutoff/(generalMeanRows 1271).c)).2 =
    (26865203975149/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1271).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1271).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1271).q*(generalMeanRows 1271).c/2-2 = (8111/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable425.value]
    have hcontinuation : (generalMeanRows 1271).q*(generalMeanRows 1271).cutoff/2-2 = (6834/1001:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable426.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1271).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1271

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1271).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1271).criticalRate j.val*(generalMeanRows 1271).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1271).c*(generalMeanRows 1271).criticalPoint j.val)).2-
      (generalMeanRows 1271).J/2-(generalMeanRows 1271).error (generalMeanGrid j.val)+
      (generalMeanRows 1271).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1271).c)).2-
      (generalMeanRows 1271).J/2-(generalMeanRows 1271).error 4 := by
  have he : (generalMeanRows 1271).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1271) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1271)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1271

/-! Kernel-checked entropy margins for general spectral rectangle 1272. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1272
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4705538997) (.branch 2 (.leaf 4568176565) (.leaf 4435569986))) (.branch 5 (.branch 4 (.leaf 4307491485) (.leaf 4183729938)) (.branch 6 (.leaf 4064089144) (.leaf 3948386333)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3836450842) (.leaf 3728122975)) (.branch 10 (.leaf 3623252978) (.leaf 3521700153))) (.branch 13 (.branch 12 (.leaf 3423332064) (.leaf 3328023837)) (.branch 14 (.leaf 3235657532) (.leaf 3146121589))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3059310331) (.branch 17 (.leaf 2975123513) (.leaf 2893465924))) (.branch 20 (.branch 19 (.leaf 2814247024) (.leaf 2737380614)) (.branch 21 (.leaf 2662784544) (.leaf 2590380442)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2520093466) (.leaf 2451852087)) (.branch 25 (.leaf 2385587877) (.leaf 2321235329))) (.branch 28 (.branch 27 (.leaf 2258731680) (.leaf 2198016755)) (.branch 29 (.leaf 2139032822) (.leaf 2081724457)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2026038417) (.branch 32 (.leaf 1971923528) (.leaf 1919330577))) (.branch 35 (.branch 34 (.leaf 1868212212) (.leaf 1818522849)) (.branch 36 (.leaf 1770218586) (.leaf 1723257121)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1677597679) (.leaf 1633200940)) (.branch 40 (.leaf 1590028971) (.leaf 1548045164))) (.branch 43 (.branch 42 (.leaf 1507214180) (.leaf 1467501891)) (.branch 44 (.leaf 1428875330) (.leaf 1391302640))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1354753028) (.branch 47 (.leaf 1319196723) (.leaf 1284604932))) (.branch 50 (.branch 49 (.leaf 1250949803) (.leaf 1218204385)) (.branch 51 (.leaf 1186342595) (.leaf 1155339186)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1125169708) (.leaf 1095810486)) (.branch 55 (.leaf 1067238588) (.leaf 1039431794))) (.branch 58 (.branch 57 (.leaf 1012368575) (.leaf 986028065)) (.branch 59 (.leaf 960390038) (.leaf 935434885))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 911143593) (.branch 62 (.leaf 887497723) (.leaf 864479388))) (.branch 65 (.branch 64 (.leaf 842071240) (.leaf 820256445)) (.branch 66 (.leaf 799018671) (.leaf 778342068)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 758211250) (.leaf 738611286)) (.branch 70 (.leaf 719527678) (.leaf 700946351))) (.branch 73 (.branch 72 (.leaf 682853638) (.leaf 665236269)) (.branch 74 (.leaf 648081353) (.leaf 631376371))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 615109161) (.branch 77 (.leaf 599267911) (.leaf 583841142))) (.branch 80 (.branch 79 (.leaf 568817701) (.leaf 554186753)) (.branch 81 (.leaf 539937766) (.leaf 526060505)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 512545024) (.leaf 499381653)) (.branch 85 (.leaf 486560995) (.leaf 474073911))) (.branch 88 (.branch 87 (.leaf 461911520) (.leaf 450065186)) (.branch 89 (.leaf 438526511) (.leaf 427287330)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 416339704) (.branch 92 (.leaf 405675911) (.leaf 395288441))) (.branch 95 (.branch 94 (.leaf 385169992) (.leaf 375313459)) (.branch 96 (.leaf 365711932) (.leaf 356358692)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 347247199) (.leaf 338371093)) (.branch 100 (.leaf 329724186) (.leaf 321300457))) (.branch 103 (.branch 102 (.leaf 313094050) (.leaf 305099266)) (.branch 104 (.leaf 297310558) (.leaf 289722532))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 282329935) (.leaf 275127658)) (.branch 108 (.leaf 268110729) (.leaf 261274308))) (.branch 111 (.branch 110 (.leaf 254613685) (.leaf 248124276)) (.branch 112 (.leaf 241801619) (.leaf 235641372)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 229639307) (.leaf 223791311)) (.branch 116 (.leaf 218093378) (.leaf 212541609))) (.branch 119 (.branch 118 (.leaf 207132210) (.leaf 201861484)) (.branch 120 (.leaf 196725836) (.leaf 191721764)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1272).prefactor = (2230006636059231/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1272).cutoff/(generalMeanRows 1272).c)).2 =
    (26865203975149/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1272).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1272).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1272).q*(generalMeanRows 1272).c/2-2 = (8111/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable425.value]
    have hcontinuation : (generalMeanRows 1272).q*(generalMeanRows 1272).cutoff/2-2 = (6834/1001:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable426.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1272).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1272

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1272).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1272).criticalRate j.val*(generalMeanRows 1272).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1272).c*(generalMeanRows 1272).criticalPoint j.val)).2-
      (generalMeanRows 1272).J/2-(generalMeanRows 1272).error (generalMeanGrid j.val)+
      (generalMeanRows 1272).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1272).c)).2-
      (generalMeanRows 1272).J/2-(generalMeanRows 1272).error 4 := by
  have he : (generalMeanRows 1272).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1272) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1272)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1272

/-! Kernel-checked entropy margins for general spectral rectangle 1273. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1273
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4979558242) (.branch 2 (.leaf 4844179521) (.leaf 4713231141))) (.branch 5 (.branch 4 (.leaf 4586508917) (.leaf 4463823159)) (.branch 6 (.leaf 4344997203) (.leaf 4229866126)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4118275630) (.leaf 4010081053)) (.branch 10 (.leaf 3905146503) (.leaf 3803344090))) (.branch 13 (.branch 12 (.leaf 3704553248) (.leaf 3608660129)) (.branch 14 (.leaf 3515557063) (.leaf 3425142077))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3337318459) (.branch 17 (.leaf 3251994373) (.leaf 3169082503))) (.branch 20 (.branch 19 (.leaf 3088499736) (.leaf 3010166877)) (.branch 21 (.leaf 2934008382) (.leaf 2859952124)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2787929171) (.leaf 2717873593)) (.branch 25 (.leaf 2649722271) (.leaf 2583414736))) (.branch 28 (.branch 27 (.leaf 2518893012) (.leaf 2456101473)) (.branch 29 (.leaf 2394986715) (.leaf 2335497430)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2277584295) (.branch 32 (.leaf 2221199868) (.leaf 2166298493))) (.branch 35 (.branch 34 (.leaf 2112836204) (.leaf 2060770645)) (.branch 36 (.leaf 2010060992) (.leaf 1960667874)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1912553312) (.leaf 1865680648)) (.branch 40 (.leaf 1820014487) (.leaf 1775520641))) (.branch 43 (.branch 42 (.leaf 1732166074) (.leaf 1689918852)) (.branch 44 (.leaf 1648748098) (.leaf 1608623944))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1569517491) (.branch 47 (.leaf 1531400767) (.leaf 1494246693))) (.branch 50 (.branch 49 (.leaf 1458029043) (.leaf 1422722415)) (.branch 51 (.leaf 1388302193) (.leaf 1354744523)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1322026278) (.leaf 1290125037)) (.branch 55 (.leaf 1259019051) (.leaf 1228687227))) (.branch 58 (.branch 57 (.leaf 1199109098) (.leaf 1170264800)) (.branch 59 (.leaf 1142135057) (.leaf 1114701154))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1087944918) (.branch 62 (.leaf 1061848704) (.leaf 1036395370))) (.branch 65 (.branch 64 (.leaf 1011568268) (.leaf 987351221)) (.branch 66 (.leaf 963728507) (.leaf 940684851)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 918205403) (.leaf 896275728)) (.branch 70 (.leaf 874881791) (.leaf 854009944))) (.branch 73 (.branch 72 (.leaf 833646918) (.leaf 813779804)) (.branch 74 (.leaf 794396047) (.leaf 775483433))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 757030080) (.branch 77 (.leaf 739024425) (.leaf 721455218))) (.branch 80 (.branch 79 (.leaf 704311509) (.leaf 687582642)) (.branch 81 (.leaf 671258243) (.leaf 655328215)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 639782728) (.leaf 624612211)) (.branch 85 (.leaf 609807345) (.leaf 595359055))) (.branch 88 (.branch 87 (.leaf 581258505) (.leaf 567497088)) (.branch 89 (.leaf 554066423) (.leaf 540958344)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 528164898) (.branch 92 (.leaf 515678338) (.leaf 503491117))) (.branch 95 (.branch 94 (.leaf 491595880) (.leaf 479985462)) (.branch 96 (.leaf 468652884) (.leaf 457591340)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 446794203) (.leaf 436255012)) (.branch 100 (.leaf 425967470) (.leaf 415925440))) (.branch 103 (.branch 102 (.leaf 406122941) (.leaf 396554144)) (.branch 104 (.leaf 387213364) (.leaf 378095062))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 369193837) (.leaf 360504425)) (.branch 108 (.leaf 352021691) (.leaf 343740630))) (.branch 111 (.branch 110 (.leaf 335656365) (.leaf 327764135)) (.branch 112 (.leaf 320059303) (.leaf 312537344)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 305193846) (.leaf 298024508)) (.branch 116 (.leaf 291025134) (.leaf 284191632))) (.branch 119 (.branch 118 (.leaf 277520012) (.leaf 271006382)) (.branch 120 (.leaf 264646946) (.leaf 258438001)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1273).prefactor = (424147572261763/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1273).cutoff/(generalMeanRows 1273).c)).2 =
    (1227655288969521/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1273).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1273).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1273).q*(generalMeanRows 1273).cutoff/2-2 = (865/108:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable427.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1273).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1273

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1273).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1273).criticalRate j.val*(generalMeanRows 1273).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1273).c*(generalMeanRows 1273).criticalPoint j.val)).2-
      (generalMeanRows 1273).J/2-(generalMeanRows 1273).error (generalMeanGrid j.val)+
      (generalMeanRows 1273).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1273).c)).2-
      (generalMeanRows 1273).J/2-(generalMeanRows 1273).error 4 := by
  have he : (generalMeanRows 1273).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1273) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1273)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1273

/-! Kernel-checked entropy margins for general spectral rectangle 1274. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1274
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5194958940) (.branch 2 (.leaf 5056548315) (.leaf 4922610187))) (.branch 5 (.branch 4 (.leaf 4792938650) (.leaf 4667342497)) (.branch 6 (.leaf 4545643719) (.leaf 4427676203)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4313284592) (.leaf 4202323280)) (.branch 10 (.leaf 4094655533) (.leaf 3990152707))) (.branch 13 (.branch 12 (.leaf 3888693559) (.leaf 3790163632)) (.branch 14 (.leaf 3694454705) (.leaf 3601464308))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3511095276) (.branch 17 (.leaf 3423255359) (.leaf 3337856861))) (.branch 20 (.branch 19 (.leaf 3254816324) (.leaf 3174054229)) (.branch 21 (.leaf 3095494733) (.leaf 3019065430)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2944697129) (.leaf 2872323649)) (.branch 25 (.leaf 2801881641) (.leaf 2733310413))) (.branch 28 (.branch 27 (.leaf 2666551774) (.leaf 2601549894)) (.branch 29 (.leaf 2538251170) (.leaf 2476604102)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2416559177) (.branch 32 (.leaf 2358068772) (.leaf 2301087045))) (.branch 35 (.branch 34 (.leaf 2245569855) (.leaf 2191474667)) (.branch 36 (.leaf 2138760481) (.leaf 2087387751)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2037318323) (.leaf 1988515364)) (.branch 40 (.leaf 1940943305) (.leaf 1894567782))) (.branch 43 (.branch 42 (.leaf 1849355583) (.leaf 1805274599)) (.branch 44 (.leaf 1762293773) (.leaf 1720383060))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1679513380) (.branch 47 (.leaf 1639656581) (.leaf 1600785402))) (.branch 50 (.branch 49 (.leaf 1562873434) (.leaf 1525895089)) (.branch 51 (.leaf 1489825566) (.leaf 1454640824)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1420317548) (.leaf 1386833126)) (.branch 55 (.leaf 1354165622) (.leaf 1322293747))) (.branch 58 (.branch 57 (.leaf 1291196842) (.leaf 1260854853)) (.branch 59 (.leaf 1231248305) (.leaf 1202358288))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1174166435) (.branch 62 (.leaf 1146654902) (.leaf 1119806352))) (.branch 65 (.branch 64 (.leaf 1093603935) (.leaf 1068031276)) (.branch 66 (.leaf 1043072456) (.leaf 1018711999)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 994934854) (.leaf 971726387)) (.branch 70 (.leaf 949072363) (.leaf 926958935))) (.branch 73 (.branch 72 (.leaf 905372631) (.leaf 884300342)) (.branch 74 (.leaf 863729315) (.leaf 843647135))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 824041721) (.branch 77 (.leaf 804901310) (.leaf 786214453))) (.branch 80 (.branch 79 (.leaf 767970003) (.leaf 750157105)) (.branch 81 (.leaf 732765188) (.leaf 715783959)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 699203391) (.leaf 683013719)) (.branch 85 (.leaf 667205430) (.leaf 651769255))) (.branch 88 (.branch 87 (.leaf 636696165) (.leaf 621977362)) (.branch 89 (.leaf 607604273) (.leaf 593568545)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 579862036) (.branch 92 (.leaf 566476811) (.leaf 553405136))) (.branch 95 (.branch 94 (.leaf 540639472) (.leaf 528172472)) (.branch 96 (.leaf 515996970) (.leaf 504105983)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 492492702) (.leaf 481150488)) (.branch 100 (.leaf 470072866) (.leaf 459253525))) (.branch 103 (.branch 102 (.leaf 448686309) (.leaf 438365214)) (.branch 104 (.leaf 428284386) (.leaf 418438115))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 408820831) (.leaf 399427103)) (.branch 108 (.leaf 390251632) (.leaf 381289248))) (.branch 111 (.branch 110 (.leaf 372534911) (.leaf 363983701)) (.branch 112 (.leaf 355630819) (.leaf 347471583)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 339501427) (.leaf 331715893)) (.branch 116 (.leaf 324110633) (.leaf 316681404))) (.branch 119 (.branch 118 (.leaf 309424065) (.leaf 302334577)) (.branch 120 (.leaf 295408996) (.leaf 288643477)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1274).prefactor = (4318505616926999/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1274).cutoff/(generalMeanRows 1274).c)).2 =
    (308882336350107/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1274).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1274).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1274).q*(generalMeanRows 1274).cutoff/2-2 = (865/108:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable427.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1274).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1274

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1274).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1274).criticalRate j.val*(generalMeanRows 1274).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1274).c*(generalMeanRows 1274).criticalPoint j.val)).2-
      (generalMeanRows 1274).J/2-(generalMeanRows 1274).error (generalMeanGrid j.val)+
      (generalMeanRows 1274).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1274).c)).2-
      (generalMeanRows 1274).J/2-(generalMeanRows 1274).error 4 := by
  have he : (generalMeanRows 1274).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1274) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1274)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1274

/-! Kernel-checked entropy margins for general spectral rectangle 1275. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1275
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5387347907) (.branch 2 (.leaf 5246741008) (.leaf 5110620377))) (.branch 5 (.branch 4 (.leaf 4978779616) (.leaf 4851027137)) (.branch 6 (.leaf 4727184656) (.leaf 4607085865)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4490575285) (.leaf 4377507250)) (.branch 10 (.leaf 4267745012) (.leaf 4161159960))) (.branch 13 (.branch 12 (.leaf 4057630917) (.leaf 3957043520)) (.branch 14 (.leaf 3859289668) (.leaf 3764267026))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3671878583) (.branch 17 (.leaf 3582032252) (.leaf 3494640510))) (.branch 20 (.branch 19 (.leaf 3409620075) (.leaf 3326891610)) (.branch 21 (.leaf 3246379457) (.leaf 3168011392)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3091718406) (.leaf 3017434498)) (.branch 25 (.leaf 2945096493) (.leaf 2874643871))) (.branch 28 (.branch 27 (.leaf 2806018607) (.leaf 2739165031)) (.branch 29 (.leaf 2674029691) (.leaf 2610561235)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2548710291) (.branch 32 (.leaf 2488429364) (.leaf 2429672739))) (.branch 35 (.branch 34 (.leaf 2372396388) (.leaf 2316557885)) (.branch 36 (.leaf 2262116330) (.leaf 2209032270)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2157267633) (.leaf 2106785661)) (.branch 40 (.leaf 2057550854) (.leaf 2009528906))) (.branch 43 (.branch 42 (.leaf 1962686658) (.leaf 1916992045)) (.branch 44 (.leaf 1872414046) (.leaf 1828922645))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1786488784) (.branch 47 (.leaf 1745084327) (.leaf 1704682018))) (.branch 50 (.branch 49 (.leaf 1665255451) (.leaf 1626779032)) (.branch 51 (.leaf 1589227949) (.leaf 1552578141)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1516806270) (.leaf 1481889694)) (.branch 55 (.leaf 1447806440) (.leaf 1414535181))) (.branch 58 (.branch 57 (.leaf 1382055209) (.leaf 1350346419)) (.branch 59 (.leaf 1319389282) (.leaf 1289164825))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1259654616) (.branch 62 (.leaf 1230840741) (.leaf 1202705790))) (.branch 65 (.branch 64 (.leaf 1175232836) (.leaf 1148405421)) (.branch 66 (.leaf 1122207541) (.leaf 1096623632)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1071638552) (.leaf 1047237570)) (.branch 70 (.leaf 1023406355) (.leaf 1000130957))) (.branch 73 (.branch 72 (.leaf 977397802) (.leaf 955193676)) (.branch 74 (.leaf 933505715) (.leaf 912321397))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 891628524) (.branch 77 (.leaf 871415222) (.leaf 851669924))) (.branch 80 (.branch 79 (.leaf 832381365) (.leaf 813538569)) (.branch 81 (.leaf 795130846) (.leaf 777147778)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 759579216) (.leaf 742415269)) (.branch 85 (.leaf 725646296) (.leaf 709262903))) (.branch 88 (.branch 87 (.leaf 693255933) (.leaf 677616458)) (.branch 89 (.leaf 662335777) (.leaf 647405405)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 632817070) (.branch 92 (.leaf 618562706) (.leaf 604634447))) (.branch 95 (.branch 94 (.leaf 591024624) (.leaf 577725756)) (.branch 96 (.leaf 564730546) (.leaf 552031879)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 539622813) (.leaf 527496577)) (.branch 100 (.leaf 515646564) (.leaf 504066331))) (.branch 103 (.branch 102 (.leaf 492749591) (.leaf 481690207)) (.branch 104 (.leaf 470882195) (.leaf 460319714))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 449997065) (.leaf 439908684)) (.branch 108 (.leaf 430049144) (.leaf 420413147))) (.branch 111 (.branch 110 (.leaf 410995524) (.leaf 401791226)) (.branch 112 (.leaf 392795329) (.leaf 384003023)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 375409617) (.leaf 367010528)) (.branch 116 (.leaf 358801282) (.leaf 350777515))) (.branch 119 (.branch 118 (.leaf 342934963) (.leaf 335269463)) (.branch 120 (.leaf 327776953) (.leaf 320453464)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1275).prefactor = (4370634514331987/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1275).cutoff/(generalMeanRows 1275).c)).2 =
    (248693178999233/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1275).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1275).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1275).q*(generalMeanRows 1275).c/2-2 = (1773/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable428.value]
    have hcontinuation : (generalMeanRows 1275).q*(generalMeanRows 1275).cutoff/2-2 = (865/108:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable427.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1275).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1275

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1275).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1275).criticalRate j.val*(generalMeanRows 1275).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1275).c*(generalMeanRows 1275).criticalPoint j.val)).2-
      (generalMeanRows 1275).J/2-(generalMeanRows 1275).error (generalMeanGrid j.val)+
      (generalMeanRows 1275).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1275).c)).2-
      (generalMeanRows 1275).J/2-(generalMeanRows 1275).error 4 := by
  have he : (generalMeanRows 1275).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1275) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1275)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1275

/-! Kernel-checked entropy margins for general spectral rectangle 1276. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1276
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5551400089) (.branch 2 (.leaf 5406511515) (.leaf 5266245824))) (.branch 5 (.branch 4 (.leaf 5130390329) (.leaf 4998747611)) (.branch 6 (.leaf 4871133955) (.leaf 4747377990)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4627319503) (.leaf 4510808389)) (.branch 10 (.leaf 4397703740) (.leaf 4287873026))) (.branch 13 (.branch 12 (.leaf 4181191381) (.leaf 4077540959)) (.branch 14 (.leaf 3976810367) (.leaf 3878894154))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3783692355) (.branch 17 (.leaf 3691110079) (.leaf 3601057138))) (.branch 20 (.branch 19 (.leaf 3513447713) (.leaf 3428200053)) (.branch 21 (.leaf 3345236194) (.leaf 3264481713)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3185865500) (.leaf 3109319545)) (.branch 25 (.leaf 3034778748) (.leaf 2962180745))) (.branch 28 (.branch 27 (.leaf 2891465747) (.leaf 2822576387)) (.branch 29 (.leaf 2755457587) (.leaf 2690056429)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2626322038) (.branch 32 (.leaf 2564205474) (.leaf 2503659628))) (.branch 35 (.branch 34 (.leaf 2444639133) (.leaf 2387100271)) (.branch 36 (.leaf 2331000896) (.leaf 2276300353)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2222959410) (.leaf 2170940193)) (.branch 40 (.leaf 2120206118) (.leaf 2070721836))) (.branch 43 (.branch 42 (.leaf 2022453177) (.leaf 1975367099)) (.branch 44 (.leaf 1929431639) (.leaf 1884615864))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1840889834) (.branch 47 (.leaf 1798224554) (.leaf 1756591939))) (.branch 50 (.branch 49 (.leaf 1715964779) (.leaf 1676316700)) (.branch 51 (.leaf 1637622134) (.leaf 1599856289)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1562995115) (.leaf 1527015281)) (.branch 55 (.leaf 1491894145) (.leaf 1457609730))) (.branch 58 (.branch 57 (.leaf 1424140699) (.leaf 1391466332)) (.branch 59 (.leaf 1359566507) (.leaf 1328421674))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1298012838) (.branch 62 (.leaf 1268321541) (.leaf 1239329842))) (.branch 65 (.branch 64 (.leaf 1211020298) (.leaf 1183375951)) (.branch 66 (.leaf 1156380310) (.leaf 1130017336)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1104271425) (.leaf 1079127400)) (.branch 70 (.leaf 1054570491) (.leaf 1030586325))) (.branch 73 (.branch 72 (.leaf 1007160914) (.leaf 984280642)) (.branch 74 (.leaf 961932253) (.leaf 940102843))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 918779844) (.branch 77 (.leaf 897951019) (.leaf 877604449))) (.branch 80 (.branch 79 (.leaf 857728527) (.leaf 838311942)) (.branch 81 (.leaf 819343678) (.leaf 800813001)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 782709452) (.leaf 765022838)) (.branch 85 (.leaf 747743227) (.leaf 730860938))) (.branch 88 (.branch 87 (.leaf 714366533) (.leaf 698250815)) (.branch 89 (.leaf 682504816) (.leaf 667119793)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 652087223) (.branch 92 (.leaf 637398794) (.leaf 623046401))) (.branch 95 (.branch 94 (.leaf 609022140) (.leaf 595318303)) (.branch 96 (.leaf 581927371) (.leaf 568842012)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 556055073) (.leaf 543559576)) (.branch 100 (.leaf 531348714) (.leaf 519415847))) (.branch 103 (.branch 102 (.leaf 507754496) (.leaf 496358339)) (.branch 104 (.leaf 485221208) (.leaf 474337085))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 463700097) (.leaf 453304511)) (.branch 108 (.leaf 443144734) (.leaf 433215308))) (.branch 111 (.branch 110 (.leaf 423510905) (.leaf 414026323)) (.branch 112 (.leaf 404756489) (.leaf 395696446)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 386841358) (.leaf 378186505)) (.branch 116 (.leaf 369727277) (.leaf 361459175))) (.branch 119 (.branch 118 (.leaf 353377806) (.leaf 345478881)) (.branch 120 (.leaf 337758214) (.leaf 330211715)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1276).prefactor = (4503726369576127/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1276).cutoff/(generalMeanRows 1276).c)).2 =
    (248693178999233/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1276).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1276).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1276).q*(generalMeanRows 1276).c/2-2 = (1773/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable428.value]
    have hcontinuation : (generalMeanRows 1276).q*(generalMeanRows 1276).cutoff/2-2 = (865/108:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable427.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1276).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1276

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1276).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1276).criticalRate j.val*(generalMeanRows 1276).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1276).c*(generalMeanRows 1276).criticalPoint j.val)).2-
      (generalMeanRows 1276).J/2-(generalMeanRows 1276).error (generalMeanGrid j.val)+
      (generalMeanRows 1276).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1276).c)).2-
      (generalMeanRows 1276).J/2-(generalMeanRows 1276).error 4 := by
  have he : (generalMeanRows 1276).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1276) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1276)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1276

/-! Kernel-checked entropy margins for general spectral rectangle 1277. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1277
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5933575729) (.branch 2 (.leaf 5783554212) (.leaf 5638229486))) (.branch 5 (.branch 4 (.leaf 5497385505) (.leaf 5360821866)) (.branch 6 (.leaf 5228352198) (.leaf 5099802766)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4975011239) (.leaf 4853825623)) (.branch 10 (.leaf 4736103309) (.leaf 4621710242))) (.branch 13 (.branch 12 (.leaf 4510520180) (.leaf 4402414035)) (.branch 14 (.leaf 4297279290) (.leaf 4195009476))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4095503699) (.branch 17 (.leaf 3998666221) (.leaf 3904406080))) (.branch 20 (.branch 19 (.leaf 3812636750) (.leaf 3723275822)) (.branch 21 (.leaf 3636244732) (.leaf 3551468496)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3468875483) (.leaf 3388397196)) (.branch 25 (.leaf 3309968081) (.leaf 3233525345))) (.branch 28 (.branch 27 (.leaf 3159008791) (.leaf 3086360668)) (.branch 29 (.leaf 3015525530) (.leaf 2946450108)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2879083188) (.branch 32 (.leaf 2813375503) (.leaf 2749279630))) (.branch 35 (.branch 34 (.leaf 2686749893) (.leaf 2625742273)) (.branch 36 (.leaf 2566214330) (.leaf 2508125121)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2451435130) (.leaf 2396106198)) (.branch 40 (.leaf 2342101466) (.leaf 2289385307))) (.branch 43 (.branch 42 (.leaf 2237923278) (.leaf 2187682062)) (.branch 44 (.leaf 2138629422) (.leaf 2090734155))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2043966046) (.branch 47 (.leaf 1998295829) (.leaf 1953695145))) (.branch 50 (.branch 49 (.leaf 1910136510) (.leaf 1867593275)) (.branch 51 (.leaf 1826039597) (.leaf 1785450407)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1745801377) (.leaf 1707068896)) (.branch 55 (.leaf 1669230044) (.leaf 1632262561))) (.branch 58 (.branch 57 (.leaf 1596144828) (.leaf 1560855841)) (.branch 59 (.leaf 1526375193) (.leaf 1492683048))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1459760124) (.branch 62 (.leaf 1427587675) (.leaf 1396147468))) (.branch 65 (.branch 64 (.leaf 1365421773) (.leaf 1335393339)) (.branch 66 (.leaf 1306045383) (.leaf 1277361574)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1249326015) (.leaf 1221923234)) (.branch 70 (.leaf 1195138167) (.leaf 1168956147))) (.branch 73 (.branch 72 (.leaf 1143362889) (.leaf 1118344483)) (.branch 74 (.leaf 1093887378) (.leaf 1069978373))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1046604605) (.branch 77 (.leaf 1023753542) (.leaf 1001412971))) (.branch 80 (.branch 79 (.leaf 979570986) (.leaf 958215986)) (.branch 81 (.leaf 937336659) (.leaf 916921978)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 896961189) (.leaf 877443809)) (.branch 85 (.leaf 858359614) (.leaf 839698631))) (.branch 88 (.branch 87 (.leaf 821451134) (.leaf 803607636)) (.branch 89 (.leaf 786158882) (.leaf 769095843)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 752409708) (.branch 92 (.leaf 736091884) (.leaf 720133980))) (.branch 95 (.branch 94 (.leaf 704527813) (.leaf 689265393)) (.branch 96 (.leaf 674338923) (.leaf 659740794)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 645463577) (.leaf 631500019)) (.branch 100 (.leaf 617843043) (.leaf 604485737))) (.branch 103 (.branch 102 (.leaf 591421352) (.leaf 578643301)) (.branch 104 (.leaf 566145149) (.leaf 553920614))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 541963563) (.leaf 530268002)) (.branch 108 (.leaf 518828082) (.leaf 507638087))) (.branch 111 (.branch 110 (.leaf 496692436) (.leaf 485985676)) (.branch 112 (.leaf 475512482) (.leaf 465267652)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 455246103) (.leaf 445442872)) (.branch 116 (.leaf 435853107) (.leaf 426472071))) (.branch 119 (.branch 118 (.leaf 417295132) (.leaf 408317768)) (.branch 120 (.leaf 399535559) (.leaf 390944186)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1277).prefactor = (4640871055564699/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1277).cutoff/(generalMeanRows 1277).c)).2 =
    (251098017592593/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1277).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1277).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1277).q*(generalMeanRows 1277).c/2-2 = (213/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable069.value]
    have hcontinuation : (generalMeanRows 1277).q*(generalMeanRows 1277).cutoff/2-2 = (865/108:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable427.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1277).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1277

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1277).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1277).criticalRate j.val*(generalMeanRows 1277).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1277).c*(generalMeanRows 1277).criticalPoint j.val)).2-
      (generalMeanRows 1277).J/2-(generalMeanRows 1277).error (generalMeanGrid j.val)+
      (generalMeanRows 1277).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1277).c)).2-
      (generalMeanRows 1277).J/2-(generalMeanRows 1277).error 4 := by
  have he : (generalMeanRows 1277).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1277) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1277)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1277

/-! Kernel-checked entropy margins for general spectral rectangle 1278. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1278
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6420251657) (.branch 2 (.leaf 6264913639) (.leaf 6114318362))) (.branch 5 (.branch 4 (.leaf 5968247366) (.leaf 5826498197)) (.branch 6 (.leaf 5688882755) (.leaf 5555225849)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5425363932) (.leaf 5299143998)) (.branch 10 (.leaf 5176422607) (.leaf 5057065027))) (.branch 13 (.branch 12 (.leaf 4940944471) (.leaf 4827941426)) (.branch 14 (.leaf 4717943045) (.leaf 4610842618))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4506539083) (.branch 17 (.leaf 4404936598) (.leaf 4305944152))) (.branch 20 (.branch 19 (.leaf 4209475210) (.leaf 4115447400)) (.branch 21 (.leaf 4023782222) (.leaf 3934404786)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3847243573) (.leaf 3762230218)) (.branch 25 (.leaf 3679299313) (.leaf 3598388217))) (.branch 28 (.branch 27 (.leaf 3519436896) (.leaf 3442387766)) (.branch 29 (.leaf 3367185548) (.leaf 3293777142)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3222111502) (.branch 32 (.leaf 3152139524) (.leaf 3083813945))) (.branch 35 (.branch 34 (.leaf 3017089241) (.leaf 2951921543)) (.branch 36 (.leaf 2888268549) (.leaf 2826089448)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2765344847) (.leaf 2705996702)) (.branch 40 (.leaf 2648008256) (.leaf 2591343976))) (.branch 43 (.branch 42 (.leaf 2535969504) (.leaf 2481851595)) (.branch 44 (.leaf 2428958075) (.leaf 2377257793))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2326720574) (.branch 47 (.leaf 2277317182) (.leaf 2229019278))) (.branch 50 (.branch 49 (.leaf 2181799387) (.leaf 2135630858)) (.branch 51 (.leaf 2090487836) (.leaf 2046345228)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2003178675) (.leaf 1960964523)) (.branch 55 (.leaf 1919679797) (.leaf 1879302177))) (.branch 58 (.branch 57 (.leaf 1839809972) (.leaf 1801182098)) (.branch 59 (.leaf 1763398057) (.leaf 1726437914))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1690282283) (.branch 62 (.leaf 1654912299) (.leaf 1620309610))) (.branch 65 (.branch 64 (.leaf 1586456352) (.leaf 1553335138)) (.branch 66 (.leaf 1520929039) (.leaf 1489221571)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1458196679) (.leaf 1427838725)) (.branch 70 (.leaf 1398132473) (.leaf 1369063078))) (.branch 73 (.branch 72 (.leaf 1340616073) (.leaf 1312777358)) (.branch 74 (.leaf 1285533188) (.leaf 1258870163))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1232775217) (.branch 77 (.leaf 1207235608) (.leaf 1182238911))) (.branch 80 (.branch 79 (.leaf 1157773003) (.leaf 1133826061)) (.branch 81 (.leaf 1110386550) (.leaf 1087443214)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1064985069) (.leaf 1043001397)) (.branch 85 (.leaf 1021481735) (.leaf 1000415871))) (.branch 88 (.branch 87 (.leaf 979793838) (.leaf 959605902)) (.branch 89 (.leaf 939842562) (.leaf 920494538)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 901552771) (.branch 92 (.leaf 883008412) (.leaf 864852818))) (.branch 95 (.branch 94 (.leaf 847077548) (.leaf 829674358)) (.branch 96 (.leaf 812635191) (.leaf 795952179)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 779617633) (.leaf 763624041)) (.branch 100 (.leaf 747964062) (.leaf 732630524))) (.branch 103 (.branch 102 (.leaf 717616416) (.leaf 702914888)) (.branch 104 (.leaf 688519243) (.leaf 674422938))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 660619573) (.leaf 647102897)) (.branch 108 (.leaf 633866796) (.leaf 620905293))) (.branch 111 (.branch 110 (.leaf 608212546) (.leaf 595782842)) (.branch 112 (.leaf 583610594) (.leaf 571690342)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 560016744) (.leaf 548584579)) (.branch 116 (.leaf 537388738) (.leaf 526424228))) (.branch 119 (.branch 118 (.leaf 515686163) (.leaf 505169766)) (.branch 120 (.leaf 494870364) (.leaf 484783387)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1278).prefactor = (4782191986589367/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1278).cutoff/(generalMeanRows 1278).c)).2 =
    (1271750608834747/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1278).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1278).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1278).q*(generalMeanRows 1278).cutoff/2-2 = (865/108:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable427.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1278).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1278

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1278).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1278).criticalRate j.val*(generalMeanRows 1278).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1278).c*(generalMeanRows 1278).criticalPoint j.val)).2-
      (generalMeanRows 1278).J/2-(generalMeanRows 1278).error (generalMeanGrid j.val)+
      (generalMeanRows 1278).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1278).c)).2-
      (generalMeanRows 1278).J/2-(generalMeanRows 1278).error 4 := by
  have he : (generalMeanRows 1278).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1278) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1278)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1278

/-! Kernel-checked entropy margins for general spectral rectangle 1279. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1279
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7699554073) (.branch 2 (.leaf 7511190320) (.leaf 7328685287))) (.branch 5 (.branch 4 (.leaf 7151758980) (.leaf 6980152904)) (.branch 6 (.leaf 6813627774) (.leaf 6651961510)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6494947493) (.leaf 6342393038)) (.branch 10 (.leaf 6194118049) (.leaf 6049953842))) (.branch 13 (.branch 12 (.leaf 5909742100) (.leaf 5773333951)) (.branch 14 (.leaf 5640589150) (.leaf 5511375349))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5385567452) (.branch 17 (.leaf 5263047029) (.leaf 5143701799))) (.branch 20 (.branch 19 (.leaf 5027425163) (.leaf 4914115780)) (.branch 21 (.leaf 4803677190) (.leaf 4696017467)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4591048910) (.leaf 4488687761)) (.branch 25 (.leaf 4388853940) (.leaf 4291470819))) (.branch 28 (.branch 27 (.leaf 4196465000) (.leaf 4103766119)) (.branch 29 (.leaf 4013306667) (.leaf 3925021823)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3838849299) (.branch 32 (.leaf 3754729200) (.leaf 3672603892))) (.branch 35 (.branch 34 (.leaf 3592417882) (.leaf 3514117707)) (.branch 36 (.leaf 3437651824) (.leaf 3362970520)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3290025819) (.leaf 3218771393)) (.branch 40 (.leaf 3149162491) (.leaf 3081155862))) (.branch 43 (.branch 42 (.leaf 3014709683) (.leaf 2949783498)) (.branch 44 (.leaf 2886338158) (.leaf 2824335760))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2763739597) (.branch 47 (.leaf 2704514106) (.leaf 2646624819))) (.branch 50 (.branch 49 (.leaf 2590038320) (.leaf 2534722204)) (.branch 51 (.leaf 2480645031) (.leaf 2427776295)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2376086382) (.leaf 2325546541)) (.branch 55 (.leaf 2276128848) (.leaf 2227806177))) (.branch 58 (.branch 57 (.leaf 2180552168) (.leaf 2134341204)) (.branch 59 (.leaf 2089148380) (.leaf 2044949482))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2001720958) (.branch 62 (.leaf 1959439900) (.leaf 1918084017))) (.branch 65 (.branch 64 (.leaf 1877631620) (.leaf 1838061597)) (.branch 66 (.leaf 1799353397) (.leaf 1761487009)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1724442948) (.leaf 1688202235)) (.branch 70 (.leaf 1652746383) (.leaf 1618057381))) (.branch 73 (.branch 72 (.leaf 1584117679) (.leaf 1550910172)) (.branch 74 (.leaf 1518418191) (.leaf 1486625485))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1455516213) (.branch 77 (.leaf 1425074927) (.leaf 1395286563))) (.branch 80 (.branch 79 (.leaf 1366136431) (.leaf 1337610202)) (.branch 81 (.leaf 1309693899) (.leaf 1282373884)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1255636854) (.leaf 1229469824)) (.branch 85 (.leaf 1203860127) (.leaf 1178795397))) (.branch 88 (.branch 87 (.leaf 1154263566) (.leaf 1130252853)) (.branch 89 (.leaf 1106751758) (.leaf 1083749053)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1061233774) (.branch 92 (.leaf 1039195219) (.leaf 1017622933))) (.branch 95 (.branch 94 (.leaf 996506708) (.leaf 975836574)) (.branch 96 (.leaf 955602792) (.leaf 935795851)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 916406457) (.leaf 897425534)) (.branch 100 (.leaf 878844213) (.leaf 860653827))) (.branch 103 (.branch 102 (.leaf 842845911) (.leaf 825412191)) (.branch 104 (.leaf 808344582) (.leaf 791635183))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 775276273) (.leaf 759260305)) (.branch 108 (.leaf 743579903) (.leaf 728227856))) (.branch 111 (.branch 110 (.leaf 713197116) (.leaf 698480794)) (.branch 112 (.leaf 684072155) (.leaf 669964615)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 656151735) (.leaf 642627221)) (.branch 116 (.leaf 629384920) (.leaf 616418813))) (.branch 119 (.branch 118 (.leaf 603723018) (.leaf 591291780)) (.branch 120 (.leaf 579119472) (.leaf 567200593)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1279).prefactor = (5906892812905819/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1279).cutoff/(generalMeanRows 1279).c)).2 =
    (1136214737449721/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1279).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1279).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1279).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1279

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1279).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1279).criticalRate j.val*(generalMeanRows 1279).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1279).c*(generalMeanRows 1279).criticalPoint j.val)).2-
      (generalMeanRows 1279).J/2-(generalMeanRows 1279).error (generalMeanGrid j.val)+
      (generalMeanRows 1279).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1279).c)).2-
      (generalMeanRows 1279).J/2-(generalMeanRows 1279).error 4 := by
  have he : (generalMeanRows 1279).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1279) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1279)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1279

/-! Kernel-checked entropy margins for general spectral rectangle 1280. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1280
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5000595230) (.branch 2 (.leaf 4848350188) (.leaf 4701479075))) (.branch 5 (.branch 4 (.leaf 4559730689) (.leaf 4422871169)) (.branch 6 (.leaf 4290682284) (.leaf 4162959930)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4039512822) (.leaf 3920161335)) (.branch 10 (.leaf 3804736485) (.leaf 3693079029))) (.branch 13 (.branch 12 (.leaf 3585038660) (.leaf 3480473291)) (.branch 14 (.leaf 3379248420) (.leaf 3281236550))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3186316683) (.branch 17 (.leaf 3094373845) (.leaf 3005298673))) (.branch 20 (.branch 19 (.leaf 2918987030) (.leaf 2835339661)) (.branch 21 (.leaf 2754261874) (.leaf 2675663257)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2599457409) (.leaf 2525561701)) (.branch 25 (.leaf 2453897054) (.leaf 2384387733))) (.branch 28 (.branch 27 (.leaf 2316961157) (.leaf 2251547728)) (.branch 29 (.leaf 2188080665) (.leaf 2126495857)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2066731723) (.branch 32 (.leaf 2008729083) (.leaf 1952431033))) (.branch 35 (.branch 34 (.leaf 1897782838) (.leaf 1844731824)) (.branch 36 (.leaf 1793227280) (.leaf 1743220362)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1694664012) (.leaf 1647512873)) (.branch 40 (.leaf 1601723214) (.leaf 1557252856))) (.branch 43 (.branch 42 (.leaf 1514061106) (.leaf 1472108693)) (.branch 44 (.leaf 1431357704) (.leaf 1391771532))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1353314818) (.branch 47 (.leaf 1315953401) (.leaf 1279654271))) (.branch 50 (.branch 49 (.leaf 1244385519) (.leaf 1210116296)) (.branch 51 (.leaf 1176816774) (.leaf 1144458099)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1113012361) (.leaf 1082452554)) (.branch 55 (.leaf 1052752544) (.leaf 1023887035))) (.branch 58 (.branch 57 (.leaf 995831537) (.leaf 968562340)) (.branch 59 (.leaf 942056482) (.leaf 916291725))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 891246527) (.branch 62 (.leaf 866900018) (.leaf 843231975))) (.branch 65 (.branch 64 (.leaf 820222803) (.leaf 797853509)) (.branch 66 (.leaf 776105684) (.leaf 754961483)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 734403602) (.leaf 714415265)) (.branch 70 (.leaf 694980205) (.leaf 676082642))) (.branch 73 (.branch 72 (.leaf 657707274) (.leaf 639839256)) (.branch 74 (.leaf 622464189) (.leaf 605568101))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 589137437) (.branch 77 (.leaf 573159043) (.leaf 557620155))) (.branch 80 (.branch 79 (.leaf 542508385) (.leaf 527811710)) (.branch 81 (.leaf 513518458) (.leaf 499617303)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 486097247) (.leaf 472947612)) (.branch 85 (.leaf 460158033) (.leaf 447718445))) (.branch 88 (.branch 87 (.leaf 435619076) (.leaf 423850433)) (.branch 89 (.leaf 412403302) (.leaf 401268731)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 390438026) (.branch 92 (.leaf 379902745) (.leaf 369654685))) (.branch 95 (.branch 94 (.leaf 359685879) (.leaf 349988589)) (.branch 96 (.leaf 340555295) (.leaf 331378694)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 322451689) (.leaf 313767385)) (.branch 100 (.leaf 305319083) (.leaf 297100273))) (.branch 103 (.branch 102 (.leaf 289104630) (.leaf 281326007)) (.branch 104 (.leaf 273758431) (.leaf 266396097))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 259233363) (.leaf 252264747)) (.branch 108 (.leaf 245484919) (.leaf 238888700))) (.branch 111 (.branch 110 (.leaf 232471056) (.leaf 226227093)) (.branch 112 (.leaf 220152055) (.leaf 214241318)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 208490387) (.leaf 202894893)) (.branch 116 (.leaf 197450589) (.leaf 192153344))) (.branch 119 (.branch 118 (.leaf 186999145) (.leaf 181984087)) (.branch 120 (.leaf 177104377) (.leaf 172356325)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1280).prefactor = (4927816335077389/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1280).cutoff/(generalMeanRows 1280).c)).2 =
    (1181670175727699/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1280).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1280).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1280).q*(generalMeanRows 1280).cutoff/2-2 = (865/108:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable427.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1280).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1280

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1280).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1280).criticalRate j.val*(generalMeanRows 1280).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1280).c*(generalMeanRows 1280).criticalPoint j.val)).2-
      (generalMeanRows 1280).J/2-(generalMeanRows 1280).error (generalMeanGrid j.val)+
      (generalMeanRows 1280).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1280).c)).2-
      (generalMeanRows 1280).J/2-(generalMeanRows 1280).error 4 := by
  have he : (generalMeanRows 1280).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1280) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1280)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1280

/-! Kernel-checked entropy margins for general spectral rectangle 1281. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1281
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5818191644) (.branch 2 (.leaf 5656851008) (.leaf 5500857687))) (.branch 5 (.branch 4 (.leaf 5349964868) (.leaf 5203943169)) (.branch 6 (.leaf 5062578881) (.leaf 4925672426)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4793037019) (.leaf 4664497485)) (.branch 10 (.leaf 4539889220) (.leaf 4419057269))) (.branch 13 (.branch 12 (.leaf 4301855514) (.leaf 4188145945)) (.branch 14 (.leaf 4077798014) (.leaf 3970688055))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3866698762) (.branch 17 (.leaf 3765718726) (.leaf 3667642005))) (.branch 20 (.branch 19 (.leaf 3572367747) (.leaf 3479799842)) (.branch 21 (.leaf 3389846606) (.leaf 3302420493)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3217437836) (.leaf 3134818603)) (.branch 25 (.leaf 3054486179) (.leaf 2976367163))) (.branch 28 (.branch 27 (.leaf 2900391182) (.leaf 2826490719)) (.branch 29 (.leaf 2754600954) (.leaf 2684659619)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2616606858) (.branch 32 (.leaf 2550385104) (.leaf 2485938961))) (.branch 35 (.branch 34 (.leaf 2423215094) (.leaf 2362162124)) (.branch 36 (.leaf 2302730539) (.leaf 2244872599)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2188542257) (.leaf 2133695075)) (.branch 40 (.leaf 2080288158) (.leaf 2028280080))) (.branch 43 (.branch 42 (.leaf 1977630820) (.leaf 1928301701)) (.branch 44 (.leaf 1880255333) (.leaf 1833455560))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1787867406) (.branch 47 (.leaf 1743457026) (.leaf 1700191664))) (.branch 50 (.branch 49 (.leaf 1658039608) (.leaf 1616970145)) (.branch 51 (.leaf 1576953528) (.leaf 1537960934)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1499964432) (.leaf 1462936948)) (.branch 55 (.leaf 1426852232) (.leaf 1391684832))) (.branch 58 (.branch 57 (.leaf 1357410058) (.leaf 1324003962)) (.branch 59 (.leaf 1291443305) (.leaf 1259705538))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1228768773) (.branch 62 (.leaf 1198611762) (.leaf 1169213875))) (.branch 65 (.branch 64 (.leaf 1140555080) (.leaf 1112615921)) (.branch 66 (.leaf 1085377501) (.leaf 1058821459)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1032929958) (.leaf 1007685664)) (.branch 70 (.leaf 983071733) (.leaf 959071791))) (.branch 73 (.branch 72 (.leaf 935669922) (.leaf 912850653)) (.branch 74 (.leaf 890598941) (.leaf 868900155))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 847740070) (.branch 77 (.leaf 827104850) (.leaf 806981036))) (.branch 80 (.branch 79 (.leaf 787355537) (.leaf 768215618)) (.branch 81 (.leaf 749548887) (.leaf 731343288)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 713587088) (.leaf 696268870)) (.branch 85 (.leaf 679377523) (.leaf 662902231))) (.branch 88 (.branch 87 (.leaf 646832467) (.leaf 631157984)) (.branch 89 (.leaf 615868806) (.leaf 600955220)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 586407770) (.branch 92 (.leaf 572217249) (.leaf 558374690))) (.branch 95 (.branch 94 (.leaf 544871364) (.leaf 531698767)) (.branch 96 (.leaf 518848618) (.leaf 506312853)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 494083616) (.leaf 482153254)) (.branch 100 (.leaf 470514315) (.leaf 459159537))) (.branch 103 (.branch 102 (.leaf 448081847) (.leaf 437274352)) (.branch 104 (.leaf 426730339) (.leaf 416443266))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 406406759) (.leaf 396614606)) (.branch 108 (.leaf 387060755) (.leaf 377739309))) (.branch 111 (.branch 110 (.leaf 368644520) (.leaf 359770786)) (.branch 112 (.leaf 351112649) (.leaf 342664788)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 334422019) (.leaf 326379285)) (.branch 116 (.leaf 318531663) (.leaf 310874348))) (.branch 119 (.branch 118 (.leaf 303402661) (.leaf 296112039)) (.branch 120 (.leaf 288998033) (.leaf 282056308)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1281).prefactor = (5077875146032001/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1281).cutoff/(generalMeanRows 1281).c)).2 =
    (121984274923273/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1281).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1281).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1281).q*(generalMeanRows 1281).cutoff/2-2 = (865/108:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable427.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1281).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1281

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1281).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1281).criticalRate j.val*(generalMeanRows 1281).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1281).c*(generalMeanRows 1281).criticalPoint j.val)).2-
      (generalMeanRows 1281).J/2-(generalMeanRows 1281).error (generalMeanGrid j.val)+
      (generalMeanRows 1281).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1281).c)).2-
      (generalMeanRows 1281).J/2-(generalMeanRows 1281).error 4 := by
  have he : (generalMeanRows 1281).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1281) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1281)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1281

/-! Kernel-checked entropy margins for general spectral rectangle 1282. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1282
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7111174957) (.branch 2 (.leaf 6941055807) (.leaf 6776098468))) (.branch 5 (.branch 4 (.leaf 6616065017) (.leaf 6460735024)) (.branch 6 (.leaf 6309903733) (.leaf 6163380487)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6020987340) (.leaf 5882557854)) (.branch 10 (.leaf 5747936028) (.leaf 5616975364))) (.branch 13 (.branch 12 (.leaf 5489538031) (.leaf 5365494126)) (.branch 14 (.leaf 5244721021) (.leaf 5127102771))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5012529589) (.branch 17 (.leaf 4900897377) (.leaf 4792107294))) (.branch 20 (.branch 19 (.leaf 4686065380) (.leaf 4582682201)) (.branch 21 (.leaf 4481872541) (.leaf 4383555111)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4287652291) (.leaf 4194089891)) (.branch 25 (.leaf 4102796932) (.leaf 4013705451))) (.branch 28 (.branch 27 (.leaf 3926750314) (.leaf 3841869047)) (.branch 29 (.leaf 3759001685) (.leaf 3678090628)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3599080504) (.branch 32 (.leaf 3521918054) (.leaf 3446552011))) (.branch 35 (.branch 34 (.leaf 3372933003) (.leaf 3301013446)) (.branch 36 (.leaf 3230747461) (.leaf 3162090783)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3095000687) (.leaf 3029435908)) (.branch 40 (.leaf 2965356579) (.leaf 2902724157))) (.branch 43 (.branch 42 (.leaf 2841501372) (.leaf 2781652163)) (.branch 44 (.leaf 2723141626) (.leaf 2665935964))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2610002441) (.branch 47 (.leaf 2555309334) (.leaf 2501825895))) (.branch 50 (.branch 49 (.leaf 2449522305) (.leaf 2398369643)) (.branch 51 (.leaf 2348339846) (.leaf 2299405676)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2251540691) (.leaf 2204719210)) (.branch 55 (.leaf 2158916287) (.leaf 2114107684))) (.branch 58 (.branch 57 (.leaf 2070269843) (.leaf 2027379864)) (.branch 59 (.leaf 1985415479) (.leaf 1944355032))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1904177454) (.branch 62 (.leaf 1864862249) (.leaf 1826389466))) (.branch 65 (.branch 64 (.leaf 1788739690) (.leaf 1751894014)) (.branch 66 (.leaf 1715834032) (.leaf 1680541816)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1645999903) (.leaf 1612191281)) (.branch 70 (.leaf 1579099372) (.leaf 1546708022))) (.branch 73 (.branch 72 (.leaf 1515001484) (.leaf 1483964408)) (.branch 74 (.leaf 1453581829) (.leaf 1423839153))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1394722151) (.branch 77 (.leaf 1366216940) (.leaf 1338309982))) (.branch 80 (.branch 79 (.leaf 1310988067) (.leaf 1284238306)) (.branch 81 (.leaf 1258048124) (.leaf 1232405246)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1207297693) (.leaf 1182713773)) (.branch 85 (.leaf 1158642071) (.leaf 1135071442))) (.branch 88 (.branch 87 (.leaf 1111991006) (.leaf 1089390136)) (.branch 89 (.leaf 1067258457) (.leaf 1045585835)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1024362371) (.branch 92 (.leaf 1003578397) (.leaf 983224467))) (.branch 95 (.branch 94 (.leaf 963291354) (.leaf 943770042)) (.branch 96 (.leaf 924651723) (.leaf 905927787)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 887589824) (.leaf 869629612)) (.branch 100 (.leaf 852039115) (.leaf 834810481))) (.branch 103 (.branch 102 (.leaf 817936033) (.leaf 801408266)) (.branch 104 (.leaf 785219844) (.leaf 769363595))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 753832508) (.leaf 738619724)) (.branch 108 (.leaf 723718541) (.leaf 709122404))) (.branch 111 (.branch 110 (.leaf 694824900) (.leaf 680819761)) (.branch 112 (.leaf 667100856) (.leaf 653662188)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 640497892) (.leaf 627602230)) (.branch 116 (.leaf 614969592) (.leaf 602594487))) (.branch 119 (.branch 118 (.leaf 590471546) (.leaf 578595517)) (.branch 120 (.leaf 566961259) (.leaf 555563745)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1282).prefactor = (1308125863739429/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1282).cutoff/(generalMeanRows 1282).c)).2 =
    (1275857390787401/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1282).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1282).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1282).q*(generalMeanRows 1282).c/2-2 = (1589/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable251.value]
    have hcontinuation : (generalMeanRows 1282).q*(generalMeanRows 1282).cutoff/2-2 = (865/108:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable427.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1282).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1282

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1282).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1282).criticalRate j.val*(generalMeanRows 1282).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1282).c*(generalMeanRows 1282).criticalPoint j.val)).2-
      (generalMeanRows 1282).J/2-(generalMeanRows 1282).error (generalMeanGrid j.val)+
      (generalMeanRows 1282).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1282).c)).2-
      (generalMeanRows 1282).J/2-(generalMeanRows 1282).error 4 := by
  have he : (generalMeanRows 1282).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1282) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1282)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1282

/-! Kernel-checked entropy margins for general spectral rectangle 1283. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1283
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5159075539) (.branch 2 (.leaf 5019881754) (.leaf 4885199022))) (.branch 5 (.branch 4 (.leaf 4754823479) (.leaf 4628565220)) (.branch 6 (.leaf 4506246941) (.leaf 4387702754)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4272777142) (.leaf 4161324035)) (.branch 10 (.leaf 4053205998) (.leaf 3948293500))) (.branch 13 (.branch 12 (.leaf 3846464274) (.leaf 3747602732)) (.branch 14 (.leaf 3651599451) (.leaf 3558350705))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3467758045) (.branch 17 (.leaf 3379727919) (.leaf 3294171331))) (.branch 20 (.branch 19 (.leaf 3211003523) (.leaf 3130143695)) (.branch 21 (.leaf 3051514743) (.leaf 2975043024)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2900658138) (.leaf 2828292730)) (.branch 25 (.leaf 2757882304) (.leaf 2689365060))) (.branch 28 (.branch 27 (.leaf 2622681731) (.leaf 2557775449)) (.branch 29 (.leaf 2494591604) (.leaf 2433077725)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2373183366) (.branch 32 (.leaf 2314859998) (.leaf 2258060914))) (.branch 35 (.branch 34 (.leaf 2202741132) (.leaf 2148857315)) (.branch 36 (.leaf 2096367685) (.leaf 2045231952)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1995411246) (.leaf 1946868044)) (.branch 40 (.leaf 1899566116) (.leaf 1853470461))) (.branch 43 (.branch 42 (.leaf 1808547257) (.leaf 1764763808)) (.branch 44 (.leaf 1722088495) (.leaf 1680490730))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1639940918) (.branch 47 (.leaf 1600410407) (.leaf 1561871458))) (.branch 50 (.branch 49 (.leaf 1524297206) (.leaf 1487661622)) (.branch 51 (.leaf 1451939487) (.leaf 1417106353)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1383138522) (.leaf 1350013010)) (.branch 55 (.leaf 1317707525) (.leaf 1286200441))) (.branch 58 (.branch 57 (.leaf 1255470774) (.leaf 1225498158)) (.branch 59 (.leaf 1196262821) (.leaf 1167745569))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1139927763) (.branch 62 (.leaf 1112791299) (.leaf 1086318591))) (.branch 65 (.branch 64 (.leaf 1060492555) (.leaf 1035296588)) (.branch 66 (.leaf 1010714556) (.leaf 986730777)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 963330005) (.leaf 940497418)) (.branch 70 (.leaf 918218604) (.leaf 896479547))) (.branch 73 (.branch 72 (.leaf 875266615) (.leaf 854566547)) (.branch 74 (.leaf 834366443) (.leaf 814653752))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 795416261) (.branch 77 (.leaf 776642086) (.leaf 758319659))) (.branch 80 (.branch 79 (.leaf 740437724) (.leaf 722985321)) (.branch 81 (.leaf 705951781) (.leaf 689326718)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 673100018) (.leaf 657261834)) (.branch 85 (.leaf 641802575) (.leaf 626712901))) (.branch 88 (.branch 87 (.leaf 611983715) (.leaf 597606157)) (.branch 89 (.leaf 583571596) (.leaf 569871621)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 556498043) (.branch 92 (.leaf 543442878) (.leaf 530698351))) (.branch 95 (.branch 94 (.leaf 518256882) (.leaf 506111088)) (.branch 96 (.leaf 494253772) (.leaf 482677919)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 471376694) (.leaf 460343433)) (.branch 100 (.leaf 449571643) (.leaf 439054991))) (.branch 103 (.branch 102 (.leaf 428787306) (.leaf 418762571)) (.branch 104 (.leaf 408974920) (.leaf 399418634))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 390088137) (.leaf 380977991)) (.branch 108 (.leaf 372082894) (.leaf 363397677))) (.branch 111 (.branch 110 (.leaf 354917298) (.leaf 346636840)) (.branch 112 (.leaf 338551508) (.leaf 330656626)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 322947633) (.leaf 315420079)) (.branch 116 (.leaf 308069627) (.leaf 300892043))) (.branch 119 (.branch 118 (.leaf 293883200) (.leaf 287039069)) (.branch 120 (.leaf 280355722) (.leaf 273829328)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1283).prefactor = (4265702382831907/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1283).cutoff/(generalMeanRows 1283).c)).2 =
    (1376765437774039/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1283).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1283).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1283).q*(generalMeanRows 1283).cutoff/2-2 = (700/73:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable429.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1283).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1283

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1283).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1283).criticalRate j.val*(generalMeanRows 1283).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1283).c*(generalMeanRows 1283).criticalPoint j.val)).2-
      (generalMeanRows 1283).J/2-(generalMeanRows 1283).error (generalMeanGrid j.val)+
      (generalMeanRows 1283).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1283).c)).2-
      (generalMeanRows 1283).J/2-(generalMeanRows 1283).error 4 := by
  have he : (generalMeanRows 1283).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1283) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1283)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1283

/-! Kernel-checked entropy margins for general spectral rectangle 1284. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1284
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5283936869) (.branch 2 (.leaf 5142778042) (.leaf 5006165486))) (.branch 5 (.branch 4 (.leaf 4873893877) (.leaf 4745771986)) (.branch 6 (.leaf 4621621306) (.leaf 4501274854)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4384576108) (.leaf 4271378081)) (.branch 10 (.leaf 4161542493) (.leaf 4054939038))) (.branch 13 (.branch 12 (.leaf 3951444727) (.leaf 3850943309)) (.branch 14 (.leaf 3753324743) (.leaf 3658484729))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3566324282) (.branch 17 (.leaf 3476749350) (.leaf 3389670465))) (.branch 20 (.branch 19 (.leaf 3305002428) (.leaf 3222664021)) (.branch 21 (.leaf 3142577748) (.leaf 3064669592)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2988868799) (.leaf 2915107677)) (.branch 25 (.leaf 2843321409) (.leaf 2773447885))) (.branch 28 (.branch 27 (.leaf 2705427546) (.leaf 2639203238)) (.branch 29 (.leaf 2574720079) (.leaf 2511925335)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2450768305) (.branch 32 (.leaf 2391200214) (.leaf 2333174115))) (.branch 35 (.branch 34 (.leaf 2276644794) (.leaf 2221568686)) (.branch 36 (.leaf 2167903793) (.leaf 2115609611)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2064647056) (.leaf 2014978400)) (.branch 40 (.leaf 1966567209) (.leaf 1919378284))) (.branch 43 (.branch 42 (.leaf 1873377607) (.leaf 1828532291)) (.branch 44 (.leaf 1784810525) (.leaf 1742181538))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1700615546) (.branch 47 (.leaf 1660083721) (.leaf 1620558141))) (.branch 50 (.branch 49 (.leaf 1582011765) (.leaf 1544418389)) (.branch 51 (.leaf 1507752620) (.leaf 1471989841)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1437106181) (.leaf 1403078490)) (.branch 55 (.leaf 1369884311) (.leaf 1337501852))) (.branch 58 (.branch 57 (.leaf 1305909966) (.leaf 1275088124)) (.branch 59 (.leaf 1245016396) (.leaf 1215675429))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1187046424) (.branch 62 (.leaf 1159111124) (.leaf 1131851786))) (.branch 65 (.branch 64 (.leaf 1105251173) (.leaf 1079292530)) (.branch 66 (.leaf 1053959571) (.leaf 1029236465)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1005107818) (.leaf 981558661)) (.branch 70 (.leaf 958574435) (.leaf 936140979))) (.branch 73 (.branch 72 (.leaf 914244517) (.leaf 892871647)) (.branch 74 (.leaf 872009327) (.leaf 851644866))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 831765913) (.branch 77 (.leaf 812360446) (.leaf 793416761))) (.branch 80 (.branch 79 (.leaf 774923465) (.leaf 756869465)) (.branch 81 (.leaf 739243961) (.leaf 722036434)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 705236640) (.leaf 688834602)) (.branch 85 (.leaf 672820603) (.leaf 657185175))) (.branch 88 (.branch 87 (.leaf 641919097) (.leaf 627013383)) (.branch 89 (.leaf 612459279) (.leaf 598248255)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 584371999) (.branch 92 (.leaf 570822409) (.leaf 557591590))) (.branch 95 (.branch 94 (.leaf 544671848) (.leaf 532055683)) (.branch 96 (.leaf 519735782) (.leaf 507705019)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 495956447) (.leaf 484483291)) (.branch 100 (.leaf 473278947) (.leaf 462336975))) (.branch 103 (.branch 102 (.leaf 451651097) (.leaf 441215191)) (.branch 104 (.leaf 431023284) (.leaf 421069555))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 411348325) (.leaf 401854056)) (.branch 108 (.leaf 392581346) (.leaf 383524926))) (.branch 111 (.branch 110 (.leaf 374679658) (.leaf 366040527)) (.branch 112 (.leaf 357602644) (.leaf 349361238)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 341311656) (.leaf 333449357)) (.branch 116 (.leaf 325769911) (.leaf 318268997))) (.branch 119 (.branch 118 (.leaf 310942398) (.leaf 303785999)) (.branch 120 (.leaf 296795785) (.leaf 289967840)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1284).prefactor = (2158602704030613/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1284).cutoff/(generalMeanRows 1284).c)).2 =
    (345154751772507/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1284).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1284).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1284).q*(generalMeanRows 1284).c/2-2 = (731/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable371.value]
    have hcontinuation : (generalMeanRows 1284).q*(generalMeanRows 1284).cutoff/2-2 = (700/73:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable429.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1284).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1284

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1284).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1284).criticalRate j.val*(generalMeanRows 1284).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1284).c*(generalMeanRows 1284).criticalPoint j.val)).2-
      (generalMeanRows 1284).J/2-(generalMeanRows 1284).error (generalMeanGrid j.val)+
      (generalMeanRows 1284).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1284).c)).2-
      (generalMeanRows 1284).J/2-(generalMeanRows 1284).error 4 := by
  have he : (generalMeanRows 1284).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1284) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1284)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1284

/-! Kernel-checked entropy margins for general spectral rectangle 1285. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1285
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5444876359) (.branch 2 (.leaf 5299418081) (.leaf 5158644545))) (.branch 5 (.branch 4 (.leaf 5022344174) (.leaf 4890319913)) (.branch 6 (.leaf 4762387821) (.leaf 4638375826)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4518122640) (.leaf 4401476799)) (.branch 10 (.leaf 4288295811) (.leaf 4178445400))) (.branch 13 (.branch 12 (.leaf 4071798833) (.leaf 3968236317)) (.branch 14 (.leaf 3867644460) (.leaf 3769915785))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3674948292) (.branch 17 (.leaf 3582645064) (.leaf 3492913908))) (.branch 20 (.branch 19 (.leaf 3405667030) (.leaf 3320820739)) (.branch 21 (.leaf 3238295178) (.leaf 3158014076)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3079904524) (.leaf 3003896766)) (.branch 25 (.leaf 2929924014) (.leaf 2857922264))) (.branch 28 (.branch 27 (.leaf 2787830144) (.leaf 2719588760)) (.branch 29 (.leaf 2653141556) (.leaf 2588434194)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2525414428) (.branch 32 (.leaf 2464031997) (.leaf 2404238524))) (.branch 35 (.branch 34 (.leaf 2345987419) (.leaf 2289233789)) (.branch 36 (.leaf 2233934357) (.leaf 2180047386)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2127532600) (.leaf 2076351123)) (.branch 40 (.leaf 2026465412) (.leaf 1977839195))) (.branch 43 (.branch 42 (.leaf 1930437418) (.leaf 1884226191)) (.branch 44 (.leaf 1839172737) (.leaf 1795245345))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1752413326) (.branch 47 (.leaf 1710646972) (.leaf 1669917512))) (.branch 50 (.branch 49 (.leaf 1630197080) (.leaf 1591458676)) (.branch 51 (.leaf 1553676132) (.leaf 1516824081)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1480877926) (.leaf 1445813811)) (.branch 55 (.leaf 1411608595) (.leaf 1378239823))) (.branch 58 (.branch 57 (.leaf 1345685703) (.leaf 1313925082)) (.branch 59 (.leaf 1282937422) (.leaf 1252702780))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1223201786) (.branch 62 (.leaf 1194415624) (.leaf 1166326015))) (.branch 65 (.branch 64 (.leaf 1138915193) (.leaf 1112165895)) (.branch 66 (.leaf 1086061339) (.leaf 1060585211)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1035721647) (.leaf 1011455224)) (.branch 70 (.leaf 987770938) (.leaf 964654199))) (.branch 73 (.branch 72 (.leaf 942090809) (.leaf 920066958)) (.branch 74 (.leaf 898569209) (.leaf 877584482))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 857100051) (.branch 77 (.leaf 837103526) (.leaf 817582850))) (.branch 80 (.branch 79 (.leaf 798526280) (.leaf 779922388)) (.branch 81 (.leaf 761760041) (.leaf 744028403)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 726716916) (.leaf 709815301)) (.branch 85 (.leaf 693313543) (.leaf 677201888))) (.branch 88 (.branch 87 (.leaf 661470831) (.leaf 646111116)) (.branch 89 (.leaf 631113719) (.leaf 616469853)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 602170950) (.branch 92 (.leaf 588208663) (.leaf 574574856))) (.branch 95 (.branch 94 (.leaf 561261602) (.leaf 548261170)) (.branch 96 (.leaf 535566026) (.leaf 523168828)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 511062414) (.leaf 499239806)) (.branch 100 (.leaf 487694197) (.leaf 476418952))) (.branch 103 (.branch 102 (.leaf 465407601) (.leaf 454653835)) (.branch 104 (.leaf 444151501) (.leaf 433894599))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 423877277) (.leaf 414093829)) (.branch 108 (.leaf 404538688) (.leaf 395206426))) (.branch 111 (.branch 110 (.leaf 386091746) (.leaf 377189482)) (.branch 112 (.leaf 368494596) (.leaf 360002172)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 351707413) (.leaf 343605642)) (.branch 116 (.leaf 335692294) (.leaf 327962915))) (.branch 119 (.branch 118 (.leaf 320413160) (.leaf 313038790)) (.branch 120 (.leaf 305835667) (.leaf 298799754)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1285).prefactor = (2224349973012909/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1285).cutoff/(generalMeanRows 1285).c)).2 =
    (345154751772507/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1285).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1285).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1285).q*(generalMeanRows 1285).c/2-2 = (731/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable371.value]
    have hcontinuation : (generalMeanRows 1285).q*(generalMeanRows 1285).cutoff/2-2 = (700/73:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable429.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1285).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1285

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1285).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1285).criticalRate j.val*(generalMeanRows 1285).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1285).c*(generalMeanRows 1285).criticalPoint j.val)).2-
      (generalMeanRows 1285).J/2-(generalMeanRows 1285).error (generalMeanGrid j.val)+
      (generalMeanRows 1285).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1285).c)).2-
      (generalMeanRows 1285).J/2-(generalMeanRows 1285).error 4 := by
  have he : (generalMeanRows 1285).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1285) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1285)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1285

/-! Kernel-checked entropy margins for general spectral rectangle 1286. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1286
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5814994509) (.branch 2 (.leaf 5664284533) (.leaf 5518338450))) (.branch 5 (.branch 4 (.leaf 5376941393) (.leaf 5239893366)) (.branch 6 (.leaf 5107007783) (.leaf 4978110198)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4853037181) (.leaf 4731635332)) (.branch 10 (.leaf 4613760407) (.leaf 4499276539))) (.branch 13 (.branch 12 (.leaf 4388055546) (.leaf 4279976315)) (.branch 14 (.leaf 4174924246) (.leaf 4072790753))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3973472818) (.branch 17 (.leaf 3876872584) (.leaf 3782896989))) (.branch 20 (.branch 19 (.leaf 3691457431) (.leaf 3602469468)) (.branch 21 (.leaf 3515852541) (.leaf 3431529722)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3349427482) (.leaf 3269475483)) (.branch 25 (.leaf 3191606380) (.leaf 3115755646))) (.branch 28 (.branch 27 (.leaf 3041861406) (.leaf 2969864284)) (.branch 29 (.leaf 2899707265) (.leaf 2831335563)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2764696503) (.branch 32 (.leaf 2699739406) (.leaf 2636415488))) (.branch 35 (.branch 34 (.leaf 2574677762) (.leaf 2514480948)) (.branch 36 (.leaf 2455781387) (.leaf 2398536968)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2342707046) (.leaf 2288252382)) (.branch 40 (.leaf 2235135070) (.leaf 2183318485))) (.branch 43 (.branch 42 (.leaf 2132767217) (.leaf 2083447025)) (.branch 44 (.leaf 2035324783) (.leaf 1988368432))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1942546936) (.branch 47 (.leaf 1897830242) (.leaf 1854189236))) (.branch 50 (.branch 49 (.leaf 1811595706) (.leaf 1770022309)) (.branch 51 (.leaf 1729442534) (.leaf 1689830671)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1651161782) (.leaf 1613411667)) (.branch 55 (.leaf 1576556842) (.leaf 1540574510))) (.branch 58 (.branch 57 (.leaf 1505442537) (.leaf 1471139427)) (.branch 59 (.leaf 1437644299) (.leaf 1404936869))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1372997423) (.branch 62 (.leaf 1341806806) (.leaf 1311346393))) (.branch 65 (.branch 64 (.leaf 1281598079) (.leaf 1252544257)) (.branch 66 (.leaf 1224167806) (.leaf 1196452070)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1169380846) (.leaf 1142938369)) (.branch 70 (.leaf 1117109298) (.leaf 1091878702))) (.branch 73 (.branch 72 (.leaf 1067232048) (.leaf 1043155187)) (.branch 74 (.leaf 1019634346) (.leaf 996656111))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 974207420) (.branch 77 (.leaf 952275552) (.leaf 930848117))) (.branch 80 (.branch 79 (.leaf 909913042) (.leaf 889458567)) (.branch 81 (.leaf 869473236) (.leaf 849945882)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 830865625) (.leaf 812221861)) (.branch 85 (.leaf 794004253) (.leaf 776202728))) (.branch 88 (.branch 87 (.leaf 758807462) (.leaf 741808882)) (.branch 89 (.leaf 725197651) (.leaf 708964667)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 693101053) (.branch 92 (.leaf 677598152) (.leaf 662447523))) (.branch 95 (.branch 94 (.leaf 647640931) (.leaf 633170344)) (.branch 96 (.leaf 619027930) (.leaf 605206045)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 591697235) (.leaf 578494224)) (.branch 100 (.leaf 565589917) (.leaf 552977389))) (.branch 103 (.branch 102 (.leaf 540649884) (.leaf 528600806)) (.branch 104 (.leaf 516823724) (.leaf 505312356))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 494060575) (.leaf 483062399)) (.branch 108 (.leaf 472311990) (.leaf 461803649))) (.branch 111 (.branch 110 (.leaf 451531814) (.leaf 441491055)) (.branch 112 (.leaf 431676071) (.leaf 422081686)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 412702849) (.leaf 403534627)) (.branch 116 (.leaf 394572204) (.leaf 385810877))) (.branch 119 (.branch 118 (.leaf 377246055) (.leaf 368873255)) (.branch 120 (.leaf 360688099) (.leaf 352686311)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1286).prefactor = (4584199577999189/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1286).cutoff/(generalMeanRows 1286).c)).2 =
    (1392269624310021/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1286).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1286).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1286).q*(generalMeanRows 1286).c/2-2 = (22/25:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable099.value]
    have hcontinuation : (generalMeanRows 1286).q*(generalMeanRows 1286).cutoff/2-2 = (700/73:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable429.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1286).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1286

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1286).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1286).criticalRate j.val*(generalMeanRows 1286).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1286).c*(generalMeanRows 1286).criticalPoint j.val)).2-
      (generalMeanRows 1286).J/2-(generalMeanRows 1286).error (generalMeanGrid j.val)+
      (generalMeanRows 1286).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1286).c)).2-
      (generalMeanRows 1286).J/2-(generalMeanRows 1286).error 4 := by
  have he : (generalMeanRows 1286).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1286) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1286)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1286

/-! Kernel-checked entropy margins for general spectral rectangle 1287. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1287
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6360618579) (.branch 2 (.leaf 6204223751) (.leaf 6052621400))) (.branch 5 (.branch 4 (.leaf 5905595390) (.leaf 5762944754)) (.branch 6 (.leaf 5624482197) (.leaf 5490032782)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5359432777) (.leaf 5232528642)) (.branch 10 (.leaf 5109176128) (.leaf 4989239477))) (.branch 13 (.branch 12 (.leaf 4872590717) (.leaf 4759109024)) (.branch 14 (.leaf 4648680154) (.leaf 4541195935))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4436553805) (.branch 17 (.leaf 4334656403) (.leaf 4235411187))) (.branch 20 (.branch 19 (.leaf 4138730098) (.leaf 4044529251)) (.branch 21 (.leaf 3952728656) (.leaf 3863251953)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3776026190) (.leaf 3690981595)) (.branch 25 (.leaf 3608051389) (.leaf 3527171600))) (.branch 28 (.branch 27 (.leaf 3448280897) (.leaf 3371320437)) (.branch 29 (.leaf 3296233722) (.leaf 3222966468)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3151466485) (.branch 32 (.leaf 3081683561) (.leaf 3013569360))) (.branch 35 (.branch 34 (.leaf 2947077323) (.leaf 2882162580)) (.branch 36 (.leaf 2818781862) (.leaf 2756893422)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2696456966) (.leaf 2637433579)) (.branch 40 (.leaf 2579785663) (.leaf 2523476875))) (.branch 43 (.branch 42 (.leaf 2468472071) (.leaf 2414737254)) (.branch 44 (.leaf 2362239521) (.leaf 2310947016))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2260828888) (.branch 47 (.leaf 2211855248) (.leaf 2163997126))) (.branch 50 (.branch 49 (.leaf 2117226440) (.leaf 2071515952)) (.branch 51 (.leaf 2026839245) (.leaf 1983170680)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1940485375) (.leaf 1898759172)) (.branch 55 (.leaf 1857968608) (.leaf 1818090897))) (.branch 58 (.branch 57 (.leaf 1779103895) (.leaf 1740986084)) (.branch 59 (.leaf 1703716549) (.leaf 1667274954))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1631641523) (.branch 62 (.leaf 1596797022) (.leaf 1562722738))) (.branch 65 (.branch 64 (.leaf 1529400466) (.leaf 1496812486)) (.branch 66 (.leaf 1464941552) (.leaf 1433770874)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1403284104) (.leaf 1373465322)) (.branch 70 (.leaf 1344299021) (.leaf 1315770098))) (.branch 73 (.branch 72 (.leaf 1287863836) (.leaf 1260565896)) (.branch 74 (.leaf 1233862306) (.leaf 1207739445))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1182184037) (.branch 77 (.leaf 1157183141) (.leaf 1132724138))) (.branch 80 (.branch 79 (.leaf 1108794722) (.leaf 1085382894)) (.branch 81 (.leaf 1062476950) (.leaf 1040065475)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1018137332) (.leaf 996681655)) (.branch 85 (.leaf 975687845) (.leaf 955145556))) (.branch 88 (.branch 87 (.leaf 935044694) (.leaf 915375407)) (.branch 89 (.leaf 896128078) (.leaf 877293322)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 858861974) (.branch 92 (.leaf 840825090) (.leaf 823173936))) (.branch 95 (.branch 94 (.leaf 805899982) (.leaf 788994903)) (.branch 96 (.leaf 772450565) (.leaf 756259026)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 740412531) (.leaf 724903502)) (.branch 100 (.leaf 709724538) (.leaf 694868412))) (.branch 103 (.branch 102 (.leaf 680328060) (.leaf 666096582)) (.branch 104 (.leaf 652167239) (.leaf 638533443))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 625188759) (.leaf 612126898)) (.branch 108 (.leaf 599341714) (.leaf 586827202))) (.branch 111 (.branch 110 (.leaf 574577492) (.leaf 562586849)) (.branch 112 (.leaf 550849664) (.leaf 539360459)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 528113876) (.leaf 517104678)) (.branch 116 (.leaf 506327747) (.leaf 495778079))) (.branch 119 (.branch 118 (.leaf 485450782) (.leaf 475341072)) (.branch 120 (.leaf 465444275) (.leaf 455755816)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1287).prefactor = (73809785814861/15625000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1287).cutoff/(generalMeanRows 1287).c)).2 =
    (1411994129657799/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1287).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1287).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1287).q*(generalMeanRows 1287).c/2-2 = (659/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable430.value]
    have hcontinuation : (generalMeanRows 1287).q*(generalMeanRows 1287).cutoff/2-2 = (700/73:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable429.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1287).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1287

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1287).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1287).criticalRate j.val*(generalMeanRows 1287).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1287).c*(generalMeanRows 1287).criticalPoint j.val)).2-
      (generalMeanRows 1287).J/2-(generalMeanRows 1287).error (generalMeanGrid j.val)+
      (generalMeanRows 1287).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1287).c)).2-
      (generalMeanRows 1287).J/2-(generalMeanRows 1287).error 4 := by
  have he : (generalMeanRows 1287).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1287) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1287)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1287

/-! Kernel-checked entropy margins for general spectral rectangle 1288. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1288
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6902499973) (.branch 2 (.leaf 6743801958) (.leaf 6589791854))) (.branch 5 (.branch 4 (.leaf 6440257438) (.leaf 6295001654)) (.branch 6 (.leaf 6153841100) (.leaf 6016604705)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5883132562) (.leaf 5753274907)) (.branch 10 (.leaf 5626891208) (.leaf 5503849366))) (.branch 13 (.branch 12 (.leaf 5384024998) (.leaf 5267300797)) (.branch 14 (.leaf 5153565965) (.leaf 5042715696))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4934650722) (.branch 17 (.leaf 4829276889) (.leaf 4726504789))) (.branch 20 (.branch 19 (.leaf 4626249412) (.leaf 4528429846)) (.branch 21 (.leaf 4432968989) (.leaf 4339793293)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4248832534) (.leaf 4160019596)) (.branch 25 (.leaf 4073290274) (.leaf 3988583093))) (.branch 28 (.branch 27 (.leaf 3905839145) (.leaf 3825001935)) (.branch 29 (.leaf 3746017239) (.leaf 3668832976)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3593399087) (.branch 32 (.leaf 3519667424) (.leaf 3447591644))) (.branch 35 (.branch 34 (.leaf 3377127118) (.leaf 3308230837)) (.branch 36 (.leaf 3240861330) (.leaf 3174978589)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3110543994) (.leaf 3047520247)) (.branch 40 (.leaf 2985871308) (.leaf 2925562336))) (.branch 43 (.branch 42 (.leaf 2866559632) (.leaf 2808830592)) (.branch 44 (.leaf 2752343651) (.leaf 2697068243))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2642974755) (.branch 47 (.leaf 2590034487) (.leaf 2538219613))) (.branch 50 (.branch 49 (.leaf 2487503144) (.leaf 2437858898)) (.branch 51 (.leaf 2389261462) (.leaf 2341686165)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2295109048) (.leaf 2249506836)) (.branch 55 (.leaf 2204856915) (.leaf 2161137302))) (.branch 58 (.branch 57 (.leaf 2118326625) (.leaf 2076404102)) (.branch 59 (.leaf 2035349517) (.leaf 1995143200))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1955766009) (.branch 62 (.leaf 1917199313) (.leaf 1879424970))) (.branch 65 (.branch 64 (.leaf 1842425315) (.leaf 1806183143)) (.branch 66 (.leaf 1770681691) (.leaf 1735904626)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1701836031) (.leaf 1668460393)) (.branch 70 (.leaf 1635762586) (.leaf 1603727861))) (.branch 73 (.branch 72 (.leaf 1572341838) (.leaf 1541590488)) (.branch 74 (.leaf 1511460128) (.leaf 1481937406))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1453009295) (.branch 77 (.leaf 1424663081) (.leaf 1396886356))) (.branch 80 (.branch 79 (.leaf 1369667006) (.leaf 1342993205)) (.branch 81 (.leaf 1316853406) (.leaf 1291236333)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1266130973) (.leaf 1241526570)) (.branch 85 (.leaf 1217412618) (.leaf 1193778851))) (.branch 88 (.branch 87 (.leaf 1170615240) (.leaf 1147911986)) (.branch 89 (.leaf 1125659511) (.leaf 1103848458)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1082469677) (.branch 92 (.leaf 1061514228) (.leaf 1040973369))) (.branch 95 (.branch 94 (.leaf 1020838553) (.leaf 1001101427)) (.branch 96 (.leaf 981753819) (.leaf 962787741)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 944195380) (.leaf 925969094)) (.branch 100 (.leaf 908101411) (.leaf 890585019))) (.branch 103 (.branch 102 (.leaf 873412769) (.leaf 856577663)) (.branch 104 (.leaf 840072859) (.leaf 823891661))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 808027515) (.leaf 792474013)) (.branch 108 (.leaf 777224880) (.leaf 762273977))) (.branch 111 (.branch 110 (.leaf 747615296) (.leaf 733242957)) (.branch 112 (.leaf 719151204) (.leaf 705334405)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 691787044) (.leaf 678503724)) (.branch 116 (.leaf 665479160) (.leaf 652708181))) (.branch 119 (.branch 118 (.leaf 640185720) (.leaf 627906820)) (.branch 120 (.leaf 615866625) (.leaf 604060382)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1288).prefactor = (1192826819238911/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1288).cutoff/(generalMeanRows 1288).c)).2 =
    (287237771648971/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1288).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1288).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1288).q*(generalMeanRows 1288).c/2-2 = (121/160:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable416.value]
    have hcontinuation : (generalMeanRows 1288).q*(generalMeanRows 1288).cutoff/2-2 = (700/73:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable429.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1288).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1288

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1288).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1288).criticalRate j.val*(generalMeanRows 1288).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1288).c*(generalMeanRows 1288).criticalPoint j.val)).2-
      (generalMeanRows 1288).J/2-(generalMeanRows 1288).error (generalMeanGrid j.val)+
      (generalMeanRows 1288).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1288).c)).2-
      (generalMeanRows 1288).J/2-(generalMeanRows 1288).error 4 := by
  have he : (generalMeanRows 1288).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1288) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1288)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1288

/-! Kernel-checked entropy margins for general spectral rectangle 1289. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1289
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4724387371) (.branch 2 (.leaf 4588262060) (.leaf 4456735459))) (.branch 5 (.branch 4 (.leaf 4329599780) (.leaf 4206660961)) (.branch 6 (.leaf 4087737397) (.leaf 3972658820)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3861265307) (.leaf 3753406398)) (.branch 10 (.leaf 3648940311) (.leaf 3547733243))) (.branch 13 (.branch 12 (.leaf 3449658736) (.leaf 3354597120)) (.branch 14 (.leaf 3262434997) (.leaf 3173064788))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3086384310) (.branch 17 (.leaf 3002296408) (.leaf 2920708604))) (.branch 20 (.branch 19 (.leaf 2841532791) (.leaf 2764684942)) (.branch 21 (.leaf 2690084856) (.leaf 2617655913)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2547324860) (.leaf 2479021604)) (.branch 25 (.leaf 2412679031) (.leaf 2348232833))) (.branch 28 (.branch 27 (.leaf 2285621348) (.leaf 2224785417)) (.branch 29 (.leaf 2165668245) (.leaf 2108215276)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2052374077) (.branch 32 (.leaf 1998094227) (.leaf 1945327217))) (.branch 35 (.branch 34 (.leaf 1894026354) (.leaf 1844146672)) (.branch 36 (.leaf 1795644850) (.leaf 1748479136)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1702609269) (.leaf 1657996417)) (.branch 40 (.leaf 1614603107) (.leaf 1572393168))) (.branch 43 (.branch 42 (.leaf 1531331674) (.leaf 1491384888)) (.branch 44 (.leaf 1452520213) (.leaf 1414706144))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1377912222) (.branch 47 (.leaf 1342108993) (.leaf 1307267965))) (.branch 50 (.branch 49 (.leaf 1273361570) (.leaf 1240363132)) (.branch 51 (.leaf 1208246823) (.leaf 1176987640)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1146561369) (.leaf 1116944552)) (.branch 55 (.leaf 1088114468) (.leaf 1060049095))) (.branch 58 (.branch 57 (.leaf 1032727093) (.leaf 1006127774)) (.branch 59 (.leaf 980231082) (.leaf 955017568))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 930468370) (.branch 62 (.leaf 906565192) (.leaf 883290286))) (.branch 65 (.branch 64 (.leaf 860626429) (.leaf 838556909)) (.branch 66 (.leaf 817065509) (.leaf 796136485)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 775754555) (.leaf 755904880)) (.branch 70 (.leaf 736573053) (.leaf 717745084))) (.branch 73 (.branch 72 (.leaf 699407383) (.leaf 681546754)) (.branch 74 (.leaf 664150375) (.leaf 647205791))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 630700900) (.branch 77 (.leaf 614623944) (.leaf 598963496))) (.branch 80 (.branch 79 (.leaf 583708452) (.leaf 568848017)) (.branch 81 (.leaf 554371702) (.leaf 540269308)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 526530922) (.leaf 513146905)) (.branch 85 (.leaf 500107885) (.leaf 487404751))) (.branch 88 (.branch 87 (.leaf 475028641) (.leaf 462970939)) (.branch 89 (.leaf 451223265) (.leaf 439777466)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 428625617) (.branch 92 (.leaf 417760004) (.leaf 407173128))) (.branch 95 (.branch 94 (.leaf 396857689) (.leaf 386806589)) (.branch 96 (.leaf 377012921) (.leaf 367469963)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 358171178) (.leaf 349110202)) (.branch 100 (.leaf 340280843) (.leaf 331677076))) (.branch 103 (.branch 102 (.leaf 323293038) (.leaf 315123021)) (.branch 104 (.leaf 307161472) (.leaf 299402984))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 291842296) (.leaf 284474287)) (.branch 108 (.leaf 277293969) (.leaf 270296492))) (.branch 111 (.branch 110 (.leaf 263477130) (.leaf 256831285)) (.branch 112 (.leaf 250354478) (.leaf 244042350)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 237890659) (.leaf 231895270)) (.branch 116 (.leaf 226052162) (.leaf 220357416))) (.branch 119 (.branch 118 (.leaf 214807219) (.leaf 209397855)) (.branch 120 (.leaf 204125708) (.leaf 198987256)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1289).prefactor = (1037022564754973/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1289).cutoff/(generalMeanRows 1289).c)).2 =
    (1551118824918831/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1289).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1289).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1289).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1289

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1289).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1289).criticalRate j.val*(generalMeanRows 1289).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1289).c*(generalMeanRows 1289).criticalPoint j.val)).2-
      (generalMeanRows 1289).J/2-(generalMeanRows 1289).error (generalMeanGrid j.val)+
      (generalMeanRows 1289).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1289).c)).2-
      (generalMeanRows 1289).J/2-(generalMeanRows 1289).error 4 := by
  have he : (generalMeanRows 1289).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1289) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1289)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1289

/-! Kernel-checked entropy margins for general spectral rectangle 1290. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1290
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5648448298) (.branch 2 (.leaf 5487052134) (.leaf 5331085880))) (.branch 5 (.branch 4 (.leaf 5180302721) (.leaf 5034472499)) (.branch 6 (.leaf 4893380119) (.leaf 4756824143)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4624615562) (.leaf 4496576701)) (.branch 10 (.leaf 4372540258) (.leaf 4252348442))) (.branch 13 (.branch 12 (.leaf 4135852209) (.leaf 4022910575)) (.branch 14 (.leaf 3913389999) (.leaf 3807163834))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3704111819) (.branch 17 (.leaf 3604119635) (.leaf 3507078490))) (.branch 20 (.branch 19 (.leaf 3412884745) (.leaf 3321439581)) (.branch 21 (.leaf 3232648679) (.leaf 3146421945)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3062673244) (.leaf 2981320163)) (.branch 25 (.leaf 2902283794) (.leaf 2825488524))) (.branch 28 (.branch 27 (.leaf 2750861857) (.leaf 2678334234)) (.branch 29 (.leaf 2607838875) (.leaf 2539311630)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2472690844) (.branch 32 (.leaf 2407917223) (.leaf 2344933717))) (.branch 35 (.branch 34 (.leaf 2283685409) (.leaf 2224119411)) (.branch 36 (.leaf 2166184763) (.leaf 2109832346)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2055014793) (.leaf 2001686411)) (.branch 40 (.leaf 1949803103) (.leaf 1899322299))) (.branch 43 (.branch 42 (.leaf 1850202888) (.leaf 1802405157)) (.branch 44 (.leaf 1755890728) (.leaf 1710622503))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1666564615) (.branch 47 (.leaf 1623682369) (.leaf 1581942205))) (.branch 50 (.branch 49 (.leaf 1541311644) (.leaf 1501759250)) (.branch 51 (.leaf 1463254589) (.leaf 1425768189)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1389271502) (.leaf 1353736875)) (.branch 55 (.leaf 1319137510) (.leaf 1285447436))) (.branch 58 (.branch 57 (.leaf 1252641479) (.leaf 1220695229)) (.branch 59 (.leaf 1189585021) (.leaf 1159287898))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1129781595) (.branch 62 (.leaf 1101044511) (.leaf 1073055686))) (.branch 65 (.branch 64 (.leaf 1045794778) (.leaf 1019242046)) (.branch 66 (.leaf 993378327) (.leaf 968185014)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 943644045) (.leaf 919737876)) (.branch 70 (.leaf 896449471) (.leaf 873762283))) (.branch 73 (.branch 72 (.leaf 851660238) (.leaf 830127720)) (.branch 74 (.leaf 809149556) (.leaf 788711003))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 768797733) (.branch 77 (.leaf 749395823) (.leaf 730491739))) (.branch 80 (.branch 79 (.leaf 712072325) (.leaf 694124792)) (.branch 81 (.leaf 676636706) (.leaf 659595979)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 642990856) (.leaf 626809906)) (.branch 85 (.leaf 611042013) (.leaf 595676366))) (.branch 88 (.branch 87 (.leaf 580702449) (.leaf 566110035)) (.branch 89 (.leaf 551889173) (.leaf 538030185)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 524523654) (.branch 92 (.leaf 511360418) (.leaf 498531564))) (.branch 95 (.branch 94 (.leaf 486028418) (.leaf 473842539)) (.branch 96 (.leaf 461965714) (.leaf 450389950)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 439107468) (.leaf 428110695)) (.branch 100 (.leaf 417392264) (.leaf 406945000))) (.branch 103 (.branch 102 (.leaf 396761921) (.leaf 386836230)) (.branch 104 (.leaf 377161311) (.leaf 367730721))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 358538190) (.leaf 349577611)) (.branch 108 (.leaf 340843040) (.leaf 332328688))) (.branch 111 (.branch 110 (.leaf 324028920) (.leaf 315938246)) (.branch 112 (.leaf 308051323) (.leaf 300362947)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 292868050) (.leaf 285561696)) (.branch 116 (.leaf 278439078) (.leaf 271495514))) (.branch 119 (.branch 118 (.leaf 264726447) (.leaf 258127433)) (.branch 120 (.leaf 251694149) (.leaf 245422382)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1290).prefactor = (501596761057181/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1290).cutoff/(generalMeanRows 1290).c)).2 =
    (676975380003933/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1290).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1290).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1290).q*(generalMeanRows 1290).c/2-2 = (397/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable376.value]
    have hcontinuation : (generalMeanRows 1290).q*(generalMeanRows 1290).cutoff/2-2 = (700/73:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable429.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1290).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1290

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1290).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1290).criticalRate j.val*(generalMeanRows 1290).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1290).c*(generalMeanRows 1290).criticalPoint j.val)).2-
      (generalMeanRows 1290).J/2-(generalMeanRows 1290).error (generalMeanGrid j.val)+
      (generalMeanRows 1290).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1290).c)).2-
      (generalMeanRows 1290).J/2-(generalMeanRows 1290).error 4 := by
  have he : (generalMeanRows 1290).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1290) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1290)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1290

/-! Kernel-checked entropy margins for general spectral rectangle 1291. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1291
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6959700648) (.branch 2 (.leaf 6788575596) (.leaf 6622694406))) (.branch 5 (.branch 4 (.leaf 6461820585) (.leaf 6305734237)) (.branch 6 (.leaf 6154230427) (.leaf 6007117741)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5864217027) (.leaf 5725360282)) (.branch 10 (.leaf 5590389671) (.leaf 5459156651))) (.branch 13 (.branch 12 (.leaf 5331521196) (.leaf 5207351101)) (.branch 14 (.leaf 5086521362) (.leaf 4968913620))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4854415654) (.branch 17 (.leaf 4742920929) (.leaf 4634328189))) (.branch 20 (.branch 19 (.leaf 4528541082) (.leaf 4425467823)) (.branch 21 (.leaf 4325020884) (.leaf 4227116717)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4131675496) (.leaf 4038620879)) (.branch 25 (.leaf 3947879798) (.leaf 3859382254))) (.branch 28 (.branch 27 (.leaf 3773061141) (.leaf 3688852073)) (.branch 29 (.leaf 3606693230) (.leaf 3526525217)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3448290927) (.branch 32 (.leaf 3371935419) (.leaf 3297405805))) (.branch 35 (.branch 34 (.leaf 3224651141) (.leaf 3153622329)) (.branch 36 (.leaf 3084272026) (.leaf 3016554553)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2950425821) (.leaf 2885843250)) (.branch 40 (.leaf 2822765699) (.leaf 2761153404))) (.branch 43 (.branch 42 (.leaf 2700967911) (.leaf 2642172019)) (.branch 44 (.leaf 2584729727) (.leaf 2528606180))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2473767619) (.branch 47 (.leaf 2420181341) (.leaf 2367815648))) (.branch 50 (.branch 49 (.leaf 2316639811) (.leaf 2266624030)) (.branch 51 (.leaf 2217739396) (.leaf 2169957858)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2123252189) (.leaf 2077595956)) (.branch 55 (.leaf 2032963487) (.leaf 1989329848))) (.branch 58 (.branch 57 (.leaf 1946670811) (.leaf 1904962832)) (.branch 59 (.leaf 1864183023) (.leaf 1824309135))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1785319529) (.branch 62 (.leaf 1747193159) (.leaf 1709909551))) (.branch 65 (.branch 64 (.leaf 1673448782) (.leaf 1637791467)) (.branch 66 (.leaf 1602918733) (.leaf 1568812209)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1535454008) (.leaf 1502826709)) (.branch 70 (.leaf 1470913348) (.leaf 1439697395))) (.branch 73 (.branch 72 (.leaf 1409162751) (.leaf 1379293724)) (.branch 74 (.leaf 1350075025) (.leaf 1321491753))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1293529381) (.branch 77 (.leaf 1266173747) (.leaf 1239411044))) (.branch 80 (.branch 79 (.leaf 1213227809) (.leaf 1187610912)) (.branch 81 (.leaf 1162547546) (.leaf 1138025220)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1114031750) (.leaf 1090555246)) (.branch 85 (.leaf 1067584110) (.leaf 1045107022))) (.branch 88 (.branch 87 (.leaf 1023112938) (.leaf 1001591077)) (.branch 89 (.leaf 980530917) (.leaf 959922187)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 939754863) (.branch 92 (.leaf 920019154) (.leaf 900705506))) (.branch 95 (.branch 94 (.leaf 881804586) (.leaf 863307282)) (.branch 96 (.leaf 845204697) (.leaf 827488140)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 810149124) (.leaf 793179359)) (.branch 100 (.leaf 776570748) (.leaf 760315380))) (.branch 103 (.branch 102 (.leaf 744405529) (.leaf 728833644)) (.branch 104 (.leaf 713592349) (.leaf 698674439))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 684072871) (.leaf 669780763)) (.branch 108 (.leaf 655791392) (.leaf 642098187))) (.branch 111 (.branch 110 (.leaf 628694725) (.leaf 615574729)) (.branch 112 (.leaf 602732064) (.leaf 590160735)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 577854879) (.leaf 565808768)) (.branch 116 (.leaf 554016800) (.leaf 542473499))) (.branch 119 (.branch 118 (.leaf 531173514) (.leaf 520111610)) (.branch 120 (.leaf 509282671) (.leaf 498681694)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1291).prefactor = (5168745225036461/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1291).cutoff/(generalMeanRows 1291).c)).2 =
    (1411994129657799/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1291).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1291).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1291).q*(generalMeanRows 1291).c/2-2 = (659/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable430.value]
    have hcontinuation : (generalMeanRows 1291).q*(generalMeanRows 1291).cutoff/2-2 = (700/73:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable429.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1291).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1291

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1291).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1291).criticalRate j.val*(generalMeanRows 1291).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1291).c*(generalMeanRows 1291).criticalPoint j.val)).2-
      (generalMeanRows 1291).J/2-(generalMeanRows 1291).error (generalMeanGrid j.val)+
      (generalMeanRows 1291).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1291).c)).2-
      (generalMeanRows 1291).J/2-(generalMeanRows 1291).error 4 := by
  have he : (generalMeanRows 1291).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1291) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1291)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1291

/-! Kernel-checked entropy margins for general spectral rectangle 1292. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1292
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8254950389) (.branch 2 (.leaf 8080547651) (.leaf 7911088762))) (.branch 5 (.branch 4 (.leaf 7746347560) (.leaf 7586114417)) (.branch 6 (.leaf 7430194563) (.leaf 7278406632)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 7130581379) (.leaf 6986560553)) (.branch 10 (.leaf 6846195902) (.leaf 6709348288))) (.branch 13 (.branch 12 (.leaf 6575886905) (.leaf 6445688577)) (.branch 14 (.leaf 6318637133) (.leaf 6194622845))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 6073541925) (.branch 17 (.leaf 5955296070) (.leaf 5839792052))) (.branch 20 (.branch 19 (.leaf 5726941346) (.leaf 5616659792)) (.branch 21 (.leaf 5508867290) (.leaf 5403487522)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 5300447694) (.leaf 5199678307)) (.branch 25 (.leaf 5101112941) (.leaf 5004688064))) (.branch 28 (.branch 27 (.leaf 4910342845) (.leaf 4818018998)) (.branch 29 (.leaf 4727660621) (.leaf 4639214062)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 4552627788) (.branch 32 (.leaf 4467852262) (.leaf 4384839835))) (.branch 35 (.branch 34 (.leaf 4303544642) (.leaf 4223922505)) (.branch 36 (.leaf 4145930845) (.leaf 4069528600)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3994676146) (.leaf 3921335226)) (.branch 40 (.leaf 3849468881) (.leaf 3779041390))) (.branch 43 (.branch 42 (.leaf 3710018209) (.leaf 3642365915)) (.branch 44 (.leaf 3576052156) (.leaf 3511045602))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 3447315900) (.branch 47 (.leaf 3384833630) (.leaf 3323570262))) (.branch 50 (.branch 49 (.leaf 3263498124) (.leaf 3204590362)) (.branch 51 (.leaf 3146820907) (.leaf 3090164441)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 3034596373) (.leaf 2980092801)) (.branch 55 (.leaf 2926630493) (.leaf 2874186858))) (.branch 58 (.branch 57 (.leaf 2822739923) (.leaf 2772268307)) (.branch 59 (.leaf 2722751201) (.leaf 2674168350))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2626500026) (.branch 62 (.leaf 2579727019) (.leaf 2533830609))) (.branch 65 (.branch 64 (.leaf 2488792555) (.leaf 2444595079)) (.branch 66 (.leaf 2401220847) (.leaf 2358652955)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 2316874918) (.leaf 2275870654)) (.branch 70 (.leaf 2235624468) (.leaf 2196121047))) (.branch 73 (.branch 72 (.leaf 2157345443) (.leaf 2119283060)) (.branch 74 (.leaf 2081919649) (.leaf 2045241292))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 2009234397) (.branch 77 (.leaf 1973885684) (.leaf 1939182176))) (.branch 80 (.branch 79 (.leaf 1905111195) (.leaf 1871660347)) (.branch 81 (.leaf 1838817519) (.leaf 1806570869)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1774908817) (.leaf 1743820040)) (.branch 85 (.leaf 1713293465) (.leaf 1683318260))) (.branch 88 (.branch 87 (.leaf 1653883828) (.leaf 1624979805)) (.branch 89 (.leaf 1596596046) (.leaf 1568722627)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1541349834) (.branch 92 (.leaf 1514468159) (.leaf 1488068298))) (.branch 95 (.branch 94 (.leaf 1462141139) (.leaf 1436677763)) (.branch 96 (.leaf 1411669438) (.leaf 1387107612)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1362983910) (.leaf 1339290131)) (.branch 100 (.leaf 1316018243) (.leaf 1293160375))) (.branch 103 (.branch 102 (.leaf 1270708820) (.leaf 1248656027)) (.branch 104 (.leaf 1226994597) (.leaf 1205717279))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1184816972) (.leaf 1164286713)) (.branch 108 (.leaf 1144119681) (.leaf 1124309189))) (.branch 111 (.branch 110 (.leaf 1104848685) (.leaf 1085731743)) (.branch 112 (.leaf 1066952069) (.leaf 1048503488)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1030379950) (.leaf 1012575522)) (.branch 116 (.leaf 995084385) (.leaf 977900836))) (.branch 119 (.branch 118 (.leaf 961019282) (.leaf 944434238)) (.branch 120 (.leaf 928140326) (.leaf 912132270)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1292).prefactor = (1311717568975911/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1292).cutoff/(generalMeanRows 1292).c)).2 =
    (1465176395118109/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1292).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1292).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1292).q*(generalMeanRows 1292).c/2-2 = (271/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable076.value]
    have hcontinuation : (generalMeanRows 1292).q*(generalMeanRows 1292).cutoff/2-2 = (700/73:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable429.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1292).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1292

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1292).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1292).criticalRate j.val*(generalMeanRows 1292).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1292).c*(generalMeanRows 1292).criticalPoint j.val)).2-
      (generalMeanRows 1292).J/2-(generalMeanRows 1292).error (generalMeanGrid j.val)+
      (generalMeanRows 1292).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1292).c)).2-
      (generalMeanRows 1292).J/2-(generalMeanRows 1292).error 4 := by
  have he : (generalMeanRows 1292).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1292) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1292)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1292

/-! Kernel-checked entropy margins for general spectral rectangle 1293. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1293
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5408454339) (.branch 2 (.leaf 5262444080) (.leaf 5121160366))) (.branch 5 (.branch 4 (.leaf 4984391137) (.leaf 4851938574)) (.branch 6 (.leaf 4723617760) (.leaf 4599255500)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4478689280) (.leaf 4361766344)) (.branch 10 (.leaf 4248342865) (.leaf 4138283219))) (.branch 13 (.branch 12 (.leaf 4031459321) (.leaf 3927750036)) (.branch 14 (.leaf 3827040651) (.leaf 3729222395))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3634192007) (.branch 17 (.leaf 3541851339) (.leaf 3452107009))) (.branch 20 (.branch 19 (.leaf 3364870070) (.leaf 3280055716)) (.branch 21 (.leaf 3197583016) (.leaf 3117374662)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3039356749) (.leaf 2963458561)) (.branch 25 (.leaf 2889612382) (.leaf 2817753324))) (.branch 28 (.branch 27 (.leaf 2747819160) (.leaf 2679750174)) (.branch 29 (.leaf 2613489025) (.leaf 2548980616)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2486171974) (.branch 32 (.leaf 2425012141) (.leaf 2365452070))) (.branch 35 (.branch 34 (.leaf 2307444527) (.leaf 2250944003)) (.branch 36 (.leaf 2195906630) (.leaf 2142290099)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2090053592) (.leaf 2039157709)) (.branch 40 (.leaf 1989564405) (.leaf 1941236927))) (.branch 43 (.branch 42 (.leaf 1894139760) (.leaf 1848238572)) (.branch 44 (.leaf 1803500161) (.leaf 1759892411))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1717384244) (.branch 47 (.leaf 1675945577) (.leaf 1635547283))) (.branch 50 (.branch 49 (.leaf 1596161155) (.leaf 1557759864)) (.branch 51 (.leaf 1520316929) (.leaf 1483806683)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1448204243) (.leaf 1413485478)) (.branch 55 (.leaf 1379626986) (.leaf 1346606060))) (.branch 58 (.branch 57 (.leaf 1314400669) (.leaf 1282989431)) (.branch 59 (.leaf 1252351592) (.leaf 1222466999))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1193316084) (.branch 62 (.leaf 1164879843) (.leaf 1137139815))) (.branch 65 (.branch 64 (.leaf 1110078064) (.leaf 1083677163)) (.branch 66 (.leaf 1057920174) (.leaf 1032790637)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1008272548) (.leaf 984350348)) (.branch 70 (.leaf 961008911) (.leaf 938233523))) (.branch 73 (.branch 72 (.leaf 916009877) (.leaf 894324055)) (.branch 74 (.leaf 873162516) (.leaf 852512088))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 832359953) (.branch 77 (.leaf 812693637) (.leaf 793501002))) (.branch 80 (.branch 79 (.leaf 774770233) (.leaf 756489828)) (.branch 81 (.leaf 738648591) (.leaf 721235623)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 704240310) (.leaf 687652319)) (.branch 85 (.leaf 671461585) (.leaf 655658308))) (.branch 88 (.branch 87 (.leaf 640232943) (.leaf 625176192)) (.branch 89 (.leaf 610478998) (.leaf 596132538)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 582128218) (.branch 92 (.leaf 568457662) (.leaf 555112712))) (.branch 95 (.branch 94 (.leaf 542085416) (.leaf 529368028)) (.branch 96 (.leaf 516952997) (.leaf 504832964)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 493000759) (.leaf 481449391)) (.branch 100 (.leaf 470172046) (.leaf 459162085))) (.branch 103 (.branch 102 (.leaf 448413032) (.leaf 437918576)) (.branch 104 (.leaf 427672564) (.leaf 417668997))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 407902026) (.leaf 398365948)) (.branch 108 (.leaf 389055202) (.leaf 379964366))) (.branch 111 (.branch 110 (.leaf 371088152) (.leaf 362421404)) (.branch 112 (.leaf 353959093) (.leaf 345696314)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 337628284) (.leaf 329750338)) (.branch 116 (.leaf 322057926) (.leaf 314546610))) (.branch 119 (.branch 118 (.leaf 307212059) (.leaf 300050053)) (.branch 120 (.leaf 293056470) (.leaf 286227292)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1293).prefactor = (875465641555009/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1293).cutoff/(generalMeanRows 1293).c)).2 =
    (781744329633157/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1293).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1293).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1293).q*(generalMeanRows 1293).c/2-2 = (463/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable109.value]
    have hcontinuation : (generalMeanRows 1293).q*(generalMeanRows 1293).cutoff/2-2 = (443/37:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable431.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1293).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1293

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1293).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1293).criticalRate j.val*(generalMeanRows 1293).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1293).c*(generalMeanRows 1293).criticalPoint j.val)).2-
      (generalMeanRows 1293).J/2-(generalMeanRows 1293).error (generalMeanGrid j.val)+
      (generalMeanRows 1293).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1293).c)).2-
      (generalMeanRows 1293).J/2-(generalMeanRows 1293).error 4 := by
  have he : (generalMeanRows 1293).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1293) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1293)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1293

/-! Kernel-checked entropy margins for general spectral rectangle 1294. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1294
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5703887422) (.branch 2 (.leaf 5552864212) (.leaf 5406670401))) (.branch 5 (.branch 4 (.leaf 5265089591) (.leaf 5127919990)) (.branch 6 (.leaf 4994973031) (.leaf 4866072157)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4741051756) (.leaf 4619756200)) (.branch 10 (.leaf 4502039005) (.leaf 4387762075))) (.branch 13 (.branch 12 (.leaf 4276795025) (.leaf 4169014572)) (.branch 14 (.leaf 4064303996) (.leaf 3962552643))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3863655484) (.branch 17 (.leaf 3767512711) (.leaf 3674029372))) (.branch 20 (.branch 19 (.leaf 3583115037) (.leaf 3494683501)) (.branch 21 (.leaf 3408652500) (.leaf 3324943465)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3243481285) (.leaf 3164194098)) (.branch 25 (.leaf 3087013093) (.leaf 3011872332))) (.branch 28 (.branch 27 (.leaf 2938708582) (.leaf 2867461163)) (.branch 29 (.leaf 2798071804) (.leaf 2730484516)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2664645463) (.branch 32 (.leaf 2600502854) (.leaf 2538006837))) (.branch 35 (.branch 34 (.leaf 2477109398) (.leaf 2417764272)) (.branch 36 (.leaf 2359926856) (.leaf 2303554128)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2248604576) (.leaf 2195038125)) (.branch 40 (.leaf 2142816068) (.leaf 2091901012))) (.branch 43 (.branch 42 (.leaf 2042256813) (.leaf 1993848523)) (.branch 44 (.leaf 1946642343) (.leaf 1900605566))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1855706539) (.branch 47 (.leaf 1811914615) (.leaf 1769200113))) (.branch 50 (.branch 49 (.leaf 1727534282) (.leaf 1686889259)) (.branch 51 (.leaf 1647238040) (.leaf 1608554442)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1570813075) (.leaf 1533989311)) (.branch 55 (.leaf 1498059254) (.leaf 1462999717))) (.branch 58 (.branch 57 (.leaf 1428788194) (.leaf 1395402832)) (.branch 59 (.leaf 1362822417) (.leaf 1331026341))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1299994588) (.branch 62 (.leaf 1269707711) (.leaf 1240146814))) (.branch 65 (.branch 64 (.leaf 1211293531) (.leaf 1183130010)) (.branch 66 (.leaf 1155638896) (.leaf 1128803314)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1102606854) (.leaf 1077033556)) (.branch 70 (.leaf 1052067895) (.leaf 1027694766))) (.branch 73 (.branch 72 (.leaf 1003899476) (.leaf 980667724)) (.branch 74 (.leaf 957985593) (.leaf 935839538))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 914216374) (.branch 77 (.leaf 893103265) (.leaf 872487714))) (.branch 80 (.branch 79 (.leaf 852357551) (.leaf 832700928)) (.branch 81 (.leaf 813506302) (.leaf 794762433)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 776458373) (.leaf 758583454)) (.branch 85 (.leaf 741127287) (.leaf 724079745))) (.branch 88 (.branch 87 (.leaf 707430966) (.leaf 691171334)) (.branch 89 (.leaf 675291483) (.leaf 659782282)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 644634832) (.branch 92 (.leaf 629840460) (.leaf 615390710))) (.branch 95 (.branch 94 (.leaf 601277340) (.leaf 587492313)) (.branch 96 (.leaf 574027795) (.leaf 560876148)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 548029923) (.leaf 535481856)) (.branch 100 (.leaf 523224864) (.leaf 511252040))) (.branch 103 (.branch 102 (.leaf 499556647) (.leaf 488132114)) (.branch 104 (.leaf 476972032) (.leaf 466070151))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 455420372) (.leaf 445016747)) (.branch 108 (.leaf 434853473) (.leaf 424924889))) (.branch 111 (.branch 110 (.leaf 415225470) (.leaf 405749828)) (.branch 112 (.leaf 396492706) (.leaf 387448973)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 378613622) (.leaf 369981770)) (.branch 116 (.leaf 361548648) (.leaf 353309605))) (.branch 119 (.branch 118 (.leaf 345260101) (.leaf 337395706)) (.branch 120 (.leaf 329712095) (.leaf 322205048)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1294).prefactor = (4510119519826731/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1294).cutoff/(generalMeanRows 1294).c)).2 =
    (1571035864901697/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1294).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1294).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1294).q*(generalMeanRows 1294).c/2-2 = (113/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable124.value]
    have hcontinuation : (generalMeanRows 1294).q*(generalMeanRows 1294).cutoff/2-2 = (443/37:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable431.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1294).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1294

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1294).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1294).criticalRate j.val*(generalMeanRows 1294).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1294).c*(generalMeanRows 1294).criticalPoint j.val)).2-
      (generalMeanRows 1294).J/2-(generalMeanRows 1294).error (generalMeanGrid j.val)+
      (generalMeanRows 1294).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1294).c)).2-
      (generalMeanRows 1294).J/2-(generalMeanRows 1294).error 4 := by
  have he : (generalMeanRows 1294).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1294) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1294)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1294

/-! Kernel-checked entropy margins for general spectral rectangle 1295. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1295
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6229821559) (.branch 2 (.leaf 6072967006) (.leaf 5920977605))) (.branch 5 (.branch 4 (.leaf 5773635680) (.leaf 5630738442)) (.branch 6 (.leaf 5492096567) (.leaf 5357532953)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5226881615) (.leaf 5099986708)) (.branch 10 (.leaf 4976701657) (.leaf 4856888386))) (.branch 13 (.branch 12 (.leaf 4740416620) (.leaf 4627163266)) (.branch 14 (.leaf 4517011859) (.leaf 4409852049))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4305579157) (.branch 17 (.leaf 4204093758) (.leaf 4105301310))) (.branch 20 (.branch 19 (.leaf 4009111813) (.leaf 3915439504)) (.branch 21 (.leaf 3824202574) (.leaf 3735322908)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3648725855) (.leaf 3564340006)) (.branch 25 (.leaf 3482096999) (.leaf 3401931336))) (.branch 28 (.branch 27 (.leaf 3323780215) (.leaf 3247583373)) (.branch 29 (.leaf 3173282944) (.leaf 3100823325)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3030151054) (.branch 32 (.leaf 2961214696) (.leaf 2893964735))) (.branch 35 (.branch 34 (.leaf 2828353475) (.leaf 2764334951)) (.branch 36 (.leaf 2701864841) (.leaf 2640900384)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2581400308) (.leaf 2523324758)) (.branch 40 (.leaf 2466635232) (.leaf 2411294516))) (.branch 43 (.branch 42 (.leaf 2357266630) (.leaf 2304516771)) (.branch 44 (.leaf 2253011261) (.leaf 2202717501))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2153603924) (.branch 47 (.leaf 2105639954) (.leaf 2058795961))) (.branch 50 (.branch 49 (.leaf 2013043228) (.leaf 1968353909)) (.branch 51 (.leaf 1924701002) (.leaf 1882058309)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1840400408) (.leaf 1799702626)) (.branch 55 (.leaf 1759941008) (.leaf 1721092291))) (.branch 58 (.branch 57 (.leaf 1683133879) (.leaf 1646043821)) (.branch 59 (.leaf 1609800785) (.leaf 1574384037))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1539773422) (.branch 62 (.leaf 1505949344) (.leaf 1472892742))) (.branch 65 (.branch 64 (.leaf 1440585079) (.leaf 1409008321)) (.branch 66 (.leaf 1378144920) (.leaf 1347977801)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1318490340) (.leaf 1289666360)) (.branch 70 (.leaf 1261490108) (.leaf 1233946243))) (.branch 73 (.branch 72 (.leaf 1207019829) (.leaf 1180696316)) (.branch 74 (.leaf 1154961529) (.leaf 1129801662))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1105203260) (.branch 77 (.leaf 1081153212) (.leaf 1057638741))) (.branch 80 (.branch 79 (.leaf 1034647393) (.leaf 1012167028)) (.branch 81 (.leaf 990185811) (.leaf 968692203)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 947674952) (.leaf 927123087)) (.branch 85 (.leaf 907025907) (.leaf 887372976))) (.branch 88 (.branch 87 (.leaf 868154114) (.leaf 849359389)) (.branch 89 (.leaf 830979114) (.leaf 813003836)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 795424334) (.branch 92 (.leaf 778231606) (.leaf 761416872))) (.branch 95 (.branch 94 (.leaf 744971559) (.leaf 728887303)) (.branch 96 (.leaf 713155939) (.leaf 697769496)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 682720195) (.leaf 668000439)) (.branch 100 (.leaf 653602815) (.leaf 639520081))) (.branch 103 (.branch 102 (.leaf 625745168) (.leaf 612271175)) (.branch 104 (.leaf 599091359) (.leaf 586199140))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 573588088) (.leaf 561251925)) (.branch 108 (.leaf 549184519) (.leaf 537379880))) (.branch 111 (.branch 110 (.leaf 525832158) (.leaf 514535638)) (.branch 112 (.leaf 503484737) (.leaf 492674003)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 482098106) (.leaf 471751842)) (.branch 116 (.leaf 461630124) (.leaf 451727984))) (.branch 119 (.branch 118 (.leaf 442040567) (.leaf 432563128)) (.branch 120 (.leaf 423291031) (.leaf 414219747)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1295).prefactor = (290433700616051/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1295).cutoff/(generalMeanRows 1295).c)).2 =
    (795078453174237/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1295).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1295).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1295).q*(generalMeanRows 1295).c/2-2 = (849/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable306.value]
    have hcontinuation : (generalMeanRows 1295).q*(generalMeanRows 1295).cutoff/2-2 = (443/37:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable431.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1295).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1295

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1295).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1295).criticalRate j.val*(generalMeanRows 1295).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1295).c*(generalMeanRows 1295).criticalPoint j.val)).2-
      (generalMeanRows 1295).J/2-(generalMeanRows 1295).error (generalMeanGrid j.val)+
      (generalMeanRows 1295).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1295).c)).2-
      (generalMeanRows 1295).J/2-(generalMeanRows 1295).error 4 := by
  have he : (generalMeanRows 1295).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1295) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1295)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1295

/-! Kernel-checked entropy margins for general spectral rectangle 1296. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1296
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6828567445) (.branch 2 (.leaf 6669068703) (.leaf 6514312691))) (.branch 5 (.branch 4 (.leaf 6364086682) (.leaf 6218192796)) (.branch 6 (.leaf 6076446559) (.leaf 5938675656)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5804718806) (.leaf 5674424791)) (.branch 10 (.leaf 5547651571) (.leaf 5424265509))) (.branch 13 (.branch 12 (.leaf 5304140674) (.leaf 5187158218)) (.branch 14 (.leaf 5073205812) (.leaf 4962177149))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4853971479) (.branch 17 (.leaf 4748493209) (.leaf 4645651518))) (.branch 20 (.branch 19 (.leaf 4545360029) (.leaf 4447536496)) (.branch 21 (.leaf 4352102523) (.leaf 4258983310)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4168107418) (.leaf 4079406553)) (.branch 25 (.leaf 3992815370) (.leaf 3908271296))) (.branch 28 (.branch 27 (.leaf 3825714353) (.leaf 3745087017)) (.branch 29 (.leaf 3666334067) (.leaf 3589402459)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3514241200) (.branch 32 (.leaf 3440801243) (.leaf 3369035373))) (.branch 35 (.branch 34 (.leaf 3298898120) (.leaf 3230345660)) (.branch 36 (.leaf 3163335737) (.leaf 3097827584)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3033781844) (.leaf 2971160511)) (.branch 40 (.leaf 2909926857) (.leaf 2850045379))) (.branch 43 (.branch 42 (.leaf 2791481738) (.leaf 2734202708)) (.branch 44 (.leaf 2678176129) (.leaf 2623370856))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2569756717) (.branch 47 (.leaf 2517304471) (.leaf 2465985774))) (.branch 50 (.branch 49 (.leaf 2415773132) (.leaf 2366639876)) (.branch 51 (.leaf 2318560125) (.leaf 2271508755)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2225461368) (.leaf 2180394269)) (.branch 55 (.leaf 2136284432) (.leaf 2093109484))) (.branch 58 (.branch 57 (.leaf 2050847674) (.leaf 2009477852)) (.branch 59 (.leaf 1968979448) (.leaf 1929332453))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1890517397) (.branch 62 (.leaf 1852515331) (.leaf 1815307809))) (.branch 65 (.branch 64 (.leaf 1778876871) (.leaf 1743205029)) (.branch 66 (.leaf 1708275247) (.leaf 1674070931)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1640575911) (.leaf 1607774428)) (.branch 70 (.leaf 1575651125) (.leaf 1544191027))) (.branch 73 (.branch 72 (.leaf 1513379537) (.leaf 1483202420)) (.branch 74 (.leaf 1453645790) (.leaf 1424696107))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1396340158) (.branch 77 (.leaf 1368565052) (.leaf 1341358212))) (.branch 80 (.branch 79 (.leaf 1314707362) (.leaf 1288600519)) (.branch 81 (.leaf 1263025988) (.leaf 1237972350)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1213428456) (.leaf 1189383419)) (.branch 85 (.leaf 1165826608) (.leaf 1142747638))) (.branch 88 (.branch 87 (.leaf 1120136366) (.leaf 1097982885)) (.branch 89 (.leaf 1076277514) (.leaf 1055010797)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1034173491) (.branch 92 (.leaf 1013756565) (.leaf 993751195))) (.branch 95 (.branch 94 (.leaf 974148754) (.leaf 954940811)) (.branch 96 (.leaf 936119124) (.leaf 917675636)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 899602471) (.leaf 881891926)) (.branch 100 (.leaf 864536471) (.leaf 847528744))) (.branch 103 (.branch 102 (.leaf 830861542) (.leaf 814527824)) (.branch 104 (.leaf 798520701) (.leaf 782833438))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 767459445) (.leaf 752392275)) (.branch 108 (.leaf 737625625) (.leaf 723153324))) (.branch 111 (.branch 110 (.leaf 708969338) (.leaf 695067761)) (.branch 112 (.leaf 681442817) (.leaf 668088853)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 655000335) (.leaf 642171852)) (.branch 116 (.leaf 629598105) (.leaf 617273909))) (.branch 119 (.branch 118 (.leaf 605194190) (.leaf 593353983)) (.branch 120 (.leaf 581748426) (.leaf 570372760)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1296).prefactor = (1173365496129459/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1296).cutoff/(generalMeanRows 1296).c)).2 =
    (161755588053659/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1296).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1296).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1296).q*(generalMeanRows 1296).c/2-2 = (193/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable071.value]
    have hcontinuation : (generalMeanRows 1296).q*(generalMeanRows 1296).cutoff/2-2 = (443/37:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable431.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1296).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1296

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1296).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1296).criticalRate j.val*(generalMeanRows 1296).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1296).c*(generalMeanRows 1296).criticalPoint j.val)).2-
      (generalMeanRows 1296).J/2-(generalMeanRows 1296).error (generalMeanGrid j.val)+
      (generalMeanRows 1296).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1296).c)).2-
      (generalMeanRows 1296).J/2-(generalMeanRows 1296).error 4 := by
  have he : (generalMeanRows 1296).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1296) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1296)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1296

/-! Kernel-checked entropy margins for general spectral rectangle 1297. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1297
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4605060154) (.branch 2 (.leaf 4469865415) (.leaf 4339295780))) (.branch 5 (.branch 4 (.leaf 4213141862) (.leaf 4091207996)) (.branch 6 (.leaf 3973310993) (.leaf 3859279024)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3748950641) (.leaf 3642173903)) (.branch 10 (.leaf 3538805588) (.leaf 3438710503))) (.branch 13 (.branch 12 (.leaf 3341760850) (.leaf 3247835664)) (.branch 14 (.leaf 3156820307) (.leaf 3068606006))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2983089434) (.branch 17 (.leaf 2900172338) (.leaf 2819761192))) (.branch 20 (.branch 19 (.leaf 2741766882) (.leaf 2666104424)) (.branch 21 (.leaf 2592692697) (.leaf 2521454206)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2452314863) (.leaf 2385203780)) (.branch 25 (.leaf 2320053085) (.leaf 2256797748))) (.branch 28 (.branch 27 (.leaf 2195375421) (.leaf 2135726294)) (.branch 29 (.leaf 2077792953) (.leaf 2021520254)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1966855208) (.branch 32 (.leaf 1913746868) (.leaf 1862146225))) (.branch 35 (.branch 34 (.leaf 1812006115) (.leaf 1763281128)) (.branch 36 (.leaf 1715927525) (.leaf 1669903157)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1625167393) (.leaf 1581681051)) (.branch 40 (.leaf 1539406332) (.leaf 1498306759))) (.branch 43 (.branch 42 (.leaf 1458347119) (.leaf 1419493409)) (.branch 44 (.leaf 1381712782) (.leaf 1344973505))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1309244904) (.branch 47 (.leaf 1274497327) (.leaf 1240702102))) (.branch 50 (.branch 49 (.leaf 1207831495) (.leaf 1175858674)) (.branch 51 (.leaf 1144757678) (.leaf 1114503375)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1085071438) (.leaf 1056438312)) (.branch 55 (.leaf 1028581184) (.leaf 1001477956))) (.branch 58 (.branch 57 (.leaf 975107219) (.leaf 949448230)) (.branch 59 (.leaf 924480883) (.leaf 900185691))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 876543763) (.branch 62 (.leaf 853536782) (.leaf 831146985))) (.branch 65 (.branch 64 (.leaf 809357145) (.leaf 788150551)) (.branch 66 (.leaf 767510993) (.leaf 747422742)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 727870537) (.leaf 708839566)) (.branch 70 (.leaf 690315455) (.leaf 672284250))) (.branch 73 (.branch 72 (.leaf 654732405) (.leaf 637646770)) (.branch 74 (.leaf 621014575) (.leaf 604823421))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 589061266) (.branch 77 (.leaf 573716416) (.leaf 558777510))) (.branch 80 (.branch 79 (.leaf 544233514) (.leaf 530073709)) (.branch 81 (.leaf 516287679) (.leaf 502865306)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 489796758) (.leaf 477072480)) (.branch 85 (.leaf 464683186) (.leaf 452619853))) (.branch 88 (.branch 87 (.leaf 440873710) (.leaf 429436230)) (.branch 89 (.leaf 418299127) (.leaf 407454346)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 396894053) (.branch 92 (.leaf 386610634) (.leaf 376596686))) (.branch 95 (.branch 94 (.leaf 366845012) (.leaf 357348610)) (.branch 96 (.leaf 348100675) (.leaf 339094588)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 330323910) (.leaf 321782383)) (.branch 100 (.leaf 313463916) (.leaf 305362588))) (.branch 103 (.branch 102 (.leaf 297472637) (.leaf 289788460)) (.branch 104 (.leaf 282304607) (.leaf 275015774))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 267916804) (.leaf 261002678)) (.branch 108 (.leaf 254268513) (.leaf 247709559))) (.branch 111 (.branch 110 (.leaf 241321194) (.leaf 235098921)) (.branch 112 (.leaf 229038364) (.leaf 223135265)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 217385481) (.leaf 211784980)) (.branch 116 (.leaf 206329838) (.leaf 201016237))) (.branch 119 (.branch 118 (.leaf 195840461) (.leaf 190798893)) (.branch 120 (.leaf 185888013) (.leaf 181104396)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1297).prefactor = (4049132610671703/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1297).cutoff/(generalMeanRows 1297).c)).2 =
    (1794534592920047/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1297).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1297).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1297).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1297

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1297).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1297).criticalRate j.val*(generalMeanRows 1297).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1297).c*(generalMeanRows 1297).criticalPoint j.val)).2-
      (generalMeanRows 1297).J/2-(generalMeanRows 1297).error (generalMeanGrid j.val)+
      (generalMeanRows 1297).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1297).c)).2-
      (generalMeanRows 1297).J/2-(generalMeanRows 1297).error 4 := by
  have he : (generalMeanRows 1297).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1297) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1297)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1297

/-! Kernel-checked entropy margins for general spectral rectangle 1298. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1298
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5489482641) (.branch 2 (.leaf 5328464102) (.leaf 5172951873))) (.branch 5 (.branch 4 (.leaf 5022696424) (.leaf 4877464648)) (.branch 6 (.leaf 4737038351) (.leaf 4601212917)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4469796116) (.leaf 4342607061)) (.branch 10 (.leaf 4219475266) (.leaf 4100239813))) (.branch 13 (.branch 12 (.leaf 3984748595) (.leaf 3872857649)) (.branch 14 (.leaf 3764430544) (.leaf 3659337833))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3557456558) (.branch 17 (.leaf 3458669797) (.leaf 3362866254))) (.branch 20 (.branch 19 (.leaf 3269939890) (.leaf 3179789574)) (.branch 21 (.leaf 3092318779) (.leaf 3007435291)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2925050948) (.leaf 2845081399)) (.branch 25 (.leaf 2767445878) (.leaf 2692067005))) (.branch 28 (.branch 27 (.leaf 2618870589) (.leaf 2547785457)) (.branch 29 (.leaf 2478743291) (.leaf 2411678470)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2346527940) (.branch 32 (.leaf 2283231072) (.leaf 2221729548))) (.branch 35 (.branch 34 (.leaf 2161967242) (.leaf 2103890115)) (.branch 36 (.leaf 2047446115) (.leaf 1992585084)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1939258670) (.leaf 1887420241)) (.branch 40 (.leaf 1837024816) (.leaf 1788028981))) (.branch 43 (.branch 42 (.leaf 1740390829) (.leaf 1694069891)) (.branch 44 (.leaf 1649027078) (.leaf 1605224617))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1562626004) (.branch 47 (.leaf 1521195946) (.leaf 1480900315))) (.branch 50 (.branch 49 (.leaf 1441706103) (.leaf 1403581374)) (.branch 51 (.leaf 1366495222) (.leaf 1330417738)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1295319962) (.leaf 1261173855)) (.branch 55 (.leaf 1227952262) (.leaf 1195628877))) (.branch 58 (.branch 57 (.leaf 1164178216) (.leaf 1133575583)) (.branch 59 (.leaf 1103797046) (.leaf 1074819404))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1046620169) (.branch 62 (.leaf 1019177531) (.leaf 992470344))) (.branch 65 (.branch 64 (.leaf 966478098) (.leaf 941180896)) (.branch 66 (.leaf 916559439) (.leaf 892595000)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 869269405) (.leaf 846565020)) (.branch 70 (.leaf 824464728) (.leaf 802951914))) (.branch 73 (.branch 72 (.leaf 782010448) (.leaf 761624670)) (.branch 74 (.leaf 741779373) (.leaf 722459792))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 703651587) (.branch 77 (.leaf 685340830) (.leaf 667513991))) (.branch 80 (.branch 79 (.leaf 650157930) (.leaf 633259879)) (.branch 81 (.leaf 616807434) (.leaf 600788543)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 585191495) (.leaf 570004910)) (.branch 85 (.leaf 555217727) (.leaf 540819197))) (.branch 88 (.branch 87 (.leaf 526798871) (.leaf 513146596)) (.branch 89 (.leaf 499852497) (.leaf 486906979)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 474300711) (.branch 92 (.leaf 462024621) (.leaf 450069890))) (.branch 95 (.branch 94 (.leaf 438427941) (.leaf 427090436)) (.branch 96 (.leaf 416049263) (.leaf 405296538)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 394824589) (.leaf 384625957)) (.branch 100 (.leaf 374693387) (.leaf 365019821))) (.branch 103 (.branch 102 (.leaf 355598394) (.leaf 346422430)) (.branch 104 (.leaf 337485433) (.leaf 328781083))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 320303232) (.leaf 312045901)) (.branch 108 (.leaf 304003269) (.leaf 296169676))) (.branch 111 (.branch 110 (.leaf 288539611) (.leaf 281107717)) (.branch 112 (.leaf 273868775) (.leaf 266817712)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 259949588) (.leaf 253259597)) (.branch 116 (.leaf 246743062) (.leaf 240395431))) (.branch 119 (.branch 118 (.leaf 234212274) (.leaf 228189280)) (.branch 120 (.leaf 222322251) (.leaf 216607105)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1298).prefactor = (493315625311101/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1298).cutoff/(generalMeanRows 1298).c)).2 =
    (1530213870381441/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1298).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1298).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1298).q*(generalMeanRows 1298).c/2-2 = (41/40:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable033.value]
    have hcontinuation : (generalMeanRows 1298).q*(generalMeanRows 1298).cutoff/2-2 = (443/37:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable431.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1298).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1298

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1298).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1298).criticalRate j.val*(generalMeanRows 1298).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1298).c*(generalMeanRows 1298).criticalPoint j.val)).2-
      (generalMeanRows 1298).J/2-(generalMeanRows 1298).error (generalMeanGrid j.val)+
      (generalMeanRows 1298).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1298).c)).2-
      (generalMeanRows 1298).J/2-(generalMeanRows 1298).error 4 := by
  have he : (generalMeanRows 1298).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1298) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1298)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1298

/-! Kernel-checked entropy margins for general spectral rectangle 1299. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1299
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6814161585) (.branch 2 (.leaf 6642594510) (.leaf 6476348923))) (.branch 5 (.branch 4 (.leaf 6315186734) (.leaf 6158886129)) (.branch 6 (.leaf 6007240030) (.leaf 5860054722)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5717148650) (.leaf 5578351351)) (.branch 10 (.leaf 5443502504) (.leaf 5312451079))) (.branch 13 (.branch 12 (.leaf 5185054584) (.leaf 5061178379)) (.branch 14 (.leaf 4940695074) (.leaf 4823483971))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4709430570) (.branch 17 (.leaf 4598426122) (.leaf 4490367215))) (.branch 20 (.branch 19 (.leaf 4385155409) (.leaf 4282696897)) (.branch 21 (.leaf 4182902195) (.leaf 4085685863)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3990966246) (.leaf 3898665237)) (.branch 25 (.leaf 3808708064) (.leaf 3721023084))) (.branch 28 (.branch 27 (.leaf 3635541604) (.leaf 3552197708)) (.branch 29 (.leaf 3470928104) (.leaf 3391671974)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3314370840) (.branch 32 (.leaf 3238968442) (.leaf 3165410620))) (.branch 35 (.branch 34 (.leaf 3093645206) (.leaf 3023621922)) (.branch 36 (.leaf 2955292288) (.leaf 2888609534)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2823528515) (.leaf 2760005639)) (.branch 40 (.leaf 2697998792) (.leaf 2637467270))) (.branch 43 (.branch 42 (.leaf 2578371718) (.leaf 2520674068)) (.branch 44 (.leaf 2464337484) (.leaf 2409326308))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2355606014) (.branch 47 (.leaf 2303143156) (.leaf 2251905326))) (.branch 50 (.branch 49 (.leaf 2201861113) (.leaf 2152980060)) (.branch 51 (.leaf 2105232631) (.leaf 2058590171)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2013024875) (.leaf 1968509753)) (.branch 55 (.leaf 1925018605) (.leaf 1882525986))) (.branch 58 (.branch 57 (.leaf 1841007180) (.leaf 1800438178)) (.branch 59 (.leaf 1760795645) (.leaf 1722056904))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1684199909) (.branch 62 (.leaf 1647203226) (.leaf 1611046006))) (.branch 65 (.branch 64 (.leaf 1575707974) (.leaf 1541169403)) (.branch 66 (.leaf 1507411101) (.leaf 1474414389)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1442161087) (.leaf 1410633497)) (.branch 70 (.leaf 1379814390) (.leaf 1349686987))) (.branch 73 (.branch 72 (.leaf 1320234950) (.leaf 1291442364)) (.branch 74 (.leaf 1263293725) (.leaf 1235773932))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1208868268) (.branch 77 (.leaf 1182562392) (.leaf 1156842329))) (.branch 80 (.branch 79 (.leaf 1131694456) (.leaf 1107105495)) (.branch 81 (.leaf 1083062501) (.leaf 1059552851)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1036564241) (.leaf 1014084668)) (.branch 85 (.leaf 992102428) (.leaf 970606106))) (.branch 88 (.branch 87 (.leaf 949584567) (.leaf 929026949)) (.branch 89 (.leaf 908922656) (.leaf 889261347)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 870032936) (.branch 92 (.leaf 851227578) (.leaf 832835668))) (.branch 95 (.branch 94 (.leaf 814847830) (.leaf 797254916)) (.branch 96 (.leaf 780047993) (.leaf 763218345)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 746757460) (.leaf 730657033)) (.branch 100 (.leaf 714908950) (.leaf 699505295))) (.branch 103 (.branch 102 (.leaf 684438334) (.leaf 669700517)) (.branch 104 (.leaf 655284471) (.leaf 641182997))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 627389064) (.leaf 613895803)) (.branch 108 (.leaf 600696507) (.leaf 587784626))) (.branch 111 (.branch 110 (.leaf 575153759) (.leaf 562797657)) (.branch 112 (.leaf 550710213) (.leaf 538885461)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 527317574) (.leaf 516000859)) (.branch 116 (.leaf 504929752) (.leaf 494098819))) (.branch 119 (.branch 118 (.leaf 483502749) (.leaf 473136352)) (.branch 120 (.leaf 462994559) (.leaf 453072414)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1299).prefactor = (635351156442651/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1299).cutoff/(generalMeanRows 1299).c)).2 =
    (795078453174237/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1299).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1299).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1299).q*(generalMeanRows 1299).c/2-2 = (849/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable306.value]
    have hcontinuation : (generalMeanRows 1299).q*(generalMeanRows 1299).cutoff/2-2 = (443/37:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable431.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1299).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1299

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1299).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1299).criticalRate j.val*(generalMeanRows 1299).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1299).c*(generalMeanRows 1299).criticalPoint j.val)).2-
      (generalMeanRows 1299).J/2-(generalMeanRows 1299).error (generalMeanGrid j.val)+
      (generalMeanRows 1299).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1299).c)).2-
      (generalMeanRows 1299).J/2-(generalMeanRows 1299).error 4 := by
  have he : (generalMeanRows 1299).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1299) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1299)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1299

/-! Kernel-checked entropy margins for general spectral rectangle 1300. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1300
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8174132500) (.branch 2 (.leaf 7995970598) (.leaf 7822923489))) (.branch 5 (.branch 4 (.leaf 7654760174) (.leaf 7491266071)) (.branch 6 (.leaf 7332241416) (.leaf 7177499857)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 7026867216) (.leaf 6880180390)) (.branch 10 (.leaf 6737286376) (.leaf 6598041402))) (.branch 13 (.branch 12 (.leaf 6462310154) (.leaf 6329965080)) (.branch 14 (.leaf 6200885769) (.leaf 6074958389))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5952075182) (.branch 17 (.leaf 5832134009) (.leaf 5715037935))) (.branch 20 (.branch 19 (.leaf 5600694854) (.leaf 5489017149)) (.branch 21 (.leaf 5379921383) (.leaf 5273328012)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 5169161128) (.leaf 5067348226)) (.branch 25 (.leaf 4967819979) (.leaf 4870510045))) (.branch 28 (.branch 27 (.leaf 4775354883) (.leaf 4682293579)) (.branch 29 (.leaf 4591267698) (.leaf 4502221133)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 4415099978) (.branch 32 (.leaf 4329852400) (.leaf 4246428527))) (.branch 35 (.branch 34 (.leaf 4164780345) (.leaf 4084861592)) (.branch 36 (.leaf 4006627674) (.leaf 3930035576)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3855043783) (.leaf 3781612204)) (.branch 40 (.leaf 3709702107) (.leaf 3639276050))) (.branch 43 (.branch 42 (.leaf 3570297821) (.leaf 3502732381)) (.branch 44 (.leaf 3436545814) (.leaf 3371705270))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 3308178922) (.branch 47 (.leaf 3245935924) (.leaf 3184946364))) (.branch 50 (.branch 49 (.leaf 3125181225) (.leaf 3066612351)) (.branch 51 (.leaf 3009212412) (.leaf 2952954866)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2897813933) (.leaf 2843764561)) (.branch 55 (.leaf 2790782401) (.leaf 2738843778))) (.branch 58 (.branch 57 (.leaf 2687925667) (.leaf 2638005669)) (.branch 59 (.leaf 2589061987) (.leaf 2541073406))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2494019270) (.branch 62 (.leaf 2447879465) (.leaf 2402634399))) (.branch 65 (.branch 64 (.leaf 2358264981) (.leaf 2314752610)) (.branch 66 (.leaf 2272079156) (.leaf 2230226942)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 2189178733) (.leaf 2148917719)) (.branch 70 (.leaf 2109427502) (.leaf 2070692086))) (.branch 73 (.branch 72 (.leaf 2032695859) (.leaf 1995423585)) (.branch 74 (.leaf 1958860394) (.leaf 1922991766))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1887803522) (.branch 77 (.leaf 1853281819) (.leaf 1819413133))) (.branch 80 (.branch 79 (.leaf 1786184254) (.leaf 1753582276)) (.branch 81 (.leaf 1721594588) (.leaf 1690208864)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1659413062) (.leaf 1629195405)) (.branch 85 (.leaf 1599544384) (.leaf 1570448745))) (.branch 88 (.branch 87 (.leaf 1541897483) (.leaf 1513879837)) (.branch 89 (.leaf 1486385283) (.leaf 1459403525)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1432924493) (.branch 92 (.leaf 1406938334) (.leaf 1381435409))) (.branch 95 (.branch 94 (.leaf 1356406286) (.leaf 1331841735)) (.branch 96 (.leaf 1307732723) (.leaf 1284070407)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1260846136) (.leaf 1238051436)) (.branch 100 (.leaf 1215678014) (.leaf 1193717752))) (.branch 103 (.branch 102 (.leaf 1172162699) (.leaf 1151005071)) (.branch 104 (.leaf 1130237245) (.leaf 1109851755))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1089841291) (.leaf 1070198690)) (.branch 108 (.leaf 1050916939) (.leaf 1031989166))) (.branch 111 (.branch 110 (.leaf 1013408642) (.leaf 995168771)) (.branch 112 (.leaf 977263094) (.leaf 959685280)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 942429127) (.leaf 925488559)) (.branch 116 (.leaf 908857619) (.leaf 892530471))) (.branch 119 (.branch 118 (.leaf 876501397) (.leaf 860764789)) (.branch 120 (.leaf 845315154) (.leaf 830147107)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1300).prefactor = (1047400429340161/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1300).cutoff/(generalMeanRows 1300).c)).2 =
    (1641653432115649/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1300).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1300).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1300).q*(generalMeanRows 1300).c/2-2 = (353/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable084.value]
    have hcontinuation : (generalMeanRows 1300).q*(generalMeanRows 1300).cutoff/2-2 = (443/37:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable431.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1300).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1300

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1300).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1300).criticalRate j.val*(generalMeanRows 1300).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1300).c*(generalMeanRows 1300).criticalPoint j.val)).2-
      (generalMeanRows 1300).J/2-(generalMeanRows 1300).error (generalMeanGrid j.val)+
      (generalMeanRows 1300).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1300).c)).2-
      (generalMeanRows 1300).J/2-(generalMeanRows 1300).error 4 := by
  have he : (generalMeanRows 1300).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1300) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1300)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1300

/-! Kernel-checked entropy margins for general spectral rectangle 1301. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1301
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5822833402) (.branch 2 (.leaf 5671088894) (.leaf 5524148469))) (.branch 5 (.branch 4 (.leaf 5381797292) (.leaf 5243835027)) (.branch 6 (.leaf 5110074473) (.leaf 4980340370)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4854468337) (.leaf 4732303924)) (.branch 10 (.leaf 4613701776) (.leaf 4498524882))) (.branch 13 (.branch 12 (.leaf 4386643898) (.leaf 4277936551)) (.branch 14 (.leaf 4172287088) (.leaf 4069585791))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3969728533) (.branch 17 (.leaf 3872616377) (.leaf 3778155208))) (.branch 20 (.branch 19 (.leaf 3686255410) (.leaf 3596831554)) (.branch 21 (.leaf 3509802132) (.leaf 3425089297)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3342618636) (.leaf 3262318959)) (.branch 25 (.leaf 3184122101) (.leaf 3107962745))) (.branch 28 (.branch 27 (.leaf 3033778256) (.leaf 2961508525)) (.branch 29 (.leaf 2891095835) (.leaf 2822484722)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2755621858) (.branch 32 (.leaf 2690455938) (.leaf 2626937574))) (.branch 35 (.branch 34 (.leaf 2565019197) (.leaf 2504654969)) (.branch 36 (.leaf 2445800694) (.leaf 2388413739)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2332452963) (.leaf 2277878644)) (.branch 40 (.leaf 2224652415) (.leaf 2172737204))) (.branch 43 (.branch 42 (.leaf 2122097173) (.leaf 2072697666)) (.branch 44 (.leaf 2024505159) (.leaf 1977487209))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1931612410) (.branch 47 (.leaf 1886850353) (.leaf 1843171580))) (.branch 50 (.branch 49 (.leaf 1800547548) (.leaf 1758950596)) (.branch 51 (.leaf 1718353904) (.leaf 1678731468)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1640058062) (.leaf 1602309214)) (.branch 55 (.leaf 1565461172) (.leaf 1529490886))) (.branch 58 (.branch 57 (.leaf 1494375974) (.leaf 1460094703)) (.branch 59 (.leaf 1426625965) (.leaf 1393949254))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1362044645) (.branch 62 (.leaf 1330892778) (.leaf 1300474831))) (.branch 65 (.branch 64 (.leaf 1270772510) (.leaf 1241768025)) (.branch 66 (.leaf 1213444079) (.leaf 1185783846)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1158770961) (.leaf 1132389501)) (.branch 70 (.leaf 1106623974) (.leaf 1081459303))) (.branch 73 (.branch 72 (.leaf 1056880815) (.leaf 1032874227)) (.branch 74 (.leaf 1009425635) (.leaf 986521501))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 964148643) (.branch 77 (.leaf 942294225) (.leaf 920945744))) (.branch 80 (.branch 79 (.leaf 900091021) (.leaf 879718196)) (.branch 81 (.leaf 859815710) (.leaf 840372305)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 821377008) (.leaf 802819128)) (.branch 85 (.leaf 784688244) (.leaf 766974203))) (.branch 88 (.branch 87 (.leaf 749667104) (.leaf 732757298)) (.branch 89 (.leaf 716235379) (.leaf 700092175)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 684318745) (.branch 92 (.leaf 668906369) (.leaf 653846546))) (.branch 95 (.branch 94 (.leaf 639130983) (.leaf 624751596)) (.branch 96 (.leaf 610700496) (.leaf 596969991)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 583552578) (.leaf 570440938)) (.branch 100 (.leaf 557627929) (.leaf 545106584))) (.branch 103 (.branch 102 (.leaf 532870109) (.leaf 520911870)) (.branch 104 (.leaf 509225397) (.leaf 497804376))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 486642647) (.leaf 475734196)) (.branch 108 (.leaf 465073155) (.leaf 454653798))) (.branch 111 (.branch 110 (.leaf 444470535) (.leaf 434517910)) (.branch 112 (.leaf 424790600) (.leaf 415283406)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 405991254) (.leaf 396909191)) (.branch 116 (.leaf 388032383) (.leaf 379356109))) (.branch 119 (.branch 118 (.leaf 370875760) (.leaf 362586838)) (.branch 120 (.leaf 354484949) (.leaf 346565804)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1301).prefactor = (1104072049212821/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1301).cutoff/(generalMeanRows 1301).c)).2 =
    (1828393106218733/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1301).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1301).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1301).q*(generalMeanRows 1301).c/2-2 = (7091/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable432.value]
    have hcontinuation : (generalMeanRows 1301).q*(generalMeanRows 1301).cutoff/2-2 = (3592/225:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable433.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1301).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1301

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1301).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1301).criticalRate j.val*(generalMeanRows 1301).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1301).c*(generalMeanRows 1301).criticalPoint j.val)).2-
      (generalMeanRows 1301).J/2-(generalMeanRows 1301).error (generalMeanGrid j.val)+
      (generalMeanRows 1301).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1301).c)).2-
      (generalMeanRows 1301).J/2-(generalMeanRows 1301).error 4 := by
  have he : (generalMeanRows 1301).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1301) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1301)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1301

/-! Kernel-checked entropy margins for general spectral rectangle 1302. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1302
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5997877872) (.branch 2 (.leaf 5841571661) (.leaf 5690213952))) (.branch 5 (.branch 4 (.leaf 5543583452) (.leaf 5401473801)) (.branch 6 (.leaf 5263692173) (.leaf 5130058038)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5000402073) (.leaf 4874565186)) (.branch 10 (.leaf 4752397652) (.leaf 4633758341))) (.branch 13 (.branch 12 (.leaf 4518514021) (.leaf 4406538742)) (.branch 14 (.leaf 4297713273) (.leaf 4191924597))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4089065457) (.branch 17 (.leaf 3989033941) (.leaf 3891733106))) (.branch 20 (.branch 19 (.leaf 3797070640) (.leaf 3704958548)) (.branch 21 (.leaf 3615312871) (.leaf 3528053421)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3443103549) (.leaf 3360389924)) (.branch 25 (.leaf 3279842333) (.leaf 3201393495))) (.branch 28 (.branch 27 (.leaf 3124978891) (.leaf 3050536607)) (.branch 29 (.leaf 2978007189) (.leaf 2907333507)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2838460629) (.branch 32 (.leaf 2771335709) (.leaf 2705907873))) (.branch 35 (.branch 34 (.leaf 2642128123) (.leaf 2579949241)) (.branch 36 (.leaf 2519325704) (.leaf 2460213598)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2402570544) (.leaf 2346355626)) (.branch 40 (.leaf 2291529325) (.leaf 2238053453))) (.branch 43 (.branch 42 (.leaf 2185891094) (.leaf 2135006552)) (.branch 44 (.leaf 2085365295) (.leaf 2036933904))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1989680029) (.branch 47 (.leaf 1943572347) (.leaf 1898580514))) (.branch 50 (.branch 49 (.leaf 1854675130) (.leaf 1811827701)) (.branch 51 (.leaf 1770010603) (.leaf 1729197047)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1689361052) (.leaf 1650477407)) (.branch 55 (.leaf 1612521650) (.leaf 1575470034))) (.branch 58 (.branch 57 (.leaf 1539299507) (.leaf 1503987682)) (.branch 59 (.leaf 1469512815) (.leaf 1435853785))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1402990069) (.branch 62 (.leaf 1370901723) (.leaf 1339569360))) (.branch 65 (.branch 64 (.leaf 1308974135) (.leaf 1279097726)) (.branch 66 (.leaf 1249922312) (.leaf 1221430565)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1193605626) (.leaf 1166431093)) (.branch 70 (.leaf 1139891009) (.leaf 1113969845))) (.branch 73 (.branch 72 (.leaf 1088652485) (.leaf 1063924218)) (.branch 74 (.leaf 1039770720) (.leaf 1016178048))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 993132624) (.branch 77 (.leaf 970621223) (.leaf 948630970))) (.branch 80 (.branch 79 (.leaf 927149318) (.leaf 906164050)) (.branch 81 (.leaf 885663262) (.leaf 865635354)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 846069025) (.leaf 826953263)) (.branch 85 (.leaf 808277334) (.leaf 790030777))) (.branch 88 (.branch 87 (.leaf 772203397) (.leaf 754785253)) (.branch 89 (.leaf 737766656) (.leaf 721138160)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 704890553) (.branch 92 (.leaf 689014854) (.leaf 673502307))) (.branch 95 (.branch 94 (.leaf 658344369) (.leaf 643532712)) (.branch 96 (.leaf 629059212) (.leaf 614915944)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 601095181) (.leaf 587589382)) (.branch 100 (.leaf 574391191) (.leaf 561493434))) (.branch 103 (.branch 102 (.leaf 548889108) (.leaf 536571384)) (.branch 104 (.leaf 524533595) (.leaf 512769239))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 501271969) (.leaf 490035591)) (.branch 108 (.leaf 479054060) (.leaf 468321479))) (.branch 111 (.branch 110 (.leaf 457832090) (.leaf 447580272)) (.branch 112 (.leaf 437560542) (.leaf 427767545)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 418196055) (.leaf 408840970)) (.branch 116 (.leaf 399697309) (.leaf 390760211))) (.branch 119 (.branch 118 (.leaf 382024929) (.leaf 373486827)) (.branch 120 (.leaf 365141381) (.leaf 356984173)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1302).prefactor = (4549049478609437/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1302).cutoff/(generalMeanRows 1302).c)).2 =
    (1828393106218733/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1302).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1302).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1302).q*(generalMeanRows 1302).c/2-2 = (7091/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable432.value]
    have hcontinuation : (generalMeanRows 1302).q*(generalMeanRows 1302).cutoff/2-2 = (3592/225:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable433.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1302).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1302

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1302).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1302).criticalRate j.val*(generalMeanRows 1302).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1302).c*(generalMeanRows 1302).criticalPoint j.val)).2-
      (generalMeanRows 1302).J/2-(generalMeanRows 1302).error (generalMeanGrid j.val)+
      (generalMeanRows 1302).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1302).c)).2-
      (generalMeanRows 1302).J/2-(generalMeanRows 1302).error 4 := by
  have he : (generalMeanRows 1302).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1302) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1302)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1302

/-! Kernel-checked entropy margins for general spectral rectangle 1303. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1303
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6636291412) (.branch 2 (.leaf 6476835110) (.leaf 6322192909))) (.branch 5 (.branch 4 (.leaf 6172149503) (.leaf 6026504430)) (.branch 6 (.leaf 5885070664) (.leaf 5747673366)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5614148786) (.leaf 5484343285)) (.branch 10 (.leaf 5358112464) (.leaf 5235320387))) (.branch 13 (.branch 12 (.leaf 5115838886) (.leaf 4999546942)) (.branch 14 (.leaf 4886330119) (.leaf 4776080061))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4668694037) (.branch 17 (.leaf 4564074531) (.leaf 4462128862))) (.branch 20 (.branch 19 (.leaf 4362768848) (.leaf 4265910496)) (.branch 21 (.leaf 4171473722) (.leaf 4079382088)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3989562573) (.leaf 3901945350)) (.branch 25 (.leaf 3816463594) (.leaf 3733053295))) (.branch 28 (.branch 27 (.leaf 3651653093) (.leaf 3572204120)) (.branch 29 (.leaf 3494649861) (.leaf 3418936018)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3345010389) (.branch 32 (.leaf 3272822754) (.leaf 3202324771))) (.branch 35 (.branch 34 (.leaf 3133469876) (.leaf 3066213191)) (.branch 36 (.leaf 3000511442) (.leaf 2936322876)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2873607190) (.leaf 2812325460)) (.branch 40 (.leaf 2752440075) (.leaf 2693914680))) (.branch 43 (.branch 42 (.leaf 2636714113) (.leaf 2580804356)) (.branch 44 (.leaf 2526152484) (.leaf 2472726616))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2420495871) (.branch 47 (.leaf 2369430325) (.leaf 2319500974))) (.branch 50 (.branch 49 (.leaf 2270679694) (.leaf 2222939206)) (.branch 51 (.leaf 2176253041) (.leaf 2130595512)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2085941681) (.leaf 2042267331)) (.branch 55 (.leaf 1999548937) (.leaf 1957763645))) (.branch 58 (.branch 57 (.leaf 1916889244) (.leaf 1876904141)) (.branch 59 (.leaf 1837787345) (.leaf 1799518439))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1762077564) (.branch 62 (.leaf 1725445399) (.leaf 1689603143))) (.branch 65 (.branch 64 (.leaf 1654532494) (.leaf 1620215639)) (.branch 66 (.leaf 1586635232) (.leaf 1553774382)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1521616635) (.leaf 1490145964)) (.branch 70 (.leaf 1459346754) (.leaf 1429203788))) (.branch 73 (.branch 72 (.leaf 1399702236) (.leaf 1370827642)) (.branch 74 (.leaf 1342565913) (.leaf 1314903309))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1287826431) (.branch 77 (.leaf 1261322212) (.leaf 1235377906))) (.branch 80 (.branch 79 (.leaf 1209981082) (.leaf 1185119608)) (.branch 81 (.leaf 1160781649) (.leaf 1136955658)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1113630363) (.leaf 1090794764)) (.branch 85 (.leaf 1068438123) (.leaf 1046549958))) (.branch 88 (.branch 87 (.leaf 1025120037) (.leaf 1004138366)) (.branch 89 (.leaf 983595190) (.leaf 963480981)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 943786434) (.branch 92 (.leaf 924502459) (.leaf 905620182))) (.branch 95 (.branch 94 (.leaf 887130928) (.leaf 869026228)) (.branch 96 (.leaf 851297804) (.leaf 833937569)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 816937622) (.leaf 800290242)) (.branch 100 (.leaf 783987881) (.leaf 768023167))) (.branch 103 (.branch 102 (.leaf 752388890) (.leaf 737078006)) (.branch 104 (.leaf 722083629) (.leaf 707399028))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 693017620) (.leaf 678932973)) (.branch 108 (.leaf 665138797) (.leaf 651628942))) (.branch 111 (.branch 110 (.leaf 638397395) (.leaf 625438275)) (.branch 112 (.leaf 612745833) (.leaf 600314446)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 588138614) (.leaf 576212961)) (.branch 116 (.leaf 564532225) (.leaf 553091264))) (.branch 119 (.branch 118 (.leaf 541885044) (.leaf 530908643)) (.branch 120 (.leaf 520157247) (.leaf 509626146)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1303).prefactor = (4594184283953321/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1303).cutoff/(generalMeanRows 1303).c)).2 =
    (1858641158974229/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1303).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1303).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1303).q*(generalMeanRows 1303).cutoff/2-2 = (3592/225:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable433.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1303).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1303

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1303).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1303).criticalRate j.val*(generalMeanRows 1303).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1303).c*(generalMeanRows 1303).criticalPoint j.val)).2-
      (generalMeanRows 1303).J/2-(generalMeanRows 1303).error (generalMeanGrid j.val)+
      (generalMeanRows 1303).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1303).c)).2-
      (generalMeanRows 1303).J/2-(generalMeanRows 1303).error 4 := by
  have he : (generalMeanRows 1303).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1303) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1303)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1303

/-! Kernel-checked entropy margins for general spectral rectangle 1304. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1304
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5705037926) (.branch 2 (.leaf 5546228674) (.leaf 5392661901))) (.branch 5 (.branch 4 (.leaf 5244102011) (.leaf 5100329045)) (.branch 6 (.leaf 4961137232) (.leaf 4826333716)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4695737422) (.leaf 4569178049)) (.branch 10 (.leaf 4446495171) (.leaf 4327537439))) (.branch 13 (.branch 12 (.leaf 4212161859) (.leaf 4100233145)) (.branch 14 (.leaf 3991623138) (.leaf 3886210279))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3783879137) (.branch 17 (.leaf 3684519971) (.leaf 3588028344))) (.branch 20 (.branch 19 (.leaf 3494304763) (.leaf 3403254355)) (.branch 21 (.leaf 3314786566) (.leaf 3228814893)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3145256629) (.leaf 3064032638)) (.branch 25 (.leaf 2985067139) (.leaf 2908287515))) (.branch 28 (.branch 27 (.leaf 2833624129) (.leaf 2761010160)) (.branch 29 (.leaf 2690381448) (.leaf 2621676352)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2554835613) (.branch 32 (.leaf 2489802237) (.leaf 2426521374))) (.branch 35 (.branch 34 (.leaf 2364940213) (.leaf 2305007881)) (.branch 36 (.leaf 2246675351) (.leaf 2189895353)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2134622291) (.leaf 2080812168)) (.branch 40 (.leaf 2028422510) (.leaf 1977412303))) (.branch 43 (.branch 42 (.leaf 1927741925) (.leaf 1879373086)) (.branch 44 (.leaf 1832268773) (.leaf 1786393193))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1741711728) (.branch 47 (.leaf 1698190881) (.leaf 1655798231))) (.branch 50 (.branch 49 (.leaf 1614502397) (.leaf 1574272986)) (.branch 51 (.leaf 1535080564) (.leaf 1496896616)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1459693508) (.leaf 1423444458)) (.branch 55 (.leaf 1388123502) (.leaf 1353705466))) (.branch 58 (.branch 57 (.leaf 1320165932) (.leaf 1287481220)) (.branch 59 (.leaf 1255628352) (.leaf 1224585034))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1194329627) (.branch 62 (.leaf 1164841129) (.leaf 1136099150))) (.branch 65 (.branch 64 (.leaf 1108083892) (.leaf 1080776131)) (.branch 66 (.leaf 1054157192) (.leaf 1028208938)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1002913748) (.leaf 978254501)) (.branch 70 (.leaf 954214560) (.leaf 930777756))) (.branch 73 (.branch 72 (.leaf 907928372) (.leaf 885651134)) (.branch 74 (.leaf 863931189) (.leaf 842754097))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 822105819) (.branch 77 (.leaf 801972699) (.leaf 782341458))) (.branch 80 (.branch 79 (.leaf 763199180) (.leaf 744533303)) (.branch 81 (.leaf 726331602) (.leaf 708582188)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 691273491) (.leaf 674394253)) (.branch 85 (.leaf 657933521) (.leaf 641880632))) (.branch 88 (.branch 87 (.leaf 626225211) (.leaf 610957159)) (.branch 89 (.leaf 596066645) (.leaf 581544101)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 567380210) (.branch 92 (.leaf 553565904) (.leaf 540092351))) (.branch 95 (.branch 94 (.leaf 526950956) (.leaf 514133344)) (.branch 96 (.leaf 501631365) (.leaf 489437078)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 477542753) (.leaf 465940859)) (.branch 100 (.leaf 454624061) (.leaf 443585216))) (.branch 103 (.branch 102 (.leaf 432817366) (.leaf 422313732)) (.branch 104 (.leaf 412067711) (.leaf 402072870))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 392322943) (.leaf 382811822)) (.branch 108 (.leaf 373533561) (.leaf 364482362))) (.branch 111 (.branch 110 (.leaf 355652577) (.leaf 347038703)) (.branch 112 (.leaf 338635378) (.leaf 330437375)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 322439602) (.leaf 314637096)) (.branch 116 (.leaf 307025020) (.leaf 299598659))) (.branch 119 (.branch 118 (.leaf 292353420) (.leaf 285284824)) (.branch 120 (.leaf 278388506) (.leaf 271660212)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1304).prefactor = (2342900897363429/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1304).cutoff/(generalMeanRows 1304).c)).2 =
    (450664097893671/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1304).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1304).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1304).q*(generalMeanRows 1304).cutoff/2-2 = (3592/225:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable433.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1304).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1304

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1304).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1304).criticalRate j.val*(generalMeanRows 1304).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1304).c*(generalMeanRows 1304).criticalPoint j.val)).2-
      (generalMeanRows 1304).J/2-(generalMeanRows 1304).error (generalMeanGrid j.val)+
      (generalMeanRows 1304).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1304).c)).2-
      (generalMeanRows 1304).J/2-(generalMeanRows 1304).error 4 := by
  have he : (generalMeanRows 1304).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1304) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1304)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1304

/-! Kernel-checked entropy margins for general spectral rectangle 1305. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1305
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6436851521) (.branch 2 (.leaf 6270739980) (.leaf 6109856073))) (.branch 5 (.branch 4 (.leaf 5953966104) (.leaf 5802852187)) (.branch 6 (.leaf 5656310763) (.leaf 5514151287)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5376195070) (.leaf 5242274249)) (.branch 10 (.leaf 5112230867) (.leaf 4985916057))) (.branch 13 (.branch 12 (.leaf 4863189302) (.leaf 4743917783)) (.branch 14 (.leaf 4627975781) (.leaf 4515244143))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4405609801) (.branch 17 (.leaf 4298965331) (.leaf 4195208559))) (.branch 20 (.branch 19 (.leaf 4094242198) (.leaf 3995973516)) (.branch 21 (.leaf 3900314041) (.leaf 3807179284)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3716488483) (.leaf 3628164380)) (.branch 25 (.leaf 3542133000) (.leaf 3458323463))) (.branch 28 (.branch 27 (.leaf 3376667800) (.leaf 3297100785)) (.branch 29 (.leaf 3219559784) (.leaf 3143984614)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3070317406) (.branch 32 (.leaf 2998502486) (.leaf 2928486257))) (.branch 35 (.branch 34 (.leaf 2860217099) (.leaf 2793645265)) (.branch 36 (.leaf 2728722788) (.leaf 2665403399)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2603642442) (.leaf 2543396801)) (.branch 40 (.leaf 2484624828) (.leaf 2427286275))) (.branch 43 (.branch 42 (.leaf 2371342235) (.leaf 2316755079)) (.branch 44 (.leaf 2263488403) (.leaf 2211506977))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2160776692) (.branch 47 (.leaf 2111264517) (.leaf 2062938452))) (.branch 50 (.branch 49 (.leaf 2015767489) (.leaf 1969721572)) (.branch 51 (.leaf 1924771559) (.leaf 1880889186)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1838047037) (.leaf 1796218506)) (.branch 55 (.leaf 1755377774) (.leaf 1715499774))) (.branch 58 (.branch 57 (.leaf 1676560166) (.leaf 1638535313)) (.branch 59 (.leaf 1601402252) (.leaf 1565138672))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1529722894) (.branch 62 (.leaf 1495133845) (.leaf 1461351040))) (.branch 65 (.branch 64 (.leaf 1428354560) (.leaf 1396125037)) (.branch 66 (.leaf 1364643631) (.leaf 1333892017)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1303852366) (.leaf 1274507329)) (.branch 70 (.leaf 1245840021) (.leaf 1217834010))) (.branch 73 (.branch 72 (.leaf 1190473300) (.leaf 1163742316)) (.branch 74 (.leaf 1137625894) (.leaf 1112109268))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1087178055) (.branch 77 (.leaf 1062818249) (.leaf 1039016203))) (.branch 80 (.branch 79 (.leaf 1015758625) (.leaf 993032561)) (.branch 81 (.leaf 970825391) (.leaf 949124817)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 927918851) (.leaf 907195809)) (.branch 85 (.leaf 886944305) (.leaf 867153235))) (.branch 88 (.branch 87 (.leaf 847811777) (.leaf 828909377)) (.branch 89 (.leaf 810435746) (.leaf 792380849)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 774734900) (.branch 92 (.leaf 757488357) (.leaf 740631910))) (.branch 95 (.branch 94 (.leaf 724156481) (.leaf 708053212)) (.branch 96 (.leaf 692313463) (.leaf 676928805)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 661891014) (.leaf 647192065)) (.branch 100 (.leaf 632824129) (.leaf 618779565))) (.branch 103 (.branch 102 (.leaf 605050917) (.leaf 591630909)) (.branch 104 (.leaf 578512439) (.leaf 565688576))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 553152555) (.leaf 540897773)) (.branch 108 (.leaf 528917783) (.leaf 517206292))) (.branch 111 (.branch 110 (.leaf 505757159) (.leaf 494564386)) (.branch 112 (.leaf 483622118) (.leaf 472924639)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 462466367) (.leaf 452241853)) (.branch 116 (.leaf 442245774) (.leaf 432472935))) (.branch 119 (.branch 118 (.leaf 422918262) (.leaf 413576798)) (.branch 120 (.leaf 404443705) (.leaf 395514257)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1305).prefactor = (1206666280654373/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1305).cutoff/(generalMeanRows 1305).c)).2 =
    (183212445383159/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1305).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1305).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1305).q*(generalMeanRows 1305).cutoff/2-2 = (3592/225:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable433.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1305).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1305

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1305).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1305).criticalRate j.val*(generalMeanRows 1305).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1305).c*(generalMeanRows 1305).criticalPoint j.val)).2-
      (generalMeanRows 1305).J/2-(generalMeanRows 1305).error (generalMeanGrid j.val)+
      (generalMeanRows 1305).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1305).c)).2-
      (generalMeanRows 1305).J/2-(generalMeanRows 1305).error 4 := by
  have he : (generalMeanRows 1305).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1305) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1305)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1305

/-! Kernel-checked entropy margins for general spectral rectangle 1306. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1306
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7604257819) (.branch 2 (.leaf 7431210740) (.leaf 7263238171))) (.branch 5 (.branch 4 (.leaf 7100112333) (.leaf 6941621383)) (.branch 6 (.leaf 6787567884) (.leaf 6637767460)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6492047607) (.leaf 6350246634)) (.branch 10 (.leaf 6212212723) (.leaf 6077803091))) (.branch 13 (.branch 12 (.leaf 5946883242) (.leaf 5819326289)) (.branch 14 (.leaf 5695012358) (.leaf 5573828038))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5455665891) (.branch 17 (.leaf 5340424012) (.leaf 5228005620))) (.branch 20 (.branch 19 (.leaf 5118318699) (.leaf 5011275661)) (.branch 21 (.leaf 4906793049) (.leaf 4804791254)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4705194264) (.leaf 4607929439)) (.branch 25 (.leaf 4512927287) (.leaf 4420121280))) (.branch 28 (.branch 27 (.leaf 4329447669) (.leaf 4240845318)) (.branch 29 (.leaf 4154255553) (.leaf 4069622022)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3986890563) (.branch 32 (.leaf 3906009081) (.leaf 3826927441))) (.branch 35 (.branch 34 (.leaf 3749597360) (.leaf 3673972309)) (.branch 36 (.leaf 3600007429) (.leaf 3527659437)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3456886558) (.leaf 3387648444)) (.branch 40 (.leaf 3319906111) (.leaf 3253621868))) (.branch 43 (.branch 42 (.leaf 3188759263) (.leaf 3125283026)) (.branch 44 (.leaf 3063159012) (.leaf 3002354155))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2942836418) (.branch 47 (.leaf 2884574752) (.leaf 2827539052))) (.branch 50 (.branch 49 (.leaf 2771700119) (.leaf 2717029624)) (.branch 51 (.leaf 2663500069) (.leaf 2611084757)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2559757761) (.leaf 2509493894)) (.branch 55 (.leaf 2460268677) (.leaf 2412058319))) (.branch 58 (.branch 57 (.leaf 2364839686) (.leaf 2318590278)) (.branch 59 (.leaf 2273288210) (.leaf 2228912185))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2185441476) (.branch 62 (.leaf 2142855904) (.leaf 2101135824))) (.branch 65 (.branch 64 (.leaf 2060262100) (.leaf 2020216095)) (.branch 66 (.leaf 1980979648) (.leaf 1942535063)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1904865092) (.leaf 1867952922)) (.branch 70 (.leaf 1831782158) (.leaf 1796336814))) (.branch 73 (.branch 72 (.leaf 1761601298) (.leaf 1727560398)) (.branch 74 (.leaf 1694199277) (.leaf 1661503454))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1629458797) (.branch 77 (.leaf 1598051515) (.leaf 1567268143))) (.branch 80 (.branch 79 (.leaf 1537095535) (.leaf 1507520857)) (.branch 81 (.leaf 1478531573) (.leaf 1450115443)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1422260508) (.leaf 1394955087)) (.branch 85 (.leaf 1368187768) (.leaf 1341947400))) (.branch 88 (.branch 87 (.leaf 1316223086) (.leaf 1291004177)) (.branch 89 (.leaf 1266280264) (.leaf 1242041173)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1218276960) (.branch 92 (.leaf 1194977899) (.leaf 1172134486))) (.branch 95 (.branch 94 (.leaf 1149737422) (.leaf 1127777619)) (.branch 96 (.leaf 1106246186) (.leaf 1085134428)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1064433840) (.leaf 1044136104)) (.branch 100 (.leaf 1024233080) (.leaf 1004716808))) (.branch 103 (.branch 102 (.leaf 985579497) (.leaf 966813525)) (.branch 104 (.leaf 948411435) (.leaf 930365929))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 912669863) (.leaf 895316248)) (.branch 108 (.leaf 878298243) (.leaf 861609151))) (.branch 111 (.branch 110 (.leaf 845242417) (.leaf 829191626)) (.branch 112 (.leaf 813450495) (.leaf 798012875)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 782872747) (.leaf 768024215)) (.branch 116 (.leaf 753461507) (.leaf 739178973))) (.branch 119 (.branch 118 (.leaf 725171078) (.leaf 711432403)) (.branch 120 (.leaf 697957641) (.leaf 684741594)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1306).prefactor = (4971763046424399/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1306).cutoff/(generalMeanRows 1306).c)).2 =
    (1878021610523893/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1306).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1306).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1306).q*(generalMeanRows 1306).cutoff/2-2 = (3592/225:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable433.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1306).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1306

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1306).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1306).criticalRate j.val*(generalMeanRows 1306).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1306).c*(generalMeanRows 1306).criticalPoint j.val)).2-
      (generalMeanRows 1306).J/2-(generalMeanRows 1306).error (generalMeanGrid j.val)+
      (generalMeanRows 1306).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1306).c)).2-
      (generalMeanRows 1306).J/2-(generalMeanRows 1306).error 4 := by
  have he : (generalMeanRows 1306).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1306) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1306)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1306

/-! Kernel-checked entropy margins for general spectral rectangle 1307. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1307
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8390227716) (.branch 2 (.leaf 8212103740) (.leaf 8039029475))) (.branch 5 (.branch 4 (.leaf 7870776342) (.leaf 7707132042)) (.branch 6 (.leaf 7547898990) (.leaf 7392892917)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 7241941653) (.leaf 7094884032)) (.branch 10 (.leaf 6951568925) (.leaf 6811854383))) (.branch 13 (.branch 12 (.leaf 6675606857) (.leaf 6542700515)) (.branch 14 (.leaf 6413016618) (.leaf 6286442962))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 6162873377) (.branch 17 (.leaf 6042207266) (.leaf 5924349200))) (.branch 20 (.branch 19 (.leaf 5809208539) (.leaf 5696699093)) (.branch 21 (.leaf 5586738816) (.leaf 5479249517)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 5374156608) (.leaf 5271388866)) (.branch 25 (.leaf 5170878215) (.leaf 5072559530))) (.branch 28 (.branch 27 (.leaf 4976370451) (.leaf 4882251220)) (.branch 29 (.leaf 4790144519) (.leaf 4699995332)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 4611750813) (.branch 32 (.leaf 4525360159) (.leaf 4440774502))) (.branch 35 (.branch 34 (.leaf 4357946798) (.leaf 4276831735)) (.branch 36 (.leaf 4197385637) (.leaf 4119566383)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 4043333324) (.leaf 3968647215)) (.branch 40 (.leaf 3895470140) (.leaf 3823765451))) (.branch 43 (.branch 42 (.leaf 3753497708) (.leaf 3684632621)) (.branch 44 (.leaf 3617136998) (.leaf 3550978695))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 3486126569) (.branch 47 (.leaf 3422550434) (.leaf 3360221020))) (.branch 50 (.branch 49 (.leaf 3299109935) (.leaf 3239189625)) (.branch 51 (.leaf 3180433343) (.leaf 3122815115)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 3066309708) (.leaf 3010892600)) (.branch 55 (.leaf 2956539958) (.leaf 2903228602))) (.branch 58 (.branch 57 (.leaf 2850935989) (.leaf 2799640186)) (.branch 59 (.leaf 2749319844) (.leaf 2699954184))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2651522970) (.branch 62 (.leaf 2604006493) (.leaf 2557385552))) (.branch 65 (.branch 64 (.leaf 2511641438) (.leaf 2466755914)) (.branch 66 (.leaf 2422711200) (.leaf 2379489962)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 2337075291) (.leaf 2295450692)) (.branch 70 (.leaf 2254600075) (.leaf 2214507732))) (.branch 73 (.branch 72 (.leaf 2175158337) (.leaf 2136536924)) (.branch 74 (.leaf 2098628883) (.leaf 2061419945))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 2024896174) (.branch 77 (.leaf 1989043956) (.leaf 1953849989))) (.branch 80 (.branch 79 (.leaf 1919301277) (.leaf 1885385118)) (.branch 81 (.leaf 1852089095) (.leaf 1819401072)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1787309182) (.leaf 1755801822)) (.branch 85 (.leaf 1724867645) (.leaf 1694495554))) (.branch 88 (.branch 87 (.leaf 1664674691) (.leaf 1635394438)) (.branch 89 (.leaf 1606644404) (.leaf 1578414422)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1550694543) (.branch 92 (.leaf 1523475029) (.leaf 1496746351))) (.branch 95 (.branch 94 (.leaf 1470499179) (.leaf 1444724380)) (.branch 96 (.leaf 1419413013) (.leaf 1394556323)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1370145736) (.leaf 1346172857)) (.branch 100 (.leaf 1322629464) (.leaf 1299507502))) (.branch 103 (.branch 102 (.leaf 1276799084) (.leaf 1254496481)) (.branch 104 (.leaf 1232592123) (.leaf 1211078593))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1189948622) (.leaf 1169195091)) (.branch 108 (.leaf 1148811020) (.leaf 1128789571))) (.branch 111 (.branch 110 (.leaf 1109124041) (.leaf 1089807862)) (.branch 112 (.leaf 1070834594) (.leaf 1052197927)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1033891672) (.leaf 1015909766)) (.branch 116 (.leaf 998246261) (.leaf 980895327))) (.branch 119 (.branch 118 (.leaf 963851248) (.leaf 947108418)) (.branch 120 (.leaf 930661343) (.leaf 914504632)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1307).prefactor = (1024244573088859/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1307).cutoff/(generalMeanRows 1307).c)).2 =
    (1901785104976077/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1307).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1307).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1307).q*(generalMeanRows 1307).c/2-2 = (5457/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable434.value]
    have hcontinuation : (generalMeanRows 1307).q*(generalMeanRows 1307).cutoff/2-2 = (3592/225:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable433.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1307).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1307

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1307).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1307).criticalRate j.val*(generalMeanRows 1307).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1307).c*(generalMeanRows 1307).criticalPoint j.val)).2-
      (generalMeanRows 1307).J/2-(generalMeanRows 1307).error (generalMeanGrid j.val)+
      (generalMeanRows 1307).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1307).c)).2-
      (generalMeanRows 1307).J/2-(generalMeanRows 1307).error 4 := by
  have he : (generalMeanRows 1307).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1307) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1307)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1307

/-! Kernel-checked entropy margins for general spectral rectangle 1308. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1308
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8515406308) (.branch 2 (.leaf 8334624799) (.leaf 8158968340))) (.branch 5 (.branch 4 (.leaf 7988204943) (.leaf 7822119141)) (.branch 6 (.leaf 7660510399) (.leaf 7503191703)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 7349988311) (.leaf 7200736653)) (.branch 10 (.leaf 7055283347) (.leaf 6913484323))) (.branch 13 (.branch 12 (.leaf 6775204042) (.leaf 6640314795)) (.branch 14 (.leaf 6508696070) (.leaf 6380233990))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 6254820800) (.branch 17 (.leaf 6132354402) (.leaf 6012737945))) (.branch 20 (.branch 19 (.leaf 5895879434) (.leaf 5781691396)) (.branch 21 (.leaf 5670090558) (.leaf 5560997565)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 5454336715) (.leaf 5350035722)) (.branch 25 (.leaf 5248025496) (.leaf 5148239938))) (.branch 28 (.branch 27 (.leaf 5050615760) (.leaf 4955092310)) (.branch 29 (.leaf 4861611416) (.leaf 4770117243)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 4680556153) (.branch 32 (.leaf 4592876588) (.leaf 4507028949))) (.branch 35 (.branch 34 (.leaf 4422965492) (.leaf 4340640227)) (.branch 36 (.leaf 4260008827) (.leaf 4181028543)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 4103658120) (.leaf 4027857726)) (.branch 40 (.leaf 3953588880) (.leaf 3880814388))) (.branch 43 (.branch 42 (.leaf 3809498281) (.leaf 3739605757)) (.branch 44 (.leaf 3671103128) (.leaf 3603957772))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 3538138080) (.branch 47 (.leaf 3473613416) (.leaf 3410354074))) (.branch 50 (.branch 49 (.leaf 3348331237) (.leaf 3287516942)) (.branch 51 (.leaf 3227884042) (.leaf 3169406175)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 3112057731) (.leaf 3055813824)) (.branch 55 (.leaf 3000650263) (.leaf 2946543525))) (.branch 58 (.branch 57 (.leaf 2893470729) (.leaf 2841409614)) (.branch 59 (.leaf 2790338515) (.leaf 2740236340))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2691082553) (.branch 62 (.leaf 2642857151) (.leaf 2595540646))) (.branch 65 (.branch 64 (.leaf 2549114049) (.leaf 2503558852)) (.branch 66 (.leaf 2458857010) (.leaf 2414990930)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 2371943450) (.leaf 2329697830)) (.branch 70 (.leaf 2288237739) (.leaf 2247547236))) (.branch 73 (.branch 72 (.leaf 2207610765) (.leaf 2168413137)) (.branch 74 (.leaf 2129939524) (.leaf 2092175445))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 2055106755) (.branch 77 (.leaf 2018719637) (.leaf 1983000592))) (.branch 80 (.branch 79 (.leaf 1947936428) (.leaf 1913514254)) (.branch 81 (.leaf 1879721468) (.leaf 1846545754)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1813975067) (.leaf 1781997631)) (.branch 85 (.leaf 1750601929) (.leaf 1719776699))) (.branch 88 (.branch 87 (.leaf 1689510922) (.leaf 1659793820)) (.branch 89 (.leaf 1630614848) (.leaf 1601963687)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1573830239) (.branch 92 (.leaf 1546204622) (.leaf 1519077163))) (.branch 95 (.branch 94 (.leaf 1492438395) (.leaf 1466279047)) (.branch 96 (.leaf 1440590045) (.leaf 1415362504)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1390587722) (.leaf 1366257178)) (.branch 100 (.leaf 1342362527) (.leaf 1318895596))) (.branch 103 (.branch 102 (.leaf 1295848377) (.leaf 1273213029)) (.branch 104 (.leaf 1250981868) (.leaf 1229147365))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1207702144) (.leaf 1186638979)) (.branch 108 (.leaf 1165950786) (.leaf 1145630626))) (.branch 111 (.branch 110 (.leaf 1125671695) (.leaf 1106067327)) (.branch 112 (.leaf 1086810986) (.leaf 1067896268)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1049316892) (.leaf 1031066703)) (.branch 116 (.leaf 1013139666) (.leaf 995529863))) (.branch 119 (.branch 118 (.leaf 978231494) (.leaf 961238869)) (.branch 120 (.leaf 944546410) (.leaf 928148648)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1308).prefactor = (1299407327491997/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1308).cutoff/(generalMeanRows 1308).c)).2 =
    (1901785104976077/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1308).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1308).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1308).q*(generalMeanRows 1308).c/2-2 = (5457/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable434.value]
    have hcontinuation : (generalMeanRows 1308).q*(generalMeanRows 1308).cutoff/2-2 = (3592/225:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable433.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1308).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1308

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1308).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1308).criticalRate j.val*(generalMeanRows 1308).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1308).c*(generalMeanRows 1308).criticalPoint j.val)).2-
      (generalMeanRows 1308).J/2-(generalMeanRows 1308).error (generalMeanGrid j.val)+
      (generalMeanRows 1308).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1308).c)).2-
      (generalMeanRows 1308).J/2-(generalMeanRows 1308).error 4 := by
  have he : (generalMeanRows 1308).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1308) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1308)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1308

/-! Kernel-checked entropy margins for general spectral rectangle 1309. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1309
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6348042662) (.branch 2 (.leaf 6191104180) (.leaf 6038980824))) (.branch 5 (.branch 4 (.leaf 5891457420) (.leaf 5748333517)) (.branch 6 (.leaf 5609421989) (.leaf 5474547813)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5343546977) (.leaf 5216265519)) (.branch 10 (.leaf 5092558665) (.leaf 4972290060))) (.branch 13 (.branch 12 (.leaf 4855331083) (.leaf 4741560232)) (.branch 14 (.leaf 4630862567) (.leaf 4523129212))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4418256902) (.branch 17 (.leaf 4316147577) (.leaf 4216708009))) (.branch 20 (.branch 19 (.leaf 4119849466) (.leaf 4025487407)) (.branch 21 (.leaf 3933541198) (.leaf 3843933863)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3756591842) (.leaf 3671444783)) (.branch 25 (.leaf 3588425342) (.leaf 3507468999))) (.branch 28 (.branch 27 (.leaf 3428513898) (.leaf 3351500686)) (.branch 29 (.leaf 3276372375) (.leaf 3203074207)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3131553533) (.branch 32 (.leaf 3061759703) (.leaf 2993643954))) (.branch 35 (.branch 34 (.leaf 2927159318) (.leaf 2862260530)) (.branch 36 (.leaf 2798903938) (.leaf 2737047429)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2676650355) (.leaf 2617673459)) (.branch 40 (.leaf 2560078813) (.leaf 2503829757))) (.branch 43 (.branch 42 (.leaf 2448890842) (.leaf 2395227773)) (.branch 44 (.leaf 2342807363) (.leaf 2291597483))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2241567016) (.branch 47 (.leaf 2192685817) (.leaf 2144924673))) (.branch 50 (.branch 49 (.leaf 2098255261) (.leaf 2052650118)) (.branch 51 (.leaf 2008082603) (.leaf 1964526867)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1921957823) (.leaf 1880351114)) (.branch 55 (.leaf 1839683090) (.leaf 1799930778))) (.branch 58 (.branch 57 (.leaf 1761071859) (.leaf 1723084647)) (.branch 59 (.leaf 1685948059) (.leaf 1649641604))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1614145354) (.branch 62 (.leaf 1579439927) (.leaf 1545506472))) (.branch 65 (.branch 64 (.leaf 1512326645) (.leaf 1479882598)) (.branch 66 (.leaf 1448156958) (.leaf 1417132815)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1386793704) (.leaf 1357123595)) (.branch 70 (.leaf 1328106872) (.leaf 1299728329))) (.branch 73 (.branch 72 (.leaf 1271973151) (.leaf 1244826904)) (.branch 74 (.leaf 1218275522) (.leaf 1192305297))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1166902871) (.branch 77 (.leaf 1142055220) (.leaf 1117749647))) (.branch 80 (.branch 79 (.leaf 1093973773) (.leaf 1070715528)) (.branch 81 (.leaf 1047963138) (.leaf 1025705124)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1003930285) (.leaf 982627697)) (.branch 85 (.leaf 961786702) (.leaf 941396901))) (.branch 88 (.branch 87 (.leaf 921448146) (.leaf 901930535)) (.branch 89 (.leaf 882834405) (.leaf 864150324)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 845869084) (.branch 92 (.leaf 827981700) (.leaf 810479398))) (.branch 95 (.branch 94 (.leaf 793353612) (.leaf 776595979)) (.branch 96 (.leaf 760198334) (.leaf 744152703)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 728451297) (.leaf 713086513)) (.branch 100 (.leaf 698050923) (.leaf 683337272))) (.branch 103 (.branch 102 (.leaf 668938473) (.leaf 654847604)) (.branch 104 (.leaf 641057902) (.leaf 627562762))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 614355728) (.leaf 601430495)) (.branch 108 (.leaf 588780899) (.leaf 576400921))) (.branch 111 (.branch 110 (.leaf 564284676) (.leaf 552426415)) (.branch 112 (.leaf 540820520) (.leaf 529461497)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 518343981) (.leaf 507462726)) (.branch 116 (.leaf 496812604) (.leaf 486388604))) (.branch 119 (.branch 118 (.leaf 476185826) (.leaf 466199482)) (.branch 120 (.leaf 456424891) (.leaf 446857475)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1309).prefactor = (1107121461720833/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1309).cutoff/(generalMeanRows 1309).c)).2 =
    (1108447755588379/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1309).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1309).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1309).q*(generalMeanRows 1309).c/2-2 = (3319/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable299.value]
    have hcontinuation : (generalMeanRows 1309).q*(generalMeanRows 1309).cutoff/2-2 = (911/38:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable435.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1309).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1309

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1309).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1309).criticalRate j.val*(generalMeanRows 1309).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1309).c*(generalMeanRows 1309).criticalPoint j.val)).2-
      (generalMeanRows 1309).J/2-(generalMeanRows 1309).error (generalMeanGrid j.val)+
      (generalMeanRows 1309).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1309).c)).2-
      (generalMeanRows 1309).J/2-(generalMeanRows 1309).error 4 := by
  have he : (generalMeanRows 1309).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1309) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1309)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1309

/-! Kernel-checked entropy margins for general spectral rectangle 1310. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1310
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6339041696) (.branch 2 (.leaf 6180752642) (.leaf 6027348372))) (.branch 5 (.branch 4 (.leaf 5878610619) (.leaf 5734336008)) (.branch 6 (.leaf 5594334651) (.leaf 5458428907)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5326452281) (.leaf 5198248453)) (.branch 10 (.leaf 5073670405) (.leaf 4952579650))) (.branch 13 (.branch 12 (.leaf 4834845535) (.leaf 4720344616)) (.branch 14 (.leaf 4608960104) (.leaf 4500581355))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4395103413) (.branch 17 (.leaf 4292426601) (.leaf 4192456144))) (.branch 20 (.branch 19 (.leaf 4095101827) (.leaf 4000277688)) (.branch 21 (.leaf 3907901730) (.leaf 3817895669)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3730184690) (.leaf 3644697237)) (.branch 25 (.leaf 3561364806) (.leaf 3480121766))) (.branch 28 (.branch 27 (.leaf 3400905191) (.leaf 3323654700)) (.branch 29 (.leaf 3248312313) (.leaf 3174822322)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3103131161) (.branch 32 (.leaf 3033187297) (.leaf 2964941119))) (.branch 35 (.branch 34 (.leaf 2898344840) (.leaf 2833352405)) (.branch 36 (.leaf 2769919406) (.leaf 2708002998)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2647561826) (.leaf 2588555955)) (.branch 40 (.leaf 2530946801) (.leaf 2474697074))) (.branch 43 (.branch 42 (.leaf 2419770714) (.leaf 2366132842)) (.branch 44 (.leaf 2313749704) (.leaf 2262588625))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2212617962) (.branch 47 (.leaf 2163807064) (.leaf 2116126226))) (.branch 50 (.branch 49 (.leaf 2069546655) (.leaf 2024040434)) (.branch 51 (.leaf 1979580481) (.leaf 1936140526)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1893695073) (.leaf 1852219372)) (.branch 55 (.leaf 1811689393) (.leaf 1772081798))) (.branch 58 (.branch 57 (.leaf 1733373917) (.leaf 1695543720)) (.branch 59 (.leaf 1658569801) (.leaf 1622431351))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1587108137) (.branch 62 (.leaf 1552580485) (.leaf 1518829261))) (.branch 65 (.branch 64 (.leaf 1485835849) (.leaf 1453582138)) (.branch 66 (.leaf 1422050504) (.leaf 1391223792)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1361085303) (.leaf 1331618781)) (.branch 70 (.leaf 1302808396) (.leaf 1274638729))) (.branch 73 (.branch 72 (.leaf 1247094766) (.leaf 1220161878)) (.branch 74 (.leaf 1193825814) (.leaf 1168072688))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1142888969) (.branch 77 (.leaf 1118261467) (.leaf 1094177326))) (.branch 80 (.branch 79 (.leaf 1070624016) (.leaf 1047589318)) (.branch 81 (.leaf 1025061320) (.leaf 1003028404)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 981479243) (.leaf 960402787)) (.branch 85 (.leaf 939788258) (.leaf 919625143))) (.branch 88 (.branch 87 (.leaf 899903184) (.leaf 880612376)) (.branch 89 (.leaf 861742953) (.leaf 843285387)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 825230380) (.branch 92 (.leaf 807568857) (.leaf 790291960))) (.branch 95 (.branch 94 (.leaf 773391044) (.leaf 756857668)) (.branch 96 (.leaf 740683594) (.leaf 724860777)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 709381364) (.leaf 694237687)) (.branch 100 (.leaf 679422258) (.leaf 664927764))) (.branch 103 (.branch 102 (.leaf 650747065) (.leaf 636873186)) (.branch 104 (.leaf 623299317) (.leaf 610018803))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 597025147) (.leaf 584312001)) (.branch 108 (.leaf 571873163) (.leaf 559702576))) (.branch 111 (.branch 110 (.leaf 547794320) (.leaf 536142614)) (.branch 112 (.leaf 524741807) (.leaf 513586380)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 502670939) (.leaf 491990211)) (.branch 116 (.leaf 481539048) (.leaf 471312415))) (.branch 119 (.branch 118 (.leaf 461305393) (.leaf 451513175)) (.branch 120 (.leaf 441931061) (.leaf 432554460)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1310).prefactor = (2235887868205651/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1310).cutoff/(generalMeanRows 1310).c)).2 =
    (1106595901619637/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1310).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1310).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1310).q*(generalMeanRows 1310).cutoff/2-2 = (911/38:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable435.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1310).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1310

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1310).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1310).criticalRate j.val*(generalMeanRows 1310).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1310).c*(generalMeanRows 1310).criticalPoint j.val)).2-
      (generalMeanRows 1310).J/2-(generalMeanRows 1310).error (generalMeanGrid j.val)+
      (generalMeanRows 1310).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1310).c)).2-
      (generalMeanRows 1310).J/2-(generalMeanRows 1310).error 4 := by
  have he : (generalMeanRows 1310).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1310) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1310)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1310

/-! Kernel-checked entropy margins for general spectral rectangle 1311. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1311
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5531677526) (.branch 2 (.leaf 5374350159) (.leaf 5222290657))) (.branch 5 (.branch 4 (.leaf 5075261674) (.leaf 4933041533)) (.branch 6 (.leaf 4795422785) (.leaf 4662210935)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4533223311) (.leaf 4408288063)) (.branch 10 (.leaf 4287243263) (.leaf 4169936104))) (.branch 13 (.branch 12 (.leaf 4056222183) (.leaf 3945964853)) (.branch 14 (.leaf 3839034643) (.leaf 3735308728))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3634670456) (.branch 17 (.leaf 3537008915) (.leaf 3442218540))) (.branch 20 (.branch 19 (.leaf 3350198756) (.leaf 3260853651)) (.branch 21 (.leaf 3174091675) (.leaf 3089825372)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3007971122) (.leaf 2928448917)) (.branch 25 (.leaf 2851182143) (.leaf 2776097385))) (.branch 28 (.branch 27 (.leaf 2703124250) (.leaf 2632195194)) (.branch 29 (.leaf 2563245368) (.leaf 2496212476)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2431036640) (.branch 32 (.leaf 2367660274) (.leaf 2306027969))) (.branch 35 (.branch 34 (.leaf 2246086386) (.leaf 2187784151)) (.branch 36 (.leaf 2131071765) (.leaf 2075901511)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2022227373) (.leaf 1970004960)) (.branch 40 (.leaf 1919191427) (.leaf 1869745413))) (.branch 43 (.branch 42 (.leaf 1821626971) (.leaf 1774797507)) (.branch 44 (.leaf 1729219727) (.leaf 1684857576))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1641676192) (.branch 47 (.leaf 1599641854) (.leaf 1558721936))) (.branch 50 (.branch 49 (.leaf 1518884866) (.leaf 1480100081)) (.branch 51 (.leaf 1442337989) (.leaf 1405569934)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1369768155) (.leaf 1334905757)) (.branch 55 (.leaf 1300956679) (.leaf 1267895658))) (.branch 58 (.branch 57 (.leaf 1235698205) (.leaf 1204340575)) (.branch 59 (.leaf 1173799742) (.leaf 1144053371))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1115079795) (.branch 62 (.leaf 1086857990) (.leaf 1059367559))) (.branch 65 (.branch 64 (.leaf 1032588701) (.leaf 1006502200)) (.branch 66 (.leaf 981089397) (.leaf 956332179)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 932212957) (.leaf 908714646)) (.branch 70 (.leaf 885820655) (.leaf 863514867))) (.branch 73 (.branch 72 (.leaf 841781624) (.leaf 820605711)) (.branch 74 (.leaf 799972348) (.leaf 779867166))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 760276206) (.branch 77 (.leaf 741185895) (.leaf 722583042))) (.branch 80 (.branch 79 (.leaf 704454824) (.leaf 686788771)) (.branch 81 (.leaf 669572761) (.leaf 652795006)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 636444042) (.leaf 620508721)) (.branch 85 (.leaf 604978199) (.leaf 589841930))) (.branch 88 (.branch 87 (.leaf 575089653) (.leaf 560711390)) (.branch 89 (.leaf 546697429) (.leaf 533038326)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 519724888) (.branch 92 (.leaf 506748172) (.leaf 494099476))) (.branch 95 (.branch 94 (.leaf 481770329) (.leaf 469752491)) (.branch 96 (.leaf 458037939) (.leaf 446618866)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 435487673) (.leaf 424636962)) (.branch 100 (.leaf 414059534) (.leaf 403748379))) (.branch 103 (.branch 102 (.leaf 393696672) (.leaf 383897770)) (.branch 104 (.leaf 374345206) (.leaf 365032680))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 355954062) (.leaf 347103381)) (.branch 108 (.leaf 338474822) (.leaf 330062724))) (.branch 111 (.branch 110 (.leaf 321861574) (.leaf 313866002)) (.branch 112 (.leaf 306070779) (.leaf 298470812)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 291061142) (.leaf 283836937)) (.branch 116 (.leaf 276793492) (.leaf 269926223))) (.branch 119 (.branch 118 (.leaf 263230667) (.leaf 256702474)) (.branch 120 (.leaf 250337408) (.leaf 244131343)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1311).prefactor = (4559629170369321/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1311).cutoff/(generalMeanRows 1311).c)).2 =
    (1081365323979713/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1311).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1311).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1311).q*(generalMeanRows 1311).cutoff/2-2 = (911/38:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable435.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1311).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1311

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1311).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1311).criticalRate j.val*(generalMeanRows 1311).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1311).c*(generalMeanRows 1311).criticalPoint j.val)).2-
      (generalMeanRows 1311).J/2-(generalMeanRows 1311).error (generalMeanGrid j.val)+
      (generalMeanRows 1311).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1311).c)).2-
      (generalMeanRows 1311).J/2-(generalMeanRows 1311).error 4 := by
  have he : (generalMeanRows 1311).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1311) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1311)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1311

/-! Kernel-checked entropy margins for general spectral rectangle 1312. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1312
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6294562375) (.branch 2 (.leaf 6129576860) (.leaf 5969833126))) (.branch 5 (.branch 4 (.leaf 5815096718) (.leaf 5665148973)) (.branch 6 (.leaf 5519785547) (.leaf 5378815106)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5242058175) (.leaf 5109346107)) (.branch 10 (.leaf 4980520172) (.leaf 4855430735))) (.branch 13 (.branch 12 (.leaf 4733936529) (.leaf 4615903995)) (.branch 14 (.leaf 4501206688) (.leaf 4389724751))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4281344422) (.branch 17 (.leaf 4175957606) (.leaf 4073461474))) (.branch 20 (.branch 19 (.leaf 3973758101) (.leaf 3876754142)) (.branch 21 (.leaf 3782360523) (.leaf 3690492177)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3601067784) (.leaf 3514009542)) (.branch 25 (.leaf 3429242957) (.leaf 3346696644))) (.branch 28 (.branch 27 (.leaf 3266302150) (.leaf 3187993783)) (.branch 29 (.leaf 3111708461) (.leaf 3037385569)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2964966826) (.branch 32 (.leaf 2894396161) (.leaf 2825619600))) (.branch 35 (.branch 34 (.leaf 2758585158) (.leaf 2693242741)) (.branch 36 (.leaf 2629544052) (.leaf 2567442504)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2506893142) (.leaf 2447852563)) (.branch 40 (.leaf 2390278845) (.leaf 2334131482))) (.branch 43 (.branch 42 (.leaf 2279371322) (.leaf 2225960503)) (.branch 44 (.leaf 2173862403) (.leaf 2123041581))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2073463734) (.branch 47 (.leaf 2025095647) (.leaf 1977905146))) (.branch 50 (.branch 49 (.leaf 1931861062) (.leaf 1886933187)) (.branch 51 (.leaf 1843092237) (.leaf 1800309816)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1758558386) (.leaf 1717811229)) (.branch 55 (.leaf 1678042419) (.leaf 1639226795))) (.branch 58 (.branch 57 (.leaf 1601339930) (.leaf 1564358107)) (.branch 59 (.leaf 1528258290) (.leaf 1493018106))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1458615817) (.branch 62 (.leaf 1425030300) (.leaf 1392241026))) (.branch 65 (.branch 64 (.leaf 1360228040) (.leaf 1328971942)) (.branch 66 (.leaf 1298453867) (.leaf 1268655470)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1239558907) (.leaf 1211146822)) (.branch 70 (.leaf 1183402326) (.leaf 1156308987))) (.branch 73 (.branch 72 (.leaf 1129850815) (.leaf 1104012244)) (.branch 74 (.leaf 1078778127) (.leaf 1054133713))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1030064645) (.branch 77 (.leaf 1006556939) (.leaf 983596981))) (.branch 80 (.branch 79 (.leaf 961171509) (.leaf 939267607)) (.branch 81 (.leaf 917872694) (.leaf 896974513)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 876561123) (.leaf 856620886)) (.branch 85 (.leaf 837142466) (.leaf 818114813))) (.branch 88 (.branch 87 (.leaf 799527158) (.leaf 781369006)) (.branch 89 (.leaf 763630124) (.leaf 746300541)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 729370533) (.branch 92 (.leaf 712830621) (.leaf 696671563))) (.branch 95 (.branch 94 (.leaf 680884346) (.leaf 665460184)) (.branch 96 (.leaf 650390505) (.leaf 635666953)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 621281375) (.leaf 607225821)) (.branch 100 (.leaf 593492536) (.leaf 580073956))) (.branch 103 (.branch 102 (.leaf 566962700) (.leaf 554151570)) (.branch 104 (.leaf 541633541) (.leaf 529401762))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 517449546) (.leaf 505770369)) (.branch 108 (.leaf 494357865) (.leaf 483205823))) (.branch 111 (.branch 110 (.leaf 472308181) (.leaf 461659022)) (.branch 112 (.leaf 451252573) (.leaf 441083198)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 431145399) (.leaf 421433807)) (.branch 116 (.leaf 411943183) (.leaf 402668411))) (.branch 119 (.branch 118 (.leaf 393604500) (.leaf 384746575)) (.branch 120 (.leaf 376089880) (.leaf 367629769)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1312).prefactor = (1173664029315713/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1312).cutoff/(generalMeanRows 1312).c)).2 =
    (54871906823321/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1312).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1312).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1312).q*(generalMeanRows 1312).cutoff/2-2 = (911/38:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable435.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1312).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1312

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1312).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1312).criticalRate j.val*(generalMeanRows 1312).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1312).c*(generalMeanRows 1312).criticalPoint j.val)).2-
      (generalMeanRows 1312).J/2-(generalMeanRows 1312).error (generalMeanGrid j.val)+
      (generalMeanRows 1312).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1312).c)).2-
      (generalMeanRows 1312).J/2-(generalMeanRows 1312).error 4 := by
  have he : (generalMeanRows 1312).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1312) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1312)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1312

/-! Kernel-checked entropy margins for general spectral rectangle 1313. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1313
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7408699275) (.branch 2 (.leaf 7236575232) (.leaf 7069553530))) (.branch 5 (.branch 4 (.leaf 6907405542) (.leaf 6749918542)) (.branch 6 (.leaf 6596894191) (.leaf 6448147191)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6303504110) (.leaf 6162802319)) (.branch 10 (.leaf 6025889064) (.leaf 5892620629))) (.branch 13 (.branch 12 (.leaf 5762861586) (.leaf 5636484128)) (.branch 14 (.leaf 5513367468) (.leaf 5393397294))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5276465282) (.branch 17 (.leaf 5162468651) (.leaf 5051309764))) (.branch 20 (.branch 19 (.leaf 4942895761) (.leaf 4837138230)) (.branch 21 (.leaf 4733952903) (.leaf 4633259381)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4534980882) (.leaf 4439044008)) (.branch 25 (.leaf 4345378534) (.leaf 4253917213))) (.branch 28 (.branch 27 (.leaf 4164595596) (.leaf 4077351869)) (.branch 29 (.leaf 3992126695) (.leaf 3908863078)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3827506230) (.branch 32 (.leaf 3748003452) (.leaf 3670304016))) (.branch 35 (.branch 34 (.leaf 3594359069) (.leaf 3520121528)) (.branch 36 (.leaf 3447545995) (.leaf 3376588670)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3307207271) (.leaf 3239360965)) (.branch 40 (.leaf 3173010295) (.leaf 3108117117))) (.branch 43 (.branch 42 (.leaf 3044644538) (.leaf 2982556863)) (.branch 44 (.leaf 2921819536) (.leaf 2862399097))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2804263128) (.branch 47 (.leaf 2747380211) (.leaf 2691719890))) (.branch 50 (.branch 49 (.leaf 2637252624) (.leaf 2583949756)) (.branch 51 (.leaf 2531783473) (.leaf 2480726778)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2430753452) (.leaf 2381838029)) (.branch 55 (.leaf 2333955765) (.leaf 2287082610))) (.branch 58 (.branch 57 (.leaf 2241195187) (.leaf 2196270763)) (.branch 59 (.leaf 2152287226) (.leaf 2109223066))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2067057352) (.branch 62 (.leaf 2025769711) (.leaf 1985340312))) (.branch 65 (.branch 64 (.leaf 1945749844) (.leaf 1906979500)) (.branch 66 (.leaf 1869010962) (.leaf 1831826382)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1795408370) (.leaf 1759739978)) (.branch 70 (.leaf 1724804684) (.leaf 1690586381))) (.branch 73 (.branch 72 (.leaf 1657069364) (.leaf 1624238318)) (.branch 74 (.leaf 1592078304) (.leaf 1560574749))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1529713437) (.branch 77 (.leaf 1499480493) (.leaf 1469862380))) (.branch 80 (.branch 79 (.leaf 1440845885) (.leaf 1412418108)) (.branch 81 (.leaf 1384566459) (.leaf 1357278643)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1330542656) (.leaf 1304346774)) (.branch 85 (.leaf 1278679547) (.leaf 1253529791))) (.branch 88 (.branch 87 (.leaf 1228886581) (.leaf 1204739244)) (.branch 89 (.leaf 1181077351) (.leaf 1157890713)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1135169371) (.branch 92 (.leaf 1112903594) (.leaf 1091083869))) (.branch 95 (.branch 94 (.leaf 1069700901) (.leaf 1048745599)) (.branch 96 (.leaf 1028209079) (.leaf 1008082655)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 988357833) (.leaf 969026308)) (.branch 100 (.leaf 950079958) (.leaf 931510843))) (.branch 103 (.branch 102 (.leaf 913311192) (.leaf 895473411)) (.branch 104 (.leaf 877990067) (.leaf 860853891))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 844057773) (.leaf 827594755)) (.branch 108 (.leaf 811458033) (.leaf 795640947))) (.branch 111 (.branch 110 (.leaf 780136981) (.leaf 764939760)) (.branch 112 (.leaf 750043046) (.leaf 735440733)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 721126847) (.leaf 707095539)) (.branch 116 (.leaf 693341088) (.leaf 679857892))) (.branch 119 (.branch 118 (.leaf 666640467) (.leaf 653683447)) (.branch 120 (.leaf 640981578) (.leaf 628529717)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1313).prefactor = (4833681695559543/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1313).cutoff/(generalMeanRows 1313).c)).2 =
    (1119705266772197/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1313).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1313).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1313).q*(generalMeanRows 1313).c/2-2 = (3067/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable378.value]
    have hcontinuation : (generalMeanRows 1313).q*(generalMeanRows 1313).cutoff/2-2 = (911/38:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable435.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1313).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1313

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1313).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1313).criticalRate j.val*(generalMeanRows 1313).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1313).c*(generalMeanRows 1313).criticalPoint j.val)).2-
      (generalMeanRows 1313).J/2-(generalMeanRows 1313).error (generalMeanGrid j.val)+
      (generalMeanRows 1313).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1313).c)).2-
      (generalMeanRows 1313).J/2-(generalMeanRows 1313).error 4 := by
  have he : (generalMeanRows 1313).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1313) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1313)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1313

/-! Kernel-checked entropy margins for general spectral rectangle 1314. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1314
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8436221673) (.branch 2 (.leaf 8259094045) (.leaf 8086962672))) (.branch 5 (.branch 4 (.leaf 7919601017) (.leaf 7756798726)) (.branch 6 (.leaf 7598360058) (.leaf 7444102509)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 7293855586) (.leaf 7147459732)) (.branch 10 (.leaf 7004765355) (.leaf 6865631977))) (.branch 13 (.branch 12 (.leaf 6729927463) (.leaf 6597527338)) (.branch 14 (.leaf 6468314164) (.leaf 6342176991))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 6219010851) (.branch 17 (.leaf 6098716312) (.leaf 5981199059))) (.branch 20 (.branch 19 (.leaf 5866369532) (.leaf 5754142581)) (.branch 21 (.leaf 5644437161) (.leaf 5537176052)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 5432285601) (.leaf 5329695489)) (.branch 25 (.leaf 5229338514) (.leaf 5131150396))) (.branch 28 (.branch 27 (.leaf 5035069594) (.leaf 4941037139)) (.branch 29 (.leaf 4848996480) (.leaf 4758893343)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 4670675598) (.branch 32 (.leaf 4584293140) (.leaf 4499697772))) (.branch 35 (.branch 34 (.leaf 4416843105) (.leaf 4335684458)) (.branch 36 (.leaf 4256178769) (.leaf 4178284511)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 4101961613) (.leaf 4027171387)) (.branch 40 (.leaf 3953876460) (.leaf 3882040710))) (.branch 43 (.branch 42 (.leaf 3811629207) (.leaf 3742608155)) (.branch 44 (.leaf 3674944843) (.leaf 3608607591))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 3543565708) (.branch 47 (.leaf 3479789448) (.leaf 3417249965))) (.branch 50 (.branch 49 (.leaf 3355919278) (.leaf 3295770237)) (.branch 51 (.leaf 3236776481) (.leaf 3178912414)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 3122153168) (.leaf 3066474577)) (.branch 55 (.leaf 3011853151) (.leaf 2958266046))) (.branch 58 (.branch 57 (.leaf 2905691042) (.leaf 2854106520)) (.branch 59 (.leaf 2803491438) (.leaf 2753825311))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2705088191) (.branch 62 (.leaf 2657260649) (.leaf 2610323753))) (.branch 65 (.branch 64 (.leaf 2564259056) (.leaf 2519048575)) (.branch 66 (.leaf 2474674777) (.leaf 2431120567)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 2388369266) (.leaf 2346404608)) (.branch 70 (.leaf 2305210715) (.leaf 2264772095))) (.branch 73 (.branch 72 (.leaf 2225073623) (.leaf 2186100534)) (.branch 74 (.leaf 2147838408) (.leaf 2110273163))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 2073391042) (.branch 77 (.leaf 2037178607) (.leaf 2001622725))) (.branch 80 (.branch 79 (.leaf 1966710562) (.leaf 1932429575)) (.branch 81 (.leaf 1898767502) (.leaf 1865712353)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1833252405) (.leaf 1801376195)) (.branch 85 (.leaf 1770072509) (.leaf 1739330379))) (.branch 88 (.branch 87 (.leaf 1709139075) (.leaf 1679488097)) (.branch 89 (.leaf 1650367174) (.leaf 1621766251)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1593675487) (.branch 92 (.leaf 1566085252) (.leaf 1538986117))) (.branch 95 (.branch 94 (.leaf 1512368851) (.leaf 1486224415)) (.branch 96 (.leaf 1460543960) (.leaf 1435318818)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1410540501) (.leaf 1386200696)) (.branch 100 (.leaf 1362291258) (.leaf 1338804210))) (.branch 103 (.branch 102 (.leaf 1315731736) (.leaf 1293066179)) (.branch 104 (.leaf 1270800034) (.leaf 1248925950))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1227436721) (.leaf 1206325285)) (.branch 108 (.leaf 1185584722) (.leaf 1165208248))) (.branch 111 (.branch 110 (.leaf 1145189213) (.leaf 1125521097)) (.branch 112 (.leaf 1106197512) (.leaf 1087212191)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1068558991) (.leaf 1050231888)) (.branch 116 (.leaf 1032224978) (.leaf 1014532467))) (.branch 119 (.branch 118 (.leaf 997148675) (.leaf 980068034)) (.branch 120 (.leaf 963285078) (.leaf 946794449)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1314).prefactor = (19440719996303/3906250000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1314).cutoff/(generalMeanRows 1314).c)).2 =
    (2274163065535233/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1314).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1314).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1314).q*(generalMeanRows 1314).cutoff/2-2 = (911/38:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable435.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1314).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1314

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1314).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1314).criticalRate j.val*(generalMeanRows 1314).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1314).c*(generalMeanRows 1314).criticalPoint j.val)).2-
      (generalMeanRows 1314).J/2-(generalMeanRows 1314).error (generalMeanGrid j.val)+
      (generalMeanRows 1314).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1314).c)).2-
      (generalMeanRows 1314).J/2-(generalMeanRows 1314).error 4 := by
  have he : (generalMeanRows 1314).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1314) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1314)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1314

/-! Kernel-checked entropy margins for general spectral rectangle 1315. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1315
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8589268852) (.branch 2 (.leaf 8406792242) (.leaf 8229490358))) (.branch 5 (.branch 4 (.leaf 8057128995) (.leaf 7889490627)) (.branch 6 (.leaf 7726372795) (.leaf 7567586685)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 7412955872) (.leaf 7262315207)) (.branch 10 (.leaf 7115509825) (.leaf 6972394262))) (.branch 13 (.branch 12 (.leaf 6832831663) (.leaf 6696693077)) (.branch 14 (.leaf 6563856823) (.leaf 6434207914))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 6307637542) (.branch 17 (.leaf 6184042616) (.leaf 6063325335))) (.branch 20 (.branch 19 (.leaf 5945392805) (.leaf 5830156696)) (.branch 21 (.leaf 5717532918) (.leaf 5607441337)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 5499805507) (.leaf 5394552431)) (.branch 25 (.leaf 5291612337) (.leaf 5190918477))) (.branch 28 (.branch 27 (.leaf 5092406937) (.leaf 4996016468)) (.branch 29 (.leaf 4901688321) (.leaf 4809366110)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 4718995667) (.branch 32 (.leaf 4630524922) (.leaf 4543903786))) (.branch 35 (.branch 34 (.leaf 4459084041) (.leaf 4376019241)) (.branch 36 (.leaf 4294664620) (.leaf 4214977002)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 4136914726) (.leaf 4060437561)) (.branch 40 (.leaf 3985506646) (.leaf 3912084416))) (.branch 43 (.branch 42 (.leaf 3840134544) (.leaf 3769621882)) (.branch 44 (.leaf 3700512409) (.leaf 3632773175))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 3566372258) (.branch 47 (.leaf 3501278719) (.leaf 3437462553))) (.branch 50 (.branch 49 (.leaf 3374894659) (.leaf 3313546794)) (.branch 51 (.leaf 3253391542) (.leaf 3194402277)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 3136553136) (.leaf 3079818986)) (.branch 55 (.leaf 3024175394) (.leaf 2969598602))) (.branch 58 (.branch 57 (.leaf 2916065504) (.leaf 2863553617)) (.branch 59 (.leaf 2812041059) (.leaf 2761506532))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2711929293) (.branch 62 (.leaf 2663289141) (.leaf 2615566397))) (.branch 65 (.branch 64 (.leaf 2568741882) (.leaf 2522796904)) (.branch 66 (.leaf 2477713241) (.leaf 2433473124)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 2390059222) (.leaf 2347454631)) (.branch 70 (.leaf 2305642855) (.leaf 2264607799))) (.branch 73 (.branch 72 (.leaf 2224333751) (.leaf 2184805375)) (.branch 74 (.leaf 2146007694) (.leaf 2107926086))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 2070546266) (.branch 77 (.leaf 2033854282) (.leaf 1997836501))) (.branch 80 (.branch 79 (.leaf 1962479602) (.leaf 1927770569)) (.branch 81 (.leaf 1893696675) (.leaf 1860245483)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1827404830) (.leaf 1795162826)) (.branch 85 (.leaf 1763507842) (.leaf 1732428504))) (.branch 88 (.branch 87 (.leaf 1701913688) (.leaf 1671952508)) (.branch 89 (.leaf 1642534318) (.leaf 1613648699)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1585285455) (.branch 92 (.leaf 1557434607) (.leaf 1530086390))) (.branch 95 (.branch 94 (.leaf 1503231242) (.leaf 1476859806)) (.branch 96 (.leaf 1450962919) (.leaf 1425531609)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1400557091) (.leaf 1376030763)) (.branch 100 (.leaf 1351944198) (.leaf 1328289145))) (.branch 103 (.branch 102 (.leaf 1305057520) (.leaf 1282241406)) (.branch 104 (.leaf 1259833044) (.leaf 1237824836))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1216209334) (.leaf 1194979242)) (.branch 108 (.leaf 1174127410) (.leaf 1153646831))) (.branch 111 (.branch 110 (.leaf 1133530639) (.leaf 1113772103)) (.branch 112 (.leaf 1094364626) (.leaf 1075301741)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1056577111) (.leaf 1038184520)) (.branch 116 (.leaf 1020117877) (.leaf 1002371209))) (.branch 119 (.branch 118 (.leaf 984938660) (.leaf 967814488)) (.branch 120 (.leaf 950993061) (.leaf 934468859)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1315).prefactor = (2562102954097791/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1315).cutoff/(generalMeanRows 1315).c)).2 =
    (45404829837641/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1315).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1315).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1315).q*(generalMeanRows 1315).cutoff/2-2 = (911/38:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable435.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1315).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1315

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1315).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1315).criticalRate j.val*(generalMeanRows 1315).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1315).c*(generalMeanRows 1315).criticalPoint j.val)).2-
      (generalMeanRows 1315).J/2-(generalMeanRows 1315).error (generalMeanGrid j.val)+
      (generalMeanRows 1315).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1315).c)).2-
      (generalMeanRows 1315).J/2-(generalMeanRows 1315).error 4 := by
  have he : (generalMeanRows 1315).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1315) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1315)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1315

/-! Kernel-checked entropy margins for general spectral rectangle 1316. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1316
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6348800949) (.branch 2 (.leaf 6185036750) (.leaf 6026424852))) (.branch 5 (.branch 4 (.leaf 5872734940) (.leaf 5723752279)) (.branch 6 (.leaf 5579276253) (.leaf 5439119071)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5303104629) (.leaf 5171067492)) (.branch 10 (.leaf 5042851990) (.leaf 4918311410))) (.branch 13 (.branch 12 (.leaf 4797307270) (.leaf 4679708675)) (.branch 14 (.leaf 4565391728) (.leaf 4454239003))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4346139071) (.branch 17 (.leaf 4240986067) (.leaf 4138679299))) (.branch 20 (.branch 19 (.leaf 4039122892) (.leaf 3942225461)) (.branch 21 (.leaf 3847899818) (.leaf 3756062700)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3666634520) (.leaf 3579539140)) (.branch 25 (.leaf 3494703662) (.leaf 3412058235))) (.branch 28 (.branch 27 (.leaf 3331535876) (.leaf 3253072310)) (.branch 29 (.leaf 3176605812) (.leaf 3102077073)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3029429065) (.branch 32 (.leaf 2958606922) (.leaf 2889557829))) (.branch 35 (.branch 34 (.leaf 2822230914) (.leaf 2756577153)) (.branch 36 (.leaf 2692549275) (.leaf 2630101685)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2569190374) (.leaf 2509772853)) (.branch 40 (.leaf 2451808077) (.leaf 2395256384))) (.branch 43 (.branch 42 (.leaf 2340079430) (.leaf 2286240133)) (.branch 44 (.leaf 2233702618) (.leaf 2182432163))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2132395155) (.branch 47 (.leaf 2083559042) (.leaf 2035892287))) (.branch 50 (.branch 49 (.leaf 1989364331) (.leaf 1943945554)) (.branch 51 (.leaf 1899607234) (.leaf 1856321517)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1814061383) (.leaf 1772800612)) (.branch 55 (.leaf 1732513756) (.leaf 1693176111))) (.branch 58 (.branch 57 (.leaf 1654763689) (.leaf 1617253193)) (.branch 59 (.leaf 1580621991) (.leaf 1544848095))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1509910136) (.branch 62 (.leaf 1475787347) (.leaf 1442459536))) (.branch 65 (.branch 64 (.leaf 1409907073) (.leaf 1378110865)) (.branch 66 (.leaf 1347052346) (.leaf 1316713453)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1287076612) (.leaf 1258124724)) (.branch 70 (.leaf 1229841147) (.leaf 1202209683))) (.branch 73 (.branch 72 (.leaf 1175214565) (.leaf 1148840441)) (.branch 74 (.leaf 1123072366) (.leaf 1097895782))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1073296515) (.branch 77 (.leaf 1049260756) (.leaf 1025775055))) (.branch 80 (.branch 79 (.leaf 1002826307) (.leaf 980401746)) (.branch 81 (.leaf 958488929) (.leaf 937075734)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 916150343) (.leaf 895701241)) (.branch 85 (.leaf 875717199) (.leaf 856187275))) (.branch 88 (.branch 87 (.leaf 837100798) (.leaf 818447364)) (.branch 89 (.leaf 800216830) (.leaf 782399304)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 764985138) (.branch 92 (.leaf 747964924) (.leaf 731329485))) (.branch 95 (.branch 94 (.leaf 715069869) (.leaf 699177346)) (.branch 96 (.leaf 683643395) (.leaf 668459708)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 653618175) (.leaf 639110886)) (.branch 100 (.leaf 624930119) (.leaf 611068344))) (.branch 103 (.branch 102 (.leaf 597518207) (.leaf 584272535)) (.branch 104 (.leaf 571324325) (.leaf 558666745))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 546293122) (.leaf 534196946)) (.branch 108 (.leaf 522371862) (.leaf 510811664))) (.branch 111 (.branch 110 (.leaf 499510295) (.leaf 488461843)) (.branch 112 (.leaf 477660533) (.leaf 467100729)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 456776928) (.leaf 446683754)) (.branch 116 (.leaf 436815961) (.leaf 427168423))) (.branch 119 (.branch 118 (.leaf 417736139) (.leaf 408514220)) (.branch 120 (.leaf 399497894) (.leaf 390682501)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1316).prefactor = (4536809760579443/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1316).cutoff/(generalMeanRows 1316).c)).2 =
    (571393055111133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1316).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1316).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1316).q*(generalMeanRows 1316).cutoff/2-2 = (3700/77:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable436.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1316).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1316

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1316).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1316).criticalRate j.val*(generalMeanRows 1316).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1316).c*(generalMeanRows 1316).criticalPoint j.val)).2-
      (generalMeanRows 1316).J/2-(generalMeanRows 1316).error (generalMeanGrid j.val)+
      (generalMeanRows 1316).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1316).c)).2-
      (generalMeanRows 1316).J/2-(generalMeanRows 1316).error 4 := by
  have he : (generalMeanRows 1316).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1316) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1316)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1316

/-! Kernel-checked entropy margins for general spectral rectangle 1317. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1317
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7205040662) (.branch 2 (.leaf 7034900227) (.leaf 6869847618))) (.branch 5 (.branch 4 (.leaf 6709655101) (.leaf 6554110712)) (.branch 6 (.leaf 6403016759) (.leaf 6256188493)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6113452938) (.leaf 5974647848)) (.branch 10 (.leaf 5839620781) (.leaf 5708228274))) (.branch 13 (.branch 12 (.leaf 5580335101) (.leaf 5455813613)) (.branch 14 (.leaf 5334543136) (.leaf 5216409440))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5101304251) (.branch 17 (.leaf 4989124813) (.leaf 4879773490))) (.branch 20 (.branch 19 (.leaf 4773157403) (.leaf 4669188106)) (.branch 21 (.leaf 4567781281) (.leaf 4468856468)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4372336812) (.leaf 4278148835)) (.branch 25 (.leaf 4186222225) (.leaf 4096489642))) (.branch 28 (.branch 27 (.leaf 4008886542) (.leaf 3923351009)) (.branch 29 (.leaf 3839823604) (.leaf 3758247230)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3678566993) (.branch 32 (.leaf 3600730091) (.leaf 3524685695))) (.branch 35 (.branch 34 (.leaf 3450384848) (.leaf 3377780369)) (.branch 36 (.leaf 3306826762) (.leaf 3237480132)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3169698106) (.leaf 3103439762)) (.branch 40 (.leaf 3038665558) (.leaf 2975337266))) (.branch 43 (.branch 42 (.leaf 2913417917) (.leaf 2852871741)) (.branch 44 (.leaf 2793664113) (.leaf 2735761504))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2679131435) (.branch 47 (.leaf 2623742432) (.leaf 2569563982))) (.branch 50 (.branch 49 (.leaf 2516566497) (.leaf 2464721273)) (.branch 51 (.leaf 2414000457) (.leaf 2364377014)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2315824693) (.leaf 2268317998)) (.branch 55 (.leaf 2221832160) (.leaf 2176343112))) (.branch 58 (.branch 57 (.leaf 2131827456) (.leaf 2088262447)) (.branch 59 (.leaf 2045625966) (.leaf 2003896497))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1963053107) (.branch 62 (.leaf 1923075425) (.leaf 1883943625))) (.branch 65 (.branch 64 (.leaf 1845638405) (.leaf 1808140972)) (.branch 66 (.leaf 1771433022) (.leaf 1735496727)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1700314718) (.leaf 1665870072)) (.branch 70 (.leaf 1632146294) (.leaf 1599127310))) (.branch 73 (.branch 72 (.leaf 1566797447) (.leaf 1535141426)) (.branch 74 (.leaf 1504144346) (.leaf 1473791678))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1444069245) (.branch 77 (.leaf 1414963223) (.leaf 1386460120))) (.branch 80 (.branch 79 (.leaf 1358546773) (.leaf 1331210336)) (.branch 81 (.leaf 1304438273) (.leaf 1278218345)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1252538606) (.leaf 1227387392)) (.branch 85 (.leaf 1202753315) (.leaf 1178625255))) (.branch 88 (.branch 87 (.leaf 1154992351) (.leaf 1131843996)) (.branch 89 (.leaf 1109169829) (.leaf 1086959730)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1065203810) (.branch 92 (.leaf 1043892410) (.leaf 1023016091))) (.branch 95 (.branch 94 (.leaf 1002565629) (.leaf 982532010)) (.branch 96 (.leaf 962906425) (.leaf 943680265)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 924845113) (.leaf 906392743)) (.branch 100 (.leaf 888315113) (.leaf 870604360))) (.branch 103 (.branch 102 (.leaf 853252798) (.leaf 836252909)) (.branch 104 (.leaf 819597345) (.leaf 803278919))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 787290602) (.leaf 771625521)) (.branch 108 (.leaf 756276953) (.leaf 741238324))) (.branch 111 (.branch 110 (.leaf 726503202) (.leaf 712065295)) (.branch 112 (.leaf 697918450) (.leaf 684056646)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 670473994) (.leaf 657164730)) (.branch 116 (.leaf 644123218) (.leaf 631343940))) (.branch 119 (.branch 118 (.leaf 618821500) (.leaf 606550614)) (.branch 120 (.leaf 594526116) (.leaf 582742947)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1317).prefactor = (4668265614643833/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1317).cutoff/(generalMeanRows 1317).c)).2 =
    (115583074445777/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1317).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1317).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1317).q*(generalMeanRows 1317).cutoff/2-2 = (3700/77:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable436.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1317).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1317

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1317).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1317).criticalRate j.val*(generalMeanRows 1317).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1317).c*(generalMeanRows 1317).criticalPoint j.val)).2-
      (generalMeanRows 1317).J/2-(generalMeanRows 1317).error (generalMeanGrid j.val)+
      (generalMeanRows 1317).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1317).c)).2-
      (generalMeanRows 1317).J/2-(generalMeanRows 1317).error 4 := by
  have he : (generalMeanRows 1317).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1317) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1317)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1317

/-! Kernel-checked entropy margins for general spectral rectangle 1318. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1318
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8269059248) (.branch 2 (.leaf 8093850421) (.leaf 7923604191))) (.branch 5 (.branch 4 (.leaf 7758095863) (.leaf 7597116758)) (.branch 6 (.leaf 7440472658) (.leaf 7287982446)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 7139476896) (.leaf 6994797609)) (.branch 10 (.leaf 6853796053) (.leaf 6716332722))) (.branch 13 (.branch 12 (.leaf 6582276373) (.leaf 6451503348)) (.branch 14 (.leaf 6323896966) (.leaf 6199346970))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 6077749034) (.branch 17 (.leaf 5959004315) (.leaf 5843019050))) (.branch 20 (.branch 19 (.leaf 5729704181) (.leaf 5618975030)) (.branch 21 (.leaf 5510750987) (.leaf 5404955238)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 5301514505) (.leaf 5200358820)) (.branch 25 (.leaf 5101421310) (.leaf 5004637999))) (.branch 28 (.branch 27 (.leaf 4909947631) (.leaf 4817291506)) (.branch 29 (.leaf 4726613323) (.leaf 4637859043)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 4550976759) (.branch 32 (.leaf 4465916572) (.leaf 4382630483))) (.branch 35 (.branch 34 (.leaf 4301072290) (.leaf 4221197485)) (.branch 36 (.leaf 4142963175) (.leaf 4066327989)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3991252007) (.leaf 3917696683)) (.branch 40 (.leaf 3845624783) (.leaf 3775000313))) (.branch 43 (.branch 42 (.leaf 3705788468) (.leaf 3637955573)) (.branch 44 (.leaf 3571469031) (.leaf 3506297273))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 3442409714) (.branch 47 (.leaf 3379776711) (.leaf 3318369519))) (.branch 50 (.branch 49 (.leaf 3258160253) (.leaf 3199121855)) (.branch 51 (.leaf 3141228058) (.leaf 3084453351)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 3028772955) (.leaf 2974162789)) (.branch 55 (.leaf 2920599444) (.leaf 2868060158))) (.branch 58 (.branch 57 (.leaf 2816522789) (.leaf 2765965797)) (.branch 59 (.leaf 2716368216) (.leaf 2667709638))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2619970188) (.branch 62 (.leaf 2573130510) (.leaf 2527171746))) (.branch 65 (.branch 64 (.leaf 2482075518) (.leaf 2437823916)) (.branch 66 (.leaf 2394399477) (.leaf 2351785174)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 2309964399) (.leaf 2268920952)) (.branch 70 (.leaf 2228639025) (.leaf 2189103192))) (.branch 73 (.branch 72 (.leaf 2150298396) (.leaf 2112209937)) (.branch 74 (.leaf 2074823463) (.leaf 2038124956))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 2002100728) (.branch 77 (.leaf 1966737402) (.leaf 1932021914))) (.branch 80 (.branch 79 (.leaf 1897941493) (.leaf 1864483660)) (.branch 81 (.leaf 1831636218) (.leaf 1799387242)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1767725073) (.leaf 1736638310)) (.branch 85 (.leaf 1706115806) (.leaf 1676146654))) (.branch 88 (.branch 87 (.leaf 1646720188) (.leaf 1617825972)) (.branch 89 (.leaf 1589453796) (.leaf 1561593670)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1534235816) (.branch 92 (.leaf 1507370665) (.leaf 1480988851))) (.branch 95 (.branch 94 (.leaf 1455081205) (.leaf 1429638752)) (.branch 96 (.leaf 1404652703) (.leaf 1380114453)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1356015576) (.leaf 1332347819)) (.branch 100 (.leaf 1309103101) (.leaf 1286273504))) (.branch 103 (.branch 102 (.leaf 1263851273) (.leaf 1241828813)) (.branch 104 (.leaf 1220198680) (.leaf 1198953582))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1178086375) (.leaf 1157590057)) (.branch 108 (.leaf 1137457767) (.leaf 1117682782))) (.branch 111 (.branch 110 (.leaf 1098258510) (.leaf 1079178492)) (.branch 112 (.leaf 1060436398) (.leaf 1042026020)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1023941275) (.leaf 1006176197)) (.branch 116 (.leaf 988724938) (.leaf 971581765))) (.branch 119 (.branch 118 (.leaf 954741055) (.leaf 938197296)) (.branch 120 (.leaf 921945082) (.leaf 905979111)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1318).prefactor = (2401765226990979/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1318).cutoff/(generalMeanRows 1318).c)).2 =
    (2927104717013437/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1318).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1318).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1318).q*(generalMeanRows 1318).c/2-2 = (5443/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable437.value]
    have hcontinuation : (generalMeanRows 1318).q*(generalMeanRows 1318).cutoff/2-2 = (3700/77:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable436.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1318).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1318

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1318).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1318).criticalRate j.val*(generalMeanRows 1318).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1318).c*(generalMeanRows 1318).criticalPoint j.val)).2-
      (generalMeanRows 1318).J/2-(generalMeanRows 1318).error (generalMeanGrid j.val)+
      (generalMeanRows 1318).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1318).c)).2-
      (generalMeanRows 1318).J/2-(generalMeanRows 1318).error 4 := by
  have he : (generalMeanRows 1318).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1318) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1318)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1318

/-! Kernel-checked entropy margins for general spectral rectangle 1319. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1319
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8508658504) (.branch 2 (.leaf 8328372933) (.leaf 8153193751))) (.branch 5 (.branch 4 (.leaf 7982889754) (.leaf 7817246216)) (.branch 6 (.leaf 7656063291) (.leaf 7499154614)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 7346346058) (.leaf 7197474631)) (.branch 10 (.leaf 7052387500) (.leaf 6910941115))) (.branch 13 (.branch 12 (.leaf 6773000430) (.leaf 6638438205)) (.branch 14 (.leaf 6507134377) (.leaf 6378975496))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 6253854212) (.branch 17 (.leaf 6131668818) (.leaf 6012322834))) (.branch 20 (.branch 19 (.leaf 5895724622) (.leaf 5781787050)) (.branch 21 (.leaf 5670427173) (.leaf 5561565950)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 5455127981) (.leaf 5351041271)) (.branch 25 (.leaf 5249237007) (.leaf 5149649361))) (.branch 28 (.branch 27 (.leaf 5052215303) (.leaf 4956874429)) (.branch 29 (.leaf 4863568810) (.leaf 4772242840)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 4682843107) (.branch 32 (.leaf 4595318268) (.leaf 4509618932))) (.branch 35 (.branch 34 (.leaf 4425697557) (.leaf 4343508349)) (.branch 36 (.leaf 4263007168) (.leaf 4184151448)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 4106900109) (.leaf 4031213492)) (.branch 40 (.leaf 3957053279) (.leaf 3884382437))) (.branch 43 (.branch 42 (.leaf 3813165152) (.leaf 3743366772)) (.branch 44 (.leaf 3674953756) (.leaf 3607893620))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 3542154895) (.branch 47 (.leaf 3477707076) (.leaf 3414520586))) (.branch 50 (.branch 49 (.leaf 3352566733) (.leaf 3291817674)) (.branch 51 (.leaf 3232246381) (.leaf 3173826605)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 3116532848) (.leaf 3060340330)) (.branch 55 (.leaf 3005224966) (.leaf 2951163333))) (.branch 58 (.branch 57 (.leaf 2898132649) (.leaf 2846110748)) (.branch 59 (.leaf 2795076058) (.leaf 2745007578))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2695884859) (.branch 62 (.leaf 2647687983) (.leaf 2600397545))) (.branch 65 (.branch 64 (.leaf 2553994636) (.leaf 2508460826)) (.branch 66 (.leaf 2463778147) (.leaf 2419929078)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 2376896530) (.leaf 2334663833)) (.branch 70 (.leaf 2293214721) (.leaf 2252533321))) (.branch 73 (.branch 72 (.leaf 2212604141) (.leaf 2173412054)) (.branch 74 (.leaf 2134942292) (.leaf 2097180432))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 2060112387) (.branch 77 (.leaf 2023724395) (.leaf 1988003011))) (.branch 80 (.branch 79 (.leaf 1952935097) (.leaf 1918507810)) (.branch 81 (.leaf 1884708600) (.leaf 1851525197)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1818945604) (.leaf 1786958091)) (.branch 85 (.leaf 1755551185) (.leaf 1724713665))) (.branch 88 (.branch 87 (.leaf 1694434555) (.leaf 1664703118)) (.branch 89 (.leaf 1635508847) (.leaf 1606841463)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1578690904) (.branch 92 (.leaf 1551047325) (.leaf 1523901087))) (.branch 95 (.branch 94 (.leaf 1497242757) (.leaf 1471063099)) (.branch 96 (.leaf 1445353070) (.leaf 1420103814)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1395306663) (.leaf 1370953124)) (.branch 100 (.leaf 1347034880) (.leaf 1323543786))) (.branch 103 (.branch 102 (.leaf 1300471863) (.leaf 1277811293)) (.branch 104 (.leaf 1255554418) (.leaf 1233693735))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1212221893) (.leaf 1191131686)) (.branch 108 (.leaf 1170416055) (.leaf 1150068081))) (.branch 111 (.branch 110 (.leaf 1130080984) (.leaf 1110448115)) (.branch 112 (.leaf 1091162961) (.leaf 1072219135)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1053610377) (.leaf 1035330549)) (.branch 116 (.leaf 1017373633) (.leaf 999733730))) (.branch 119 (.branch 118 (.leaf 982405054) (.leaf 965381933)) (.branch 120 (.leaf 948658805) (.leaf 932230213)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1319).prefactor = (4942714645446017/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1319).cutoff/(generalMeanRows 1319).c)).2 =
    (2927104717013437/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1319).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1319).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1319).q*(generalMeanRows 1319).c/2-2 = (5443/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable437.value]
    have hcontinuation : (generalMeanRows 1319).q*(generalMeanRows 1319).cutoff/2-2 = (3700/77:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable436.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1319).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1319

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1319).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1319).criticalRate j.val*(generalMeanRows 1319).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1319).c*(generalMeanRows 1319).criticalPoint j.val)).2-
      (generalMeanRows 1319).J/2-(generalMeanRows 1319).error (generalMeanGrid j.val)+
      (generalMeanRows 1319).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1319).c)).2-
      (generalMeanRows 1319).J/2-(generalMeanRows 1319).error 4 := by
  have he : (generalMeanRows 1319).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1319) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1319)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1319

/-! Kernel-checked entropy margins for general spectral rectangle 1320. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1320
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8537185583) (.branch 2 (.leaf 8354223656) (.leaf 8176471239))) (.branch 5 (.branch 4 (.leaf 8003692854) (.leaf 7835669753)) (.branch 6 (.leaf 7672198304) (.leaf 7513088569)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 7358163040) (.leaf 7207255530)) (.branch 10 (.leaf 7060210171) (.leaf 6916880534))) (.branch 13 (.branch 12 (.leaf 6777128837) (.leaf 6640825232)) (.branch 14 (.leaf 6507847172) (.leaf 6378078836))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 6251410610) (.branch 17 (.leaf 6127738623) (.leaf 6006964322))) (.branch 20 (.branch 19 (.leaf 5888994084) (.leaf 5773738875)) (.branch 21 (.leaf 5661113923) (.leaf 5551038434)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 5443435324) (.leaf 5338230976)) (.branch 25 (.leaf 5235355022) (.leaf 5134740130))) (.branch 28 (.branch 27 (.leaf 5036321826) (.leaf 4940038314)) (.branch 29 (.leaf 4845830320) (.leaf 4753640942)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 4663415518) (.branch 32 (.leaf 4575101496) (.leaf 4488648320))) (.branch 35 (.branch 34 (.leaf 4404007318) (.leaf 4321131608)) (.branch 36 (.leaf 4239975996) (.leaf 4160496894)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 4082652239) (.leaf 4006401413)) (.branch 40 (.leaf 3931705176) (.leaf 3858525599))) (.branch 43 (.branch 42 (.leaf 3786826000) (.leaf 3716570887)) (.branch 44 (.leaf 3647725904) (.leaf 3580257779))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 3514134275) (.branch 47 (.leaf 3449324147) (.leaf 3385797098))) (.branch 50 (.branch 49 (.leaf 3323523737) (.leaf 3262475544)) (.branch 51 (.leaf 3202624834) (.leaf 3143944720)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 3086409086) (.leaf 3029992551)) (.branch 55 (.leaf 2974670446) (.leaf 2920418782))) (.branch 58 (.branch 57 (.leaf 2867214229) (.leaf 2815034085)) (.branch 59 (.leaf 2763856262) (.leaf 2713659254))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2664422124) (.branch 62 (.leaf 2616124479) (.leaf 2568746454))) (.branch 65 (.branch 64 (.leaf 2522268691) (.leaf 2476672326)) (.branch 66 (.leaf 2431938966) (.leaf 2388050682)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 2344989985) (.leaf 2302739817)) (.branch 70 (.leaf 2261283538) (.leaf 2220604907))) (.branch 73 (.branch 72 (.leaf 2180688076) (.leaf 2141517576)) (.branch 74 (.leaf 2103078301) (.leaf 2065355503))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 2028334778) (.branch 77 (.leaf 1992002058) (.leaf 1956343597))) (.branch 80 (.branch 79 (.leaf 1921345968) (.leaf 1886996046)) (.branch 81 (.leaf 1853281008) (.leaf 1820188316)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1787705716) (.leaf 1755821226)) (.branch 85 (.leaf 1724523129) (.leaf 1693799969))) (.branch 88 (.branch 87 (.leaf 1663640539) (.leaf 1634033878)) (.branch 89 (.leaf 1604969263) (.leaf 1576436203)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1548424434) (.branch 92 (.leaf 1520923910) (.leaf 1493924801))) (.branch 95 (.branch 94 (.leaf 1467417486) (.leaf 1441392547)) (.branch 96 (.leaf 1415840765) (.leaf 1390753115)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1366120759) (.leaf 1341935046)) (.branch 100 (.leaf 1318187502) (.leaf 1294869830))) (.branch 103 (.branch 102 (.leaf 1271973903) (.leaf 1249491763)) (.branch 104 (.leaf 1227415611) (.leaf 1205737812))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1184450882) (.leaf 1163547492)) (.branch 108 (.leaf 1143020459) (.leaf 1122862746))) (.branch 111 (.branch 110 (.leaf 1103067457) (.leaf 1083627835)) (.branch 112 (.leaf 1064537256) (.leaf 1045789230)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1027377396) (.leaf 1009295517)) (.branch 116 (.leaf 991537481) (.leaf 974097298))) (.branch 119 (.branch 118 (.leaf 956969092) (.leaf 940147106)) (.branch 120 (.leaf 923625694) (.leaf 907399320)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1320).prefactor = (1253452964945787/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1320).cutoff/(generalMeanRows 1320).c)).2 =
    (1461643959243369/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1320).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1320).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1320).q*(generalMeanRows 1320).cutoff/2-2 = (3700/77:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable436.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1320).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1320

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1320).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1320).criticalRate j.val*(generalMeanRows 1320).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1320).c*(generalMeanRows 1320).criticalPoint j.val)).2-
      (generalMeanRows 1320).J/2-(generalMeanRows 1320).error (generalMeanGrid j.val)+
      (generalMeanRows 1320).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1320).c)).2-
      (generalMeanRows 1320).J/2-(generalMeanRows 1320).error 4 := by
  have he : (generalMeanRows 1320).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1320) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1320)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1320

/-! Kernel-checked entropy margins for general spectral rectangle 1321. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1321
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7613843754) (.branch 2 (.leaf 7446276802) (.leaf 7283541907))) (.branch 5 (.branch 4 (.leaf 7125421411) (.leaf 6971713016)) (.branch 6 (.leaf 6822228305) (.leaf 6676791438)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6535238001) (.leaf 6397413986)) (.branch 10 (.leaf 6263174875) (.leaf 6132384837))) (.branch 13 (.branch 12 (.leaf 6004915997) (.leaf 5880647789)) (.branch 14 (.leaf 5759466372) (.leaf 5641264102))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5525939063) (.branch 17 (.leaf 5413394633) (.leaf 5303539098))) (.branch 20 (.branch 19 (.leaf 5196285301) (.leaf 5091550318)) (.branch 21 (.leaf 4989255169) (.leaf 4889324550)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4791686592) (.leaf 4696272634)) (.branch 25 (.leaf 4603017020) (.leaf 4511856915))) (.branch 28 (.branch 27 (.leaf 4422732127) (.leaf 4335584950)) (.branch 29 (.leaf 4250360019) (.leaf 4167004173)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 4085466328) (.branch 32 (.leaf 4005697363) (.leaf 3927650015))) (.branch 35 (.branch 34 (.leaf 3851278771) (.leaf 3776539785)) (.branch 36 (.leaf 3703390785) (.leaf 3631790994)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3561701055) (.leaf 3493082962)) (.branch 40 (.leaf 3425899995) (.leaf 3360116654))) (.branch 43 (.branch 42 (.leaf 3295698607) (.leaf 3232612635)) (.branch 44 (.leaf 3170826578) (.leaf 3110309293))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 3051030603) (.branch 47 (.leaf 2992961261) (.leaf 2936072908))) (.branch 50 (.branch 49 (.leaf 2880338033) (.leaf 2825729943)) (.branch 51 (.leaf 2772222727) (.leaf 2719791222)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2668410988) (.leaf 2618058279)) (.branch 55 (.leaf 2568710013) (.leaf 2520343749))) (.branch 58 (.branch 57 (.leaf 2472937664) (.leaf 2426470529)) (.branch 59 (.leaf 2380921687) (.leaf 2336271032))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2292498992) (.branch 62 (.leaf 2249586508) (.leaf 2207515016))) (.branch 65 (.branch 64 (.leaf 2166266432) (.leaf 2125823135)) (.branch 66 (.leaf 2086167950) (.leaf 2047284135)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 2009155369) (.leaf 1971765731)) (.branch 70 (.leaf 1935099697) (.leaf 1899142119))) (.branch 73 (.branch 72 (.leaf 1863878220) (.leaf 1829293578)) (.branch 74 (.leaf 1795374117) (.leaf 1762106096))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1729476099) (.branch 77 (.leaf 1697471027) (.leaf 1666078086))) (.branch 80 (.branch 79 (.leaf 1635284781) (.leaf 1605078904)) (.branch 81 (.leaf 1575448529) (.leaf 1546382002)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1517867936) (.leaf 1489895200)) (.branch 85 (.leaf 1462452915) (.leaf 1435530443))) (.branch 88 (.branch 87 (.leaf 1409117388) (.leaf 1383203581)) (.branch 89 (.leaf 1357779080) (.leaf 1332834161)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1308359313) (.branch 92 (.leaf 1284345233) (.leaf 1260782820))) (.branch 95 (.branch 94 (.leaf 1237663170) (.leaf 1214977572)) (.branch 96 (.leaf 1192717501) (.leaf 1170874614)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1149440748) (.leaf 1128407912)) (.branch 100 (.leaf 1107768285) (.leaf 1087514209))) (.branch 103 (.branch 102 (.leaf 1067638191) (.leaf 1048132891)) (.branch 104 (.leaf 1028991126) (.leaf 1010205861))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 991770206) (.leaf 973677417)) (.branch 108 (.leaf 955920886) (.leaf 938494144))) (.branch 111 (.branch 110 (.leaf 921390853) (.leaf 904604805)) (.branch 112 (.leaf 888129919) (.leaf 871960240)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 856089932) (.leaf 840513277)) (.branch 116 (.leaf 825224675) (.leaf 810218637))) (.branch 119 (.branch 118 (.leaf 795489785) (.leaf 781032851)) (.branch 120 (.leaf 766842669) (.leaf 752914180)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1321).prefactor = (895467245684751/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1321).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1321).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1321).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1321

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1321).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1321).criticalRate j.val*(generalMeanRows 1321).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1321).c*(generalMeanRows 1321).criticalPoint j.val)).2-
      (generalMeanRows 1321).J/2-(generalMeanRows 1321).error (generalMeanGrid j.val)+
      (generalMeanRows 1321).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1321).c)).2-
      (generalMeanRows 1321).J/2-(generalMeanRows 1321).error 4 := by
  have he : (generalMeanRows 1321).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1321) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1321)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1321

/-! Kernel-checked entropy margins for general spectral rectangle 1322. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1322
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8082545395) (.branch 2 (.leaf 7910403385) (.leaf 7743148658))) (.branch 5 (.branch 4 (.leaf 7580560102) (.leaf 7422432339)) (.branch 6 (.leaf 7268574207) (.leaf 7118807421)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6972965385) (.leaf 6830892144)) (.branch 10 (.leaf 6692441446) (.leaf 6557475911))) (.branch 13 (.branch 12 (.leaf 6425866285) (.leaf 6297490774)) (.branch 14 (.leaf 6172234442) (.leaf 6049988674))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5930650688) (.branch 17 (.leaf 5814123095) (.leaf 5700313502))) (.branch 20 (.branch 19 (.leaf 5589134148) (.leaf 5480501578)) (.branch 21 (.leaf 5374336345) (.leaf 5270562732)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 5169108508) (.leaf 5069904695)) (.branch 25 (.leaf 4972885363) (.leaf 4877987436))) (.branch 28 (.branch 27 (.leaf 4785150515) (.leaf 4694316717)) (.branch 29 (.leaf 4605430522) (.leaf 4518438639)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 4433289874) (.branch 32 (.leaf 4349935015) (.leaf 4268326719))) (.branch 35 (.branch 34 (.leaf 4188419412) (.leaf 4110169195)) (.branch 36 (.leaf 4033533754) (.leaf 3958472280)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3884945391) (.leaf 3812915062)) (.branch 40 (.leaf 3742344556) (.leaf 3673198368))) (.branch 43 (.branch 42 (.leaf 3605442156) (.leaf 3539042697)) (.branch 44 (.leaf 3473967831) (.leaf 3410186411))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 3347668262) (.branch 47 (.leaf 3286384134) (.leaf 3226305668))) (.branch 50 (.branch 49 (.leaf 3167405352) (.leaf 3109656489)) (.branch 51 (.leaf 3053033162) (.leaf 2997510204)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2943063165) (.leaf 2889668287)) (.branch 55 (.leaf 2837302475) (.leaf 2785943272))) (.branch 58 (.branch 57 (.leaf 2735568836) (.leaf 2686157915)) (.branch 59 (.leaf 2637689826) (.leaf 2590144437))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2543502142) (.branch 62 (.leaf 2497743847) (.leaf 2452850951))) (.branch 65 (.branch 64 (.leaf 2408805327) (.leaf 2365589309)) (.branch 66 (.leaf 2323185673) (.leaf 2281577627)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 2240748790) (.leaf 2200683188)) (.branch 70 (.leaf 2161365230) (.leaf 2122779706))) (.branch 73 (.branch 72 (.leaf 2084911768) (.leaf 2047746923)) (.branch 74 (.leaf 2011271020) (.leaf 1975470239))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1940331084) (.branch 77 (.leaf 1905840371) (.leaf 1871985219))) (.branch 80 (.branch 79 (.leaf 1838753042) (.leaf 1806131539)) (.branch 81 (.leaf 1774108690) (.leaf 1742672743)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1711812207) (.leaf 1681515850)) (.branch 85 (.leaf 1651772686) (.leaf 1622571970))) (.branch 88 (.branch 87 (.leaf 1593903194) (.leaf 1565756078)) (.branch 89 (.leaf 1538120563) (.leaf 1510986808)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1484345185) (.branch 92 (.leaf 1458186269) (.leaf 1432500836))) (.branch 95 (.branch 94 (.leaf 1407279858) (.leaf 1382514497)) (.branch 96 (.leaf 1358196100) (.leaf 1334316196)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1310866489) (.leaf 1287838857)) (.branch 100 (.leaf 1265225344) (.leaf 1243018158))) (.branch 103 (.branch 102 (.leaf 1221209670) (.leaf 1199792402)) (.branch 104 (.leaf 1178759033) (.leaf 1158102387))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1137815436) (.leaf 1117891293)) (.branch 108 (.leaf 1098323208) (.leaf 1079104568))) (.branch 111 (.branch 110 (.leaf 1060228893) (.leaf 1041689830)) (.branch 112 (.leaf 1023481154) (.leaf 1005596763)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 988030674) (.leaf 970777025)) (.branch 116 (.leaf 953830067) (.leaf 937184165))) (.branch 119 (.branch 118 (.leaf 920833793) (.leaf 904773535)) (.branch 120 (.leaf 888998078) (.leaf 873502213)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1322).prefactor = (2301662948226827/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1322).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1322).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue]
    have hfirst : (generalMeanRows 1322).q*(generalMeanRows 1322).c/2-2 = (137/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable438.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1322).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1322

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1322).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1322).criticalRate j.val*(generalMeanRows 1322).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1322).c*(generalMeanRows 1322).criticalPoint j.val)).2-
      (generalMeanRows 1322).J/2-(generalMeanRows 1322).error (generalMeanGrid j.val)+
      (generalMeanRows 1322).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1322).c)).2-
      (generalMeanRows 1322).J/2-(generalMeanRows 1322).error 4 := by
  have he : (generalMeanRows 1322).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1322) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1322)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1322

/-! Kernel-checked entropy margins for general spectral rectangle 1323. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1323
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8399125927) (.branch 2 (.leaf 8222230201) (.leaf 8050331154))) (.branch 5 (.branch 4 (.leaf 7883202341) (.leaf 7720633478)) (.branch 6 (.leaf 7562428880) (.leaf 7408406082)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 7258394619) (.leaf 7112234950)) (.branch 10 (.leaf 6969777488) (.leaf 6830881754))) (.branch 13 (.branch 12 (.leaf 6695415604) (.leaf 6563254544)) (.branch 14 (.leaf 6434281117) (.leaf 6308384344))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 6185459228) (.branch 17 (.leaf 6065406301) (.leaf 5948131213))) (.branch 20 (.branch 19 (.leaf 5833544361) (.leaf 5721560554)) (.branch 21 (.leaf 5612098703) (.leaf 5505081542)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 5400435372) (.leaf 5298089825)) (.branch 25 (.leaf 5197977653) (.leaf 5100034526))) (.branch 28 (.branch 27 (.leaf 5004198853) (.leaf 4910411617)) (.branch 29 (.leaf 4818616218) (.leaf 4728758332)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 4640785783) (.branch 32 (.leaf 4554648414) (.leaf 4470297983))) (.branch 35 (.branch 34 (.leaf 4387688052) (.leaf 4306773895)) (.branch 36 (.leaf 4227512404) (.leaf 4149862006)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 4073782586) (.leaf 3999235413)) (.branch 40 (.leaf 3926183070) (.leaf 3854589395))) (.branch 43 (.branch 42 (.leaf 3784419416) (.leaf 3715639299)) (.branch 44 (.leaf 3648216291) (.leaf 3582118676))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 3517315727) (.branch 47 (.leaf 3453777660) (.leaf 3391475595))) (.branch 50 (.branch 49 (.leaf 3330381518) (.leaf 3270468244)) (.branch 51 (.leaf 3211709382) (.leaf 3154079303)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 3097553111) (.leaf 3042106610)) (.branch 55 (.leaf 2987716282) (.leaf 2934359256))) (.branch 58 (.branch 57 (.leaf 2882013287) (.leaf 2830656728)) (.branch 59 (.leaf 2780268516) (.leaf 2730828140))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2682315632) (.branch 62 (.leaf 2634711539) (.leaf 2587996911))) (.branch 65 (.branch 64 (.leaf 2542153278) (.leaf 2497162640)) (.branch 66 (.leaf 2453007447) (.leaf 2409670584)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 2367135358) (.leaf 2325385484)) (.branch 70 (.leaf 2284405073) (.leaf 2244178616))) (.branch 73 (.branch 72 (.leaf 2204690975) (.leaf 2165927373)) (.branch 74 (.leaf 2127873378) (.leaf 2090514896))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 2053838160) (.branch 77 (.leaf 2017829721) (.leaf 1982476438))) (.branch 80 (.branch 79 (.leaf 1947765467) (.leaf 1913684258)) (.branch 81 (.leaf 1880220539) (.leaf 1847362317)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1815097860) (.leaf 1783415700)) (.branch 85 (.leaf 1752304617) (.leaf 1721753639))) (.branch 88 (.branch 87 (.leaf 1691752032) (.leaf 1662289293)) (.branch 89 (.leaf 1633355145) (.leaf 1604939532)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1577032612) (.branch 92 (.leaf 1549624752) (.leaf 1522706520))) (.branch 95 (.branch 94 (.leaf 1496268686) (.leaf 1470302210)) (.branch 96 (.leaf 1444798243) (.leaf 1419748117)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1395143345) (.leaf 1370975613)) (.branch 100 (.leaf 1347236781) (.leaf 1323918870))) (.branch 103 (.branch 102 (.leaf 1301014068) (.leaf 1278514719)) (.branch 104 (.leaf 1256413322) (.leaf 1234702529))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1213375136) (.leaf 1192424085)) (.branch 108 (.leaf 1171842460) (.leaf 1151623481))) (.branch 111 (.branch 110 (.leaf 1131760501) (.leaf 1112247008)) (.branch 112 (.leaf 1093076614) (.leaf 1074243061)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1055740208) (.leaf 1037562040)) (.branch 116 (.leaf 1019702655) (.leaf 1002156267))) (.branch 119 (.branch 118 (.leaf 984917202) (.leaf 967979897)) (.branch 120 (.leaf 951338893) (.leaf 934988839)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1323).prefactor = (2366430420663429/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1323).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1323).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1323).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1323

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1323).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1323).criticalRate j.val*(generalMeanRows 1323).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1323).c*(generalMeanRows 1323).criticalPoint j.val)).2-
      (generalMeanRows 1323).J/2-(generalMeanRows 1323).error (generalMeanGrid j.val)+
      (generalMeanRows 1323).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1323).c)).2-
      (generalMeanRows 1323).J/2-(generalMeanRows 1323).error 4 := by
  have he : (generalMeanRows 1323).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1323) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1323)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1323

/-! Kernel-checked entropy margins for general spectral rectangle 1324. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1324
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8543821738) (.branch 2 (.leaf 8361855467) (.leaf 8185055400))) (.branch 5 (.branch 4 (.leaf 8013187805) (.leaf 7846035583)) (.branch 6 (.leaf 7683396663) (.leaf 7525082585)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 7370917245) (.leaf 7220735788)) (.branch 10 (.leaf 7074383614) (.leaf 6931715505))) (.branch 13 (.branch 12 (.leaf 6792594829) (.leaf 6656892840)) (.branch 14 (.leaf 6524488045) (.leaf 6395265628))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 6269116942) (.branch 17 (.leaf 6145939041) (.leaf 6025634256))) (.branch 20 (.branch 19 (.leaf 5908109821) (.leaf 5793277518)) (.branch 21 (.leaf 5681053363) (.leaf 5571357320)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 5464113034) (.leaf 5359247592)) (.branch 25 (.leaf 5256691301) (.leaf 5156377485))) (.branch 28 (.branch 27 (.leaf 5058242298) (.leaf 4962224553)) (.branch 29 (.leaf 4868265563) (.leaf 4776308994)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 4686300732) (.branch 32 (.leaf 4598188754) (.leaf 4511923017))) (.branch 35 (.branch 34 (.leaf 4427455346) (.leaf 4344739336)) (.branch 36 (.leaf 4263730259) (.leaf 4184384976)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 4106661857) (.leaf 4030520708)) (.branch 40 (.leaf 3955922697) (.leaf 3882830288))) (.branch 43 (.branch 42 (.leaf 3811207183) (.leaf 3741018263)) (.branch 44 (.leaf 3672229530) (.leaf 3604808061))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 3538721958) (.branch 47 (.leaf 3473940304) (.leaf 3410433119))) (.branch 50 (.branch 49 (.leaf 3348171322) (.leaf 3287126692)) (.branch 51 (.leaf 3227271834) (.leaf 3168580142)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 3111025774) (.leaf 3054583614)) (.branch 55 (.leaf 2999229250) (.leaf 2944938943))) (.branch 58 (.branch 57 (.leaf 2891689603) (.leaf 2839458767)) (.branch 59 (.leaf 2788224572) (.leaf 2737965735))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2688661533) (.branch 62 (.leaf 2640291781) (.leaf 2592836817))) (.branch 65 (.branch 64 (.leaf 2546277479) (.leaf 2500595094)) (.branch 66 (.leaf 2455771454) (.leaf 2411788808)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 2368629842) (.leaf 2326277669)) (.branch 70 (.leaf 2284715809) (.leaf 2243928182))) (.branch 73 (.branch 72 (.leaf 2203899096) (.leaf 2164613228)) (.branch 74 (.leaf 2126055620) (.leaf 2088211665))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 2051067094) (.branch 77 (.leaf 2014607973) (.leaf 1978820684))) (.branch 80 (.branch 79 (.leaf 1943691924) (.leaf 1909208690)) (.branch 81 (.leaf 1875358276) (.leaf 1842128257)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1809506490) (.leaf 1777481099)) (.branch 85 (.leaf 1746040472) (.leaf 1715173252))) (.branch 88 (.branch 87 (.leaf 1684868330) (.leaf 1655114838)) (.branch 89 (.leaf 1625902146) (.leaf 1597219850)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1569057771) (.branch 92 (.leaf 1541405948) (.leaf 1514254630))) (.branch 95 (.branch 94 (.leaf 1487594273) (.leaf 1461415536)) (.branch 96 (.leaf 1435709272) (.leaf 1410466525)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1385678528) (.leaf 1361336693)) (.branch 100 (.leaf 1337432611) (.leaf 1313958047))) (.branch 103 (.branch 102 (.leaf 1290904933) (.leaf 1268265368)) (.branch 104 (.leaf 1246031610) (.leaf 1224196075))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1202751334) (.leaf 1181690106)) (.branch 108 (.leaf 1161005258) (.leaf 1140689797))) (.branch 111 (.branch 110 (.leaf 1120736875) (.leaf 1101139775)) (.branch 112 (.leaf 1081891917) (.leaf 1062986851)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1044418254) (.leaf 1026179928)) (.branch 116 (.leaf 1008265795) (.leaf 990669900))) (.branch 119 (.branch 118 (.leaf 973386402) (.leaf 956409574)) (.branch 120 (.leaf 939733801) (.leaf 923353577)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1324).prefactor = (4866040825096007/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1324).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1324).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue]
    have hfirst : (generalMeanRows 1324).q*(generalMeanRows 1324).c/2-2 = (137/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable438.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1324).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1324

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1324).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1324).criticalRate j.val*(generalMeanRows 1324).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1324).c*(generalMeanRows 1324).criticalPoint j.val)).2-
      (generalMeanRows 1324).J/2-(generalMeanRows 1324).error (generalMeanGrid j.val)+
      (generalMeanRows 1324).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1324).c)).2-
      (generalMeanRows 1324).J/2-(generalMeanRows 1324).error 4 := by
  have he : (generalMeanRows 1324).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1324) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1324)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1324

/-! Kernel-checked entropy margins for general spectral rectangle 1325. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1325
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8263043194) (.branch 2 (.leaf 8090652353) (.leaf 7923110356))) (.branch 5 (.branch 4 (.leaf 7760197127) (.leaf 7601708335)) (.branch 6 (.leaf 7447453867) (.leaf 7297256490)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 7150950653) (.leaf 7008381443)) (.branch 10 (.leaf 6869403642) (.leaf 6733880894))) (.branch 13 (.branch 12 (.leaf 6601684956) (.leaf 6472695034)) (.branch 14 (.leaf 6346797176) (.leaf 6223883738))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 6103852890) (.branch 17 (.leaf 5986608183) (.leaf 5872058142))) (.branch 20 (.branch 19 (.leaf 5760115913) (.leaf 5650698925)) (.branch 21 (.leaf 5543728597) (.leaf 5439130065)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 5336831928) (.leaf 5236766023)) (.branch 25 (.leaf 5138867215) (.leaf 5043073206))) (.branch 28 (.branch 27 (.leaf 4949324356) (.leaf 4857563524)) (.branch 29 (.leaf 4767735915) (.leaf 4679788943)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 4593672106) (.branch 32 (.leaf 4509336863) (.leaf 4426736525))) (.branch 35 (.branch 34 (.leaf 4345826159) (.leaf 4266562487)) (.branch 36 (.leaf 4188903802) (.leaf 4112809883)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 4038241925) (.leaf 3965162461)) (.branch 40 (.leaf 3893535298) (.leaf 3823325459))) (.branch 43 (.branch 42 (.leaf 3754499118) (.leaf 3687023552)) (.branch 44 (.leaf 3620867086) (.leaf 3555999047))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 3492389716) (.branch 47 (.leaf 3430010292) (.leaf 3368832846))) (.branch 50 (.branch 49 (.leaf 3308830287) (.leaf 3249976324)) (.branch 51 (.leaf 3192245438) (.leaf 3135612842)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 3080054460) (.leaf 3025546894)) (.branch 55 (.leaf 2972067398) (.leaf 2919593852))) (.branch 58 (.branch 57 (.leaf 2868104743) (.leaf 2817579135)) (.branch 59 (.leaf 2767996653) (.leaf 2719337460))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2671582240) (.branch 62 (.leaf 2624712174) (.leaf 2578708931))) (.branch 65 (.branch 64 (.leaf 2533554644) (.leaf 2489231895)) (.branch 66 (.leaf 2445723704) (.leaf 2403013511)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 2361085163) (.leaf 2319922899)) (.branch 70 (.leaf 2279511340) (.leaf 2239835478))) (.branch 73 (.branch 72 (.leaf 2200880658) (.leaf 2162632574)) (.branch 74 (.leaf 2125077255) (.leaf 2088201055))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 2051990643) (.branch 77 (.leaf 2016432995) (.leaf 1981515384))) (.branch 80 (.branch 79 (.leaf 1947225370) (.leaf 1913550794)) (.branch 81 (.leaf 1880479770) (.leaf 1848000675)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1816102144) (.leaf 1784773061)) (.branch 85 (.leaf 1754002553) (.leaf 1723779984))) (.branch 88 (.branch 87 (.leaf 1694094947) (.leaf 1664937261)) (.branch 89 (.leaf 1636296959) (.leaf 1608164290)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1580529708) (.branch 92 (.leaf 1553383868) (.leaf 1526717621))) (.branch 95 (.branch 94 (.leaf 1500522011) (.leaf 1474788265)) (.branch 96 (.leaf 1449507795) (.leaf 1424672187)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1400273203) (.leaf 1376302771)) (.branch 100 (.leaf 1352752985) (.leaf 1329616097))) (.branch 103 (.branch 102 (.leaf 1306884518) (.leaf 1284550812)) (.branch 104 (.leaf 1262607690) (.leaf 1241048010))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1219864774) (.leaf 1199051119)) (.branch 108 (.leaf 1178600322) (.leaf 1158505791))) (.branch 111 (.branch 110 (.leaf 1138761061) (.leaf 1119359799)) (.branch 112 (.leaf 1100295791) (.leaf 1081562947)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1063155294) (.leaf 1045066975)) (.branch 116 (.leaf 1027292247) (.leaf 1009825477))) (.branch 119 (.branch 118 (.leaf 992661141) (.leaf 975793818)) (.branch 120 (.leaf 959218195) (.leaf 942929058)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1325).prefactor = (449937424974203/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1325).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1325).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1325).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1325

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1325).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1325).criticalRate j.val*(generalMeanRows 1325).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1325).c*(generalMeanRows 1325).criticalPoint j.val)).2-
      (generalMeanRows 1325).J/2-(generalMeanRows 1325).error (generalMeanGrid j.val)+
      (generalMeanRows 1325).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1325).c)).2-
      (generalMeanRows 1325).J/2-(generalMeanRows 1325).error 4 := by
  have he : (generalMeanRows 1325).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1325) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1325)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1325

/-! Kernel-checked entropy margins for general spectral rectangle 1326. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1326
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8399187412) (.branch 2 (.leaf 8222016913) (.leaf 8049854354))) (.branch 5 (.branch 4 (.leaf 7882472833) (.leaf 7719661637)) (.branch 6 (.leaf 7561224675) (.leaf 7406979097)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 7256754076) (.leaf 7110389723)) (.branch 10 (.leaf 6967736126) (.leaf 6828652492))) (.branch 13 (.branch 12 (.leaf 6693006379) (.leaf 6560673011)) (.branch 14 (.leaf 6431534660) (.leaf 6305480087))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 6182404048) (.branch 17 (.leaf 6062206836) (.leaf 5944793875))) (.branch 20 (.branch 19 (.leaf 5830075343) (.leaf 5717965839)) (.branch 21 (.leaf 5608384073) (.leaf 5501252586)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 5396497491) (.leaf 5294048241)) (.branch 25 (.leaf 5193837415) (.leaf 5095800516))) (.branch 28 (.branch 27 (.leaf 4999875793) (.leaf 4906004073)) (.branch 29 (.leaf 4814128607) (.leaf 4724194927)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 4636150714) (.branch 32 (.leaf 4549945679) (.leaf 4465531449))) (.branch 35 (.branch 34 (.leaf 4382861459) (.leaf 4301890862)) (.branch 36 (.leaf 4222576429) (.leaf 4144876476)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 4068750774) (.leaf 3994160486)) (.branch 40 (.leaf 3921068092) (.leaf 3849437328))) (.branch 43 (.branch 42 (.leaf 3779233124) (.leaf 3710421551)) (.branch 44 (.leaf 3642969766) (.leaf 3576845963))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 3512019328) (.branch 47 (.leaf 3448459993) (.leaf 3386138999))) (.branch 50 (.branch 49 (.leaf 3325028251) (.leaf 3265100487)) (.branch 51 (.leaf 3206329244) (.leaf 3148688820)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 3092154248) (.leaf 3036701265)) (.branch 55 (.leaf 2982306287) (.leaf 2928946378))) (.branch 58 (.branch 57 (.leaf 2876599232) (.leaf 2825243142)) (.branch 59 (.leaf 2774856984) (.leaf 2725420194))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2676912744) (.branch 62 (.leaf 2629315131) (.leaf 2582608351))) (.branch 65 (.branch 64 (.leaf 2536773885) (.leaf 2491793682)) (.branch 66 (.leaf 2447650144) (.leaf 2404326111)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 2361804845) (.leaf 2320070017)) (.branch 70 (.leaf 2279105694) (.leaf 2238896328))) (.branch 73 (.branch 72 (.leaf 2199426740) (.leaf 2160682112)) (.branch 74 (.leaf 2122647977) (.leaf 2085310203))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 2048654988) (.branch 77 (.leaf 2012668848) (.leaf 1977338607))) (.branch 80 (.branch 79 (.leaf 1942651391) (.leaf 1908594616)) (.branch 81 (.leaf 1875155981) (.leaf 1842323461)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1810085297) (.leaf 1778429991)) (.branch 85 (.leaf 1747346299) (.leaf 1716823219))) (.branch 88 (.branch 87 (.leaf 1686849992) (.leaf 1657416090)) (.branch 89 (.leaf 1628511214) (.leaf 1600125282)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1572248429) (.branch 92 (.leaf 1544871001) (.leaf 1517983545))) (.branch 95 (.branch 94 (.leaf 1491576809) (.leaf 1465641735)) (.branch 96 (.leaf 1440169451) (.leaf 1415151272)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1390578693) (.leaf 1366443382)) (.branch 100 (.leaf 1342737180) (.leaf 1319452094))) (.branch 103 (.branch 102 (.leaf 1296580294) (.leaf 1274114108)) (.branch 104 (.leaf 1252046022) (.leaf 1230368671))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1209074838) (.leaf 1188157452)) (.branch 108 (.leaf 1167609581) (.leaf 1147424434))) (.branch 111 (.branch 110 (.leaf 1127595352) (.leaf 1108115809)) (.branch 112 (.leaf 1088979408) (.leaf 1070179876)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1051711066) (.leaf 1033566948)) (.branch 116 (.leaf 1015741612) (.leaf 998229262))) (.branch 119 (.branch 118 (.leaf 981024214) (.leaf 964120896)) (.branch 120 (.leaf 947513841) (.leaf 931197689)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1326).prefactor = (231067462668131/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1326).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1326).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue]
    have hfirst : (generalMeanRows 1326).q*(generalMeanRows 1326).c/2-2 = (5411/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable439.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1326).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1326

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1326).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1326).criticalRate j.val*(generalMeanRows 1326).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1326).c*(generalMeanRows 1326).criticalPoint j.val)).2-
      (generalMeanRows 1326).J/2-(generalMeanRows 1326).error (generalMeanGrid j.val)+
      (generalMeanRows 1326).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1326).c)).2-
      (generalMeanRows 1326).J/2-(generalMeanRows 1326).error 4 := by
  have he : (generalMeanRows 1326).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1326) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1326)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1326

/-! Kernel-checked entropy margins for general spectral rectangle 1327. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1327
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8512274265) (.branch 2 (.leaf 8332718339) (.leaf 8158237779))) (.branch 5 (.branch 4 (.leaf 7988602629) (.leaf 7823599339)) (.branch 6 (.leaf 7663029178) (.leaf 7506706834)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 7354459180) (.leaf 7206124174)) (.branch 10 (.leaf 7061549886) (.leaf 6920593626))) (.branch 13 (.branch 12 (.leaf 6783121171) (.leaf 6649006064)) (.branch 14 (.leaf 6518128991) (.leaf 6390377216))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 6265644079) (.branch 17 (.leaf 6143828529) (.leaf 6024834717))) (.branch 20 (.branch 19 (.leaf 5908571612) (.leaf 5794952663)) (.branch 21 (.leaf 5683895486) (.leaf 5575321578)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 5469156057) (.leaf 5365327429)) (.branch 25 (.leaf 5263767362) (.leaf 5164410492))) (.branch 28 (.branch 27 (.leaf 5067194236) (.leaf 4972058625)) (.branch 29 (.leaf 4878946146) (.leaf 4787801596)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 4698571954) (.branch 32 (.leaf 4611206253) (.leaf 4525655467))) (.branch 35 (.branch 34 (.leaf 4441872407) (.leaf 4359811619)) (.branch 36 (.leaf 4279429296) (.leaf 4200683188)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 4123532528) (.leaf 4047937955)) (.branch 40 (.leaf 3973861443) (.leaf 3901266241))) (.branch 43 (.branch 42 (.leaf 3830116806) (.leaf 3760378752)) (.branch 44 (.leaf 3692018795) (.leaf 3625004700))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 3559305237) (.branch 47 (.leaf 3494890138) (.leaf 3431730052))) (.branch 50 (.branch 49 (.leaf 3369796508) (.leaf 3309061876)) (.branch 51 (.leaf 3249499335) (.leaf 3191082839)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 3133787084) (.leaf 3077587481)) (.branch 55 (.leaf 3022460127) (.leaf 2968381780))) (.branch 58 (.branch 57 (.leaf 2915329830) (.leaf 2863282281)) (.branch 59 (.leaf 2812217723) (.leaf 2762115314))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2712954759) (.branch 62 (.leaf 2664716291) (.leaf 2617380649))) (.branch 65 (.branch 64 (.leaf 2570929067) (.leaf 2525343249)) (.branch 66 (.leaf 2480605362) (.leaf 2436698014)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 2393604240) (.leaf 2351307493)) (.branch 70 (.leaf 2309791626) (.leaf 2269040879))) (.branch 73 (.branch 72 (.leaf 2229039872) (.leaf 2189773586)) (.branch 74 (.leaf 2151227358) (.leaf 2113386868))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 2076238126) (.branch 77 (.leaf 2039767467) (.leaf 2003961540))) (.branch 80 (.branch 79 (.leaf 1968807294) (.leaf 1934291978)) (.branch 81 (.leaf 1900403124) (.leaf 1867128546)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1834456327) (.leaf 1802374814)) (.branch 85 (.leaf 1770872609) (.leaf 1739938566))) (.branch 88 (.branch 87 (.leaf 1709561779) (.leaf 1679731579)) (.branch 89 (.leaf 1650437526) (.leaf 1621669405)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1593417218) (.branch 92 (.leaf 1565671180) (.leaf 1538421711))) (.branch 95 (.branch 94 (.leaf 1511659434) (.leaf 1485375169)) (.branch 96 (.leaf 1459559925) (.leaf 1434204901)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1409301476) (.leaf 1384841207)) (.branch 100 (.leaf 1360815824) (.leaf 1337217227))) (.branch 103 (.branch 102 (.leaf 1314037481) (.leaf 1291268810)) (.branch 104 (.leaf 1268903599) (.leaf 1246934383))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1225353850) (.leaf 1204154831)) (.branch 108 (.leaf 1183330304) (.leaf 1162873383))) (.branch 111 (.branch 110 (.leaf 1142777322) (.leaf 1123035506)) (.branch 112 (.leaf 1103641452) (.leaf 1084588803)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1065871328) (.leaf 1047482917)) (.branch 116 (.leaf 1029417580) (.leaf 1011669444))) (.branch 119 (.branch 118 (.leaf 994232747) (.leaf 977101842)) (.branch 120 (.leaf 960271189) (.leaf 943735356)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1327).prefactor = (4683571206340049/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1327).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1327).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue]
    have hfirst : (generalMeanRows 1327).q*(generalMeanRows 1327).c/2-2 = (5411/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable439.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1327).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1327

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1327).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1327).criticalRate j.val*(generalMeanRows 1327).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1327).c*(generalMeanRows 1327).criticalPoint j.val)).2-
      (generalMeanRows 1327).J/2-(generalMeanRows 1327).error (generalMeanGrid j.val)+
      (generalMeanRows 1327).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1327).c)).2-
      (generalMeanRows 1327).J/2-(generalMeanRows 1327).error 4 := by
  have he : (generalMeanRows 1327).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1327) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1327)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1327

/-! Kernel-checked entropy margins for general spectral rectangle 1328. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1328
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8191161206) (.branch 2 (.leaf 8019712326) (.leaf 7853092796))) (.branch 5 (.branch 4 (.leaf 7691083540) (.leaf 7533481140)) (.branch 6 (.leaf 7380096326) (.leaf 7230752634)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 7085285227) (.leaf 6943539844)) (.branch 10 (.leaf 6805371875) (.leaf 6670645523))) (.branch 13 (.branch 12 (.leaf 6539233064) (.leaf 6411014186)) (.branch 14 (.leaf 6285875386) (.leaf 6163709435))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 6044414893) (.branch 17 (.leaf 5927895673) (.leaf 5814060640))) (.branch 20 (.branch 19 (.leaf 5702823256) (.leaf 5594101249)) (.branch 21 (.leaf 5487816318) (.leaf 5383893858)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 5282262717) (.leaf 5182854963)) (.branch 25 (.leaf 5085605683) (.leaf 4990452784))) (.branch 28 (.branch 27 (.leaf 4897336822) (.leaf 4806200842)) (.branch 29 (.leaf 4716990225) (.leaf 4629652553)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 4544137479) (.branch 32 (.leaf 4460396614) (.leaf 4378383415))) (.branch 35 (.branch 34 (.leaf 4298053083) (.leaf 4219362472)) (.branch 36 (.leaf 4142269999) (.leaf 4066735565)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3992720476) (.leaf 3920187376)) (.branch 40 (.leaf 3849100180) (.leaf 3779424008))) (.branch 43 (.branch 42 (.leaf 3711125135) (.leaf 3644170930)) (.branch 44 (.leaf 3578529808) (.leaf 3514171184))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 3451065425) (.branch 47 (.leaf 3389183810) (.leaf 3328498489))) (.branch 50 (.branch 49 (.leaf 3268982447) (.leaf 3210609469)) (.branch 51 (.leaf 3153354106) (.leaf 3097191644)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 3042098072) (.leaf 2988050059)) (.branch 55 (.leaf 2935024925) (.leaf 2883000613))) (.branch 58 (.branch 57 (.leaf 2831955669) (.leaf 2781869219)) (.branch 59 (.leaf 2732720946) (.leaf 2684491072))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2637160334) (.branch 62 (.leaf 2590709971) (.leaf 2545121704))) (.branch 65 (.branch 64 (.leaf 2500377719) (.leaf 2456460651)) (.branch 66 (.leaf 2413353570) (.leaf 2371039965)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 2329503733) (.leaf 2288729162)) (.branch 70 (.leaf 2248700920) (.leaf 2209404045))) (.branch 73 (.branch 72 (.leaf 2170823929) (.leaf 2132946310)) (.branch 74 (.leaf 2095757263) (.leaf 2059243186))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 2023390790) (.branch 77 (.leaf 1988187095) (.leaf 1953619416))) (.branch 80 (.branch 79 (.leaf 1919675355) (.leaf 1886342794)) (.branch 81 (.leaf 1853609887) (.leaf 1821465052)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1789896963) (.leaf 1758894544)) (.branch 85 (.leaf 1728446960) (.leaf 1698543615))) (.branch 88 (.branch 87 (.leaf 1669174138) (.leaf 1640328386)) (.branch 89 (.leaf 1611996431) (.leaf 1584168556)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1556835253) (.branch 92 (.leaf 1529987212) (.leaf 1503615322))) (.branch 95 (.branch 94 (.leaf 1477710659) (.leaf 1452264488)) (.branch 96 (.leaf 1427268253) (.leaf 1402713576)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1378592253) (.leaf 1354896244)) (.branch 100 (.leaf 1331617678) (.leaf 1308748840))) (.branch 103 (.branch 102 (.leaf 1286282173) (.leaf 1264210273)) (.branch 104 (.leaf 1242525884) (.leaf 1221221897))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1200291343) (.leaf 1179727392)) (.branch 108 (.leaf 1159523351) (.leaf 1139672659))) (.branch 111 (.branch 110 (.leaf 1120168883) (.leaf 1101005717)) (.branch 112 (.leaf 1082176980) (.leaf 1063676610)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1045498665) (.leaf 1027637315)) (.branch 116 (.leaf 1010086848) (.leaf 992841658))) (.branch 119 (.branch 118 (.leaf 975896249) (.leaf 959245230)) (.branch 120 (.leaf 942883315) (.leaf 926805317)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1328).prefactor = (1089806461520589/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1328).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1328).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue]
    have hfirst : (generalMeanRows 1328).q*(generalMeanRows 1328).c/2-2 = (1339/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable323.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1328).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1328

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1328).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1328).criticalRate j.val*(generalMeanRows 1328).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1328).c*(generalMeanRows 1328).criticalPoint j.val)).2-
      (generalMeanRows 1328).J/2-(generalMeanRows 1328).error (generalMeanGrid j.val)+
      (generalMeanRows 1328).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1328).c)).2-
      (generalMeanRows 1328).J/2-(generalMeanRows 1328).error 4 := by
  have he : (generalMeanRows 1328).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1328) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1328)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1328

/-! Kernel-checked entropy margins for general spectral rectangle 1329. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1329
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8318556774) (.branch 2 (.leaf 8142570010) (.leaf 7971564380))) (.branch 5 (.branch 4 (.leaf 7805314299) (.leaf 7643610265)) (.branch 6 (.leaf 7486257302) (.leaf 7333073588)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 7183889249) (.leaf 7038545279)) (.branch 10 (.leaf 6896892583) (.leaf 6758791130))) (.branch 13 (.branch 12 (.leaf 6624109187) (.leaf 6492722640)) (.branch 14 (.leaf 6364514376) (.leaf 6239373737))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 6117196019) (.branch 17 (.leaf 5997882024) (.leaf 5881337652))) (.branch 20 (.branch 19 (.leaf 5767473531) (.leaf 5656204684)) (.branch 21 (.leaf 5547450219) (.leaf 5441133053)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 5337179658) (.leaf 5235519824)) (.branch 25 (.leaf 5136086448) (.leaf 5038815339))) (.branch 28 (.branch 27 (.leaf 4943645035) (.leaf 4850516636)) (.branch 29 (.leaf 4759373654) (.leaf 4670161872)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 4582829208) (.branch 32 (.leaf 4497325601) (.leaf 4413602895))) (.branch 35 (.branch 34 (.leaf 4331614733) (.leaf 4251316467)) (.branch 36 (.leaf 4172665060) (.leaf 4095619011)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 4020138269) (.leaf 3946184166)) (.branch 40 (.leaf 3873719345) (.leaf 3802707699))) (.branch 43 (.branch 42 (.leaf 3733114312) (.leaf 3664905400)) (.branch 44 (.leaf 3598048262) (.leaf 3532511229))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 3468263620) (.branch 47 (.leaf 3405275696) (.leaf 3343518619))) (.branch 50 (.branch 49 (.leaf 3282964419) (.leaf 3223585950)) (.branch 51 (.leaf 3165356861) (.leaf 3108251561)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 3052245192) (.leaf 2997313594)) (.branch 55 (.leaf 2943433285) (.leaf 2890581430))) (.branch 58 (.branch 57 (.leaf 2838735817) (.leaf 2787874836)) (.branch 59 (.leaf 2737977453) (.leaf 2689023194))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2640992122) (.branch 62 (.leaf 2593864816) (.leaf 2547622357))) (.branch 65 (.branch 64 (.leaf 2502246308) (.leaf 2457718700)) (.branch 66 (.leaf 2414022014) (.leaf 2371139165)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 2329053491) (.leaf 2287748738)) (.branch 70 (.leaf 2247209046) (.leaf 2207418937))) (.branch 73 (.branch 72 (.leaf 2168363304) (.leaf 2130027397)) (.branch 74 (.leaf 2092396815) (.leaf 2055457495))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 2019195698) (.branch 77 (.leaf 1983598005) (.leaf 1948651304))) (.branch 80 (.branch 79 (.leaf 1914342782) (.leaf 1880659916)) (.branch 81 (.leaf 1847590466) (.leaf 1815122465)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1783244213) (.leaf 1751944269)) (.branch 85 (.leaf 1721211445) (.leaf 1691034796))) (.branch 88 (.branch 87 (.leaf 1661403617) (.leaf 1632307434)) (.branch 89 (.leaf 1603736001) (.leaf 1575679289)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1548127486) (.branch 92 (.leaf 1521070986) (.leaf 1494500389))) (.branch 95 (.branch 94 (.leaf 1468406492) (.leaf 1442780285)) (.branch 96 (.leaf 1417612946) (.leaf 1392895837)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1368620499) (.leaf 1344778649)) (.branch 100 (.leaf 1321362172) (.leaf 1298363121))) (.branch 103 (.branch 102 (.leaf 1275773710) (.leaf 1253586313)) (.branch 104 (.leaf 1231793458) (.leaf 1210387823))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1189362234) (.leaf 1168709662)) (.branch 108 (.leaf 1148423218) (.leaf 1128496149))) (.branch 111 (.branch 110 (.leaf 1108921839) (.leaf 1089693802)) (.branch 112 (.leaf 1070805678) (.leaf 1052251237)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1034024367) (.leaf 1016119078)) (.branch 116 (.leaf 998529497) (.leaf 981249867))) (.branch 119 (.branch 118 (.leaf 964274539) (.leaf 947597977)) (.branch 120 (.leaf 931214752) (.leaf 915119538)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1329).prefactor = (4472135954999801/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1329).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1329).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1329).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1329

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1329).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1329).criticalRate j.val*(generalMeanRows 1329).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1329).c*(generalMeanRows 1329).criticalPoint j.val)).2-
      (generalMeanRows 1329).J/2-(generalMeanRows 1329).error (generalMeanGrid j.val)+
      (generalMeanRows 1329).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1329).c)).2-
      (generalMeanRows 1329).J/2-(generalMeanRows 1329).error 4 := by
  have he : (generalMeanRows 1329).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1329) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1329)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1329

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock18 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 18 i) := by
  fin_cases i
  · exact EntropyRow1260.numerical
  · exact EntropyRow1261.numerical
  · exact EntropyRow1262.numerical
  · exact EntropyRow1263.numerical
  · exact EntropyRow1264.numerical
  · exact EntropyRow1265.numerical
  · exact EntropyRow1266.numerical
  · exact EntropyRow1267.numerical
  · exact EntropyRow1268.numerical
  · exact EntropyRow1269.numerical
  · exact EntropyRow1270.numerical
  · exact EntropyRow1271.numerical
  · exact EntropyRow1272.numerical
  · exact EntropyRow1273.numerical
  · exact EntropyRow1274.numerical
  · exact EntropyRow1275.numerical
  · exact EntropyRow1276.numerical
  · exact EntropyRow1277.numerical
  · exact EntropyRow1278.numerical
  · exact EntropyRow1279.numerical
  · exact EntropyRow1280.numerical
  · exact EntropyRow1281.numerical
  · exact EntropyRow1282.numerical
  · exact EntropyRow1283.numerical
  · exact EntropyRow1284.numerical
  · exact EntropyRow1285.numerical
  · exact EntropyRow1286.numerical
  · exact EntropyRow1287.numerical
  · exact EntropyRow1288.numerical
  · exact EntropyRow1289.numerical
  · exact EntropyRow1290.numerical
  · exact EntropyRow1291.numerical
  · exact EntropyRow1292.numerical
  · exact EntropyRow1293.numerical
  · exact EntropyRow1294.numerical
  · exact EntropyRow1295.numerical
  · exact EntropyRow1296.numerical
  · exact EntropyRow1297.numerical
  · exact EntropyRow1298.numerical
  · exact EntropyRow1299.numerical
  · exact EntropyRow1300.numerical
  · exact EntropyRow1301.numerical
  · exact EntropyRow1302.numerical
  · exact EntropyRow1303.numerical
  · exact EntropyRow1304.numerical
  · exact EntropyRow1305.numerical
  · exact EntropyRow1306.numerical
  · exact EntropyRow1307.numerical
  · exact EntropyRow1308.numerical
  · exact EntropyRow1309.numerical
  · exact EntropyRow1310.numerical
  · exact EntropyRow1311.numerical
  · exact EntropyRow1312.numerical
  · exact EntropyRow1313.numerical
  · exact EntropyRow1314.numerical
  · exact EntropyRow1315.numerical
  · exact EntropyRow1316.numerical
  · exact EntropyRow1317.numerical
  · exact EntropyRow1318.numerical
  · exact EntropyRow1319.numerical
  · exact EntropyRow1320.numerical
  · exact EntropyRow1321.numerical
  · exact EntropyRow1322.numerical
  · exact EntropyRow1323.numerical
  · exact EntropyRow1324.numerical
  · exact EntropyRow1325.numerical
  · exact EntropyRow1326.numerical
  · exact EntropyRow1327.numerical
  · exact EntropyRow1328.numerical
  · exact EntropyRow1329.numerical
end SingularValueBounds.KL.Certificates
