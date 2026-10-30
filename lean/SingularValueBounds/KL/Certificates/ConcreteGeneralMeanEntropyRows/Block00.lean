import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block00
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block01
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block02
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 0. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0000
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8851862756) (.branch 2 (.leaf 8551147021) (.leaf 8265148066))) (.branch 5 (.branch 4 (.leaf 7992981596) (.leaf 7733826739)) (.branch 6 (.leaf 7486920466) (.leaf 7251552617)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 7027061464) (.leaf 6812829726)) (.branch 10 (.leaf 6608280999) (.leaf 6412876525))) (.branch 13 (.branch 12 (.leaf 6226112288) (.leaf 6047516367)) (.branch 14 (.leaf 5876646548) (.leaf 5713088136))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5556451973) (.branch 17 (.leaf 5406372618) (.leaf 5262506686))) (.branch 20 (.branch 19 (.leaf 5124531320) (.leaf 4992142796)) (.branch 21 (.leaf 4865055228) (.leaf 4742999385)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4625721593) (.leaf 4512982727)) (.branch 25 (.leaf 4404557271) (.leaf 4300232453))) (.branch 28 (.branch 27 (.leaf 4199807442) (.leaf 4103092601)) (.branch 29 (.leaf 4009908794) (.leaf 3920086742)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3833466424) (.branch 32 (.leaf 3749896516) (.leaf 3669233875))) (.branch 35 (.branch 34 (.leaf 3591343044) (.leaf 3516095806)) (.branch 36 (.leaf 3443370759) (.leaf 3373052913)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3305033326) (.leaf 3239208752)) (.branch 40 (.leaf 3175481319) (.leaf 3113758219))) (.branch 43 (.branch 42 (.leaf 3053951427) (.leaf 2995977428)) (.branch 44 (.leaf 2939756966) (.leaf 2885214811))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2832279531) (.branch 47 (.leaf 2780883284) (.leaf 2730961625))) (.branch 50 (.branch 49 (.leaf 2682453315) (.leaf 2635300153)) (.branch 51 (.leaf 2589446805) (.leaf 2544840657)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2501431663) (.leaf 2459172211)) (.branch 55 (.leaf 2418016993) (.leaf 2377922884))) (.branch 58 (.branch 57 (.leaf 2338848822) (.leaf 2300755708)) (.branch 59 (.leaf 2263606296) (.leaf 2227365099))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2191998297) (.branch 62 (.leaf 2157473652) (.leaf 2123760424))) (.branch 65 (.branch 64 (.leaf 2090829297) (.leaf 2058652302)) (.branch 66 (.leaf 2027202754) (.leaf 1996455179)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1966385259) (.leaf 1936969771)) (.branch 70 (.leaf 1908186531) (.leaf 1880014345))) (.branch 73 (.branch 72 (.leaf 1852432956) (.leaf 1825422997)) (.branch 74 (.leaf 1798965951) (.leaf 1773044104))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1747640508) (.branch 77 (.leaf 1722738945) (.leaf 1698323885))) (.branch 80 (.branch 79 (.leaf 1674380459) (.leaf 1650894423)) (.branch 81 (.leaf 1627852130) (.leaf 1605240498)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1583046986) (.leaf 1561259565)) (.branch 85 (.leaf 1539866697) (.leaf 1518857309))) (.branch 88 (.branch 87 (.leaf 1498220771) (.leaf 1477946875)) (.branch 89 (.leaf 1458025816) (.leaf 1438448174)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1419204893) (.branch 92 (.leaf 1400287266) (.leaf 1381686918))) (.branch 95 (.branch 94 (.leaf 1363395793) (.leaf 1345406134)) (.branch 96 (.leaf 1327710476) (.leaf 1310301626)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1293172657) (.leaf 1276316891)) (.branch 100 (.leaf 1259727889) (.leaf 1243399442))) (.branch 103 (.branch 102 (.leaf 1227325559) (.leaf 1211500458)) (.branch 104 (.leaf 1195918557) (.leaf 1180574464))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1165462969) (.leaf 1150579037)) (.branch 108 (.leaf 1135917801) (.leaf 1121474551))) (.branch 111 (.branch 110 (.leaf 1107244733) (.leaf 1093223937)) (.branch 112 (.leaf 1079407893) (.leaf 1065792466)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1052373649) (.leaf 1039147559)) (.branch 116 (.leaf 1026110430) (.leaf 1013258609))) (.branch 119 (.branch 118 (.leaf 1000588552) (.leaf 988096820)) (.branch 120 (.leaf 975780072) (.leaf 963635065)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 0).prefactor = (7333378285055737/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 0).cutoff/(generalMeanRows 0).c)).2 =
    (1920215860397/4000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 0).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 0).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 0).q*(generalMeanRows 0).cutoff/2-2 = (328/165:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable000.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 0).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 0

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 0).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 0).criticalRate j.val*(generalMeanRows 0).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 0).c*(generalMeanRows 0).criticalPoint j.val)).2-
      (generalMeanRows 0).J/2-(generalMeanRows 0).error (generalMeanGrid j.val)+
      (generalMeanRows 0).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 0).c)).2-
      (generalMeanRows 0).J/2-(generalMeanRows 0).error 4 := by
  have he : (generalMeanRows 0).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 0) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 0)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0000

/-! Kernel-checked entropy margins for general spectral rectangle 1. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0001
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8027293837) (.branch 2 (.leaf 7715300791) (.leaf 7418739642))) (.branch 5 (.branch 4 (.leaf 7136689407) (.leaf 6868295171)) (.branch 6 (.leaf 6612762244) (.leaf 6369350969)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6137372074) (.leaf 5916182523)) (.branch 10 (.leaf 5705181778) (.leaf 5503808437))) (.branch 13 (.branch 12 (.leaf 5311537193) (.leaf 5127876087)) (.branch 14 (.leaf 4952364008) (.leaf 4784568423))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4624083307) (.branch 17 (.leaf 4470527249) (.leaf 4323541730))) (.branch 20 (.branch 19 (.leaf 4182789527) (.leaf 4047953264)) (.branch 21 (.leaf 3918734072) (.leaf 3794850354)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3676036651) (.leaf 3562042589)) (.branch 25 (.leaf 3452631908) (.leaf 3347581567))) (.branch 28 (.branch 27 (.leaf 3246680906) (.leaf 3149730877)) (.branch 29 (.leaf 3056543323) (.leaf 2966940314)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2880753521) (.branch 32 (.leaf 2797823645) (.leaf 2717999870))) (.branch 35 (.branch 34 (.leaf 2641139365) (.leaf 2567106813)) (.branch 36 (.leaf 2495773974) (.leaf 2427019271)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2360727409) (.leaf 2296789016)) (.branch 40 (.leaf 2235100307) (.leaf 2175562767))) (.branch 43 (.branch 42 (.leaf 2118082854) (.leaf 2062571725)) (.branch 44 (.leaf 2008944976) (.leaf 1957122391))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1907027721) (.branch 47 (.leaf 1858588460) (.leaf 1811735646))) (.branch 50 (.branch 49 (.leaf 1766403671) (.leaf 1722530096)) (.branch 51 (.leaf 1680055487) (.leaf 1638923251)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1599079489) (.leaf 1560472851)) (.branch 55 (.leaf 1523054405) (.leaf 1486777510))) (.branch 58 (.branch 57 (.leaf 1451597697) (.leaf 1417472555)) (.branch 59 (.leaf 1384361628) (.leaf 1352226312))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1321029763) (.branch 62 (.leaf 1290736807) (.leaf 1261313852))) (.branch 65 (.branch 64 (.leaf 1232728813) (.leaf 1204951035)) (.branch 66 (.leaf 1177951219) (.leaf 1151701359)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1126174673) (.leaf 1101345546)) (.branch 70 (.leaf 1077189471) (.leaf 1053682998))) (.branch 73 (.branch 72 (.leaf 1030803676) (.leaf 1008530011)) (.branch 74 (.leaf 986841416) (.leaf 965718169))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 945141370) (.branch 77 (.leaf 925092905) (.leaf 905555403))) (.branch 80 (.branch 79 (.leaf 886512207) (.leaf 867947336)) (.branch 81 (.leaf 849845455) (.leaf 832191845)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 814972373) (.leaf 798173468)) (.branch 85 (.leaf 781782089) (.leaf 765785709))) (.branch 88 (.branch 87 (.leaf 750172284) (.leaf 734930235)) (.branch 89 (.leaf 720048426) (.leaf 705516144)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 691323079) (.branch 92 (.leaf 677459308) (.leaf 663915278))) (.branch 95 (.branch 94 (.leaf 650681786) (.leaf 637749968)) (.branch 96 (.leaf 625111282) (.leaf 612757492)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 600680661) (.leaf 588873130)) (.branch 100 (.leaf 577327512) (.leaf 566036678))) (.branch 103 (.branch 102 (.leaf 554993748) (.leaf 544192078)) (.branch 104 (.leaf 533625250) (.leaf 523287064))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 513171532) (.leaf 503272861)) (.branch 108 (.leaf 493585453) (.leaf 484103893))) (.branch 111 (.branch 110 (.leaf 474822943) (.leaf 465737534)) (.branch 112 (.leaf 456842759) (.leaf 448133868)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 439606261) (.leaf 431255483)) (.branch 116 (.leaf 423077214) (.leaf 415067271))) (.branch 119 (.branch 118 (.leaf 407221596) (.leaf 399536256)) (.branch 120 (.leaf 392007436) (.leaf 384631433)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1).prefactor = (1937292430772137/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1).cutoff/(generalMeanRows 1).c)).2 =
    (192694369279087/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1).q*(generalMeanRows 1).c/2-2 = (57/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable001.value]
    have hcontinuation : (generalMeanRows 1).q*(generalMeanRows 1).cutoff/2-2 = (328/165:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable000.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1).criticalRate j.val*(generalMeanRows 1).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1).c*(generalMeanRows 1).criticalPoint j.val)).2-
      (generalMeanRows 1).J/2-(generalMeanRows 1).error (generalMeanGrid j.val)+
      (generalMeanRows 1).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1).c)).2-
      (generalMeanRows 1).J/2-(generalMeanRows 1).error 4 := by
  have he : (generalMeanRows 1).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0001

/-! Kernel-checked entropy margins for general spectral rectangle 2. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0002
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6982729328) (.branch 2 (.leaf 6670193439) (.leaf 6373726987))) (.branch 5 (.branch 4 (.leaf 6092368274) (.leaf 5825224549)) (.branch 6 (.leaf 5571465888) (.leaf 5330319770)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5101066218) (.leaf 4883033463)) (.branch 10 (.leaf 4675594038) (.leaf 4478161271))) (.branch 13 (.branch 12 (.leaf 4290186110) (.leaf 4111154255)) (.branch 14 (.leaf 3940583553) (.leaf 3778021632))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3623043737) (.branch 17 (.leaf 3475250769) (.leaf 3334267477))) (.branch 20 (.branch 19 (.leaf 3199740808) (.leaf 3071338392)) (.branch 21 (.leaf 2948747150) (.leaf 2831672008)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2719834718) (.leaf 2612972762)) (.branch 25 (.leaf 2510838347) (.leaf 2413197466))) (.branch 28 (.branch 27 (.leaf 2319829036) (.leaf 2230524091)) (.branch 29 (.leaf 2145085039) (.leaf 2063324969)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1985067001) (.branch 32 (.leaf 1910143692) (.leaf 1838396469))) (.branch 35 (.branch 34 (.leaf 1769675113) (.leaf 1703837266)) (.branch 36 (.leaf 1640747976) (.leaf 1580279274)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1522309773) (.leaf 1466724295)) (.branch 40 (.leaf 1413413519) (.leaf 1362273657))) (.branch 43 (.branch 42 (.leaf 1313206145) (.leaf 1266117354)) (.branch 44 (.leaf 1220918319) (.leaf 1177524483))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1135855462) (.branch 47 (.leaf 1095834815) (.leaf 1057389837))) (.branch 50 (.branch 49 (.leaf 1020451355) (.leaf 984953545)) (.branch 51 (.leaf 950833749) (.leaf 918032318)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 886492445) (.leaf 856160023)) (.branch 55 (.leaf 826983504) (.leaf 798913767))) (.branch 58 (.branch 57 (.leaf 771903992) (.leaf 745909545)) (.branch 59 (.leaf 720887865) (.leaf 696798361))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 673602310) (.branch 62 (.leaf 651262767) (.leaf 629744472))) (.branch 65 (.branch 64 (.leaf 609013770) (.leaf 589038530)) (.branch 66 (.leaf 569788068) (.leaf 551233078)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 533345567) (.leaf 516098784)) (.branch 70 (.leaf 499467168) (.leaf 483426283))) (.branch 73 (.branch 72 (.leaf 467952770) (.leaf 453024291)) (.branch 74 (.leaf 438619483) (.leaf 424717909))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 411300018) (.branch 77 (.leaf 398347099) (.leaf 385841243))) (.branch 80 (.branch 79 (.leaf 373765306) (.leaf 362102875)) (.branch 81 (.leaf 350838228) (.leaf 339956310)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 329442696) (.leaf 319283564)) (.branch 85 (.leaf 309465668) (.leaf 299976312))) (.branch 88 (.branch 87 (.leaf 290803324) (.leaf 281935032)) (.branch 89 (.leaf 273360241) (.leaf 265068216)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 257048655) (.branch 92 (.leaf 249291672) (.leaf 241787783))) (.branch 95 (.branch 94 (.leaf 234527880) (.leaf 227503222)) (.branch 96 (.leaf 220705413) (.leaf 214126391)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 207758413) (.leaf 201594037)) (.branch 100 (.leaf 195626116) (.leaf 189847778))) (.branch 103 (.branch 102 (.leaf 184252419) (.leaf 178833690)) (.branch 104 (.leaf 173585487) (.leaf 168501937))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 163577394) (.leaf 158806426)) (.branch 108 (.leaf 154183805) (.leaf 149704501))) (.branch 111 (.branch 110 (.leaf 145363672) (.leaf 141156659)) (.branch 112 (.leaf 137078974) (.leaf 133126296)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 129294464) (.leaf 125579469)) (.branch 116 (.leaf 121977449) (.leaf 118484685))) (.branch 119 (.branch 118 (.leaf 115097589) (.leaf 111812707)) (.branch 120 (.leaf 108626705) (.leaf 105536372)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 2).prefactor = (4094267952848139/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 2).cutoff/(generalMeanRows 2).c)).2 =
    (132013940776953/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 2).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 2).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 2).q*(generalMeanRows 2).c/2-2 = (17/16:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable002.value]
    have hcontinuation : (generalMeanRows 2).q*(generalMeanRows 2).cutoff/2-2 = (328/165:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable000.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 2).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 2

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 2).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 2).criticalRate j.val*(generalMeanRows 2).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 2).c*(generalMeanRows 2).criticalPoint j.val)).2-
      (generalMeanRows 2).J/2-(generalMeanRows 2).error (generalMeanGrid j.val)+
      (generalMeanRows 2).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 2).c)).2-
      (generalMeanRows 2).J/2-(generalMeanRows 2).error 4 := by
  have he : (generalMeanRows 2).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 2) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 2)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0002

/-! Kernel-checked entropy margins for general spectral rectangle 3. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0003
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6491572586) (.branch 2 (.leaf 6283423401) (.leaf 6085717817))) (.branch 5 (.branch 4 (.leaf 5897795475) (.leaf 5719044809)) (.branch 6 (.leaf 5548898783) (.leaf 5386831074)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5232352650) (.leaf 5085008694)) (.branch 10 (.leaf 4944375837) (.leaf 4810059646))) (.branch 13 (.branch 12 (.leaf 4681692358) (.leaf 4558930823)) (.branch 14 (.leaf 4441454626) (.leaf 4328964384))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4221180186) (.branch 17 (.leaf 4117840167) (.leaf 4018699204))) (.branch 20 (.branch 19 (.leaf 3923527722) (.leaf 3832110588)) (.branch 21 (.leaf 3744246104) (.leaf 3659745077)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3578429956) (.leaf 3500134043)) (.branch 25 (.leaf 3424700761) (.leaf 3351982975))) (.branch 28 (.branch 27 (.leaf 3281842366) (.leaf 3214148852)) (.branch 29 (.leaf 3148780046) (.leaf 3085620760)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3024562538) (.branch 32 (.leaf 2965503227) (.leaf 2908346574))) (.branch 35 (.branch 34 (.leaf 2853001854) (.leaf 2799383521)) (.branch 36 (.leaf 2747410887) (.leaf 2697007814)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2648102440) (.leaf 2600626912)) (.branch 40 (.leaf 2554517138) (.leaf 2509712566))) (.branch 43 (.branch 42 (.leaf 2466155959) (.leaf 2423793205)) (.branch 44 (.leaf 2382573122) (.leaf 2342447286))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2303369868) (.branch 47 (.leaf 2265297478) (.leaf 2228189022))) (.branch 50 (.branch 49 (.leaf 2192005566) (.leaf 2156710214)) (.branch 51 (.leaf 2122267982) (.leaf 2088645695)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2055811877) (.leaf 2023736655)) (.branch 55 (.leaf 1992391666) (.leaf 1961749975))) (.branch 58 (.branch 57 (.leaf 1931785988) (.leaf 1902475380)) (.branch 59 (.leaf 1873795023) (.leaf 1845722915))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1818238124) (.branch 62 (.leaf 1791320722) (.leaf 1764951732))) (.branch 65 (.branch 64 (.leaf 1739113075) (.leaf 1713787522)) (.branch 66 (.leaf 1688958645) (.leaf 1664610774)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1640728957) (.leaf 1617298920)) (.branch 70 (.leaf 1594307030) (.leaf 1571740263))) (.branch 73 (.branch 72 (.leaf 1549586167) (.leaf 1527832837)) (.branch 74 (.leaf 1506468883) (.leaf 1485483401))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1464865952) (.branch 77 (.leaf 1444606535) (.leaf 1424695564))) (.branch 80 (.branch 79 (.leaf 1405123848) (.leaf 1385882568)) (.branch 81 (.leaf 1366963263) (.leaf 1348357806)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1330058390) (.leaf 1312057513)) (.branch 85 (.leaf 1294347960) (.leaf 1276922791))) (.branch 88 (.branch 87 (.leaf 1259775325) (.leaf 1242899130)) (.branch 89 (.leaf 1226288008) (.leaf 1209935988)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1193837308) (.branch 92 (.leaf 1177986412) (.leaf 1162377937))) (.branch 95 (.branch 94 (.leaf 1147006703) (.leaf 1131867706)) (.branch 96 (.leaf 1116956110) (.leaf 1102267238)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1087796566) (.leaf 1073539712)) (.branch 100 (.leaf 1059492438) (.leaf 1045650634))) (.branch 103 (.branch 102 (.leaf 1032010319) (.leaf 1018567632)) (.branch 104 (.leaf 1005318827) (.leaf 992260271))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 979388434) (.leaf 966699889)) (.branch 108 (.leaf 954191306) (.leaf 941859449))) (.branch 111 (.branch 110 (.leaf 929701167) (.leaf 917713400)) (.branch 112 (.leaf 905893166) (.leaf 894237564)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 882743766) (.leaf 871409020)) (.branch 116 (.leaf 860230641) (.leaf 849206013))) (.branch 119 (.branch 118 (.leaf 838332582) (.leaf 827607858)) (.branch 120 (.leaf 817029410) (.leaf 806594866)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 3).prefactor = (2898898535834433/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 3).cutoff/(generalMeanRows 3).c)).2 =
    (539969618435087/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 3).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 3).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 3).q*(generalMeanRows 3).c/2-2 = (49/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable003.value]
    have hcontinuation : (generalMeanRows 3).q*(generalMeanRows 3).cutoff/2-2 = (25/11:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable004.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 3).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 3

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 3).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 3).criticalRate j.val*(generalMeanRows 3).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 3).c*(generalMeanRows 3).criticalPoint j.val)).2-
      (generalMeanRows 3).J/2-(generalMeanRows 3).error (generalMeanGrid j.val)+
      (generalMeanRows 3).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 3).c)).2-
      (generalMeanRows 3).J/2-(generalMeanRows 3).error 4 := by
  have he : (generalMeanRows 3).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 3) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 3)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0003

/-! Kernel-checked entropy margins for general spectral rectangle 4. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0004
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6731555493) (.branch 2 (.leaf 6515711370) (.leaf 6310696932))) (.branch 5 (.branch 4 (.leaf 6115827405) (.leaf 5930468617)) (.branch 6 (.leaf 5754032569) (.leaf 5585973480)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5425784239) (.leaf 5272993216)) (.branch 10 (.leaf 5127161391) (.leaf 4987879747))) (.branch 13 (.branch 12 (.leaf 4854766929) (.leaf 4727467099)) (.branch 14 (.leaf 4605647998) (.leaf 4488999174))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4377230369) (.branch 17 (.leaf 4270070037) (.leaf 4167263995))) (.branch 20 (.branch 19 (.leaf 4068574177) (.leaf 3973777500)) (.branch 21 (.leaf 3882664809) (.leaf 3795039915)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3710718706) (.leaf 3629528320)) (.branch 25 (.leaf 3551306392) (.leaf 3475900347))) (.branch 28 (.branch 27 (.leaf 3403166754) (.leaf 3332970720)) (.branch 29 (.leaf 3265185336) (.leaf 3199691153)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3136375708) (.branch 32 (.leaf 3075133070) (.leaf 3015863429))) (.branch 35 (.branch 34 (.leaf 2958472704) (.leaf 2902872189)) (.branch 36 (.leaf 2848978210) (.leaf 2796711817)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2745998491) (.leaf 2696767870)) (.branch 40 (.leaf 2648953493) (.leaf 2602492568))) (.branch 43 (.branch 42 (.leaf 2557325744) (.leaf 2513396908)) (.branch 44 (.leaf 2470652985) (.leaf 2429043762))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2388521716) (.branch 47 (.leaf 2349041851) (.leaf 2310561555))) (.branch 50 (.branch 49 (.leaf 2273040456) (.leaf 2236440291)) (.branch 51 (.leaf 2200724786) (.leaf 2165859538)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2131811907) (.leaf 2098550916)) (.branch 55 (.leaf 2066047154) (.leaf 2034272689))) (.branch 58 (.branch 57 (.leaf 2003200982) (.leaf 1972806809)) (.branch 59 (.leaf 1943066185) (.leaf 1913956297))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1885455438) (.branch 62 (.leaf 1857542943) (.leaf 1830199134))) (.branch 65 (.branch 64 (.leaf 1803405264) (.leaf 1777143467)) (.branch 66 (.leaf 1751396706) (.leaf 1726148734)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1701384045) (.leaf 1677087837)) (.branch 70 (.leaf 1653245975) (.leaf 1629844950))) (.branch 73 (.branch 72 (.leaf 1606871854) (.leaf 1584314339)) (.branch 74 (.leaf 1562160593) (.leaf 1540399312))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1519019670) (.branch 77 (.leaf 1498011295) (.leaf 1477364248))) (.branch 80 (.branch 79 (.leaf 1457068997) (.leaf 1437116398)) (.branch 81 (.leaf 1417497677) (.leaf 1398204406)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1379228491) (.leaf 1360562151)) (.branch 85 (.leaf 1342197904) (.leaf 1324128555))) (.branch 88 (.branch 87 (.leaf 1306347175) (.leaf 1288847094)) (.branch 89 (.leaf 1271621887) (.leaf 1254665358)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1237971536) (.branch 92 (.leaf 1221534659) (.leaf 1205349163))) (.branch 95 (.branch 94 (.leaf 1189409680) (.leaf 1173711019)) (.branch 96 (.leaf 1158248166) (.leaf 1143016270)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1128010640) (.leaf 1113226734)) (.branch 100 (.leaf 1098660155) (.leaf 1084306642))) (.branch 103 (.branch 102 (.leaf 1070162066) (.leaf 1056222425)) (.branch 104 (.leaf 1042483833) (.leaf 1028942523))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1015594835) (.leaf 1002437216)) (.branch 108 (.leaf 989466211) (.leaf 976678464))) (.branch 111 (.branch 110 (.leaf 964070711) (.leaf 951639776)) (.branch 112 (.leaf 939382567) (.leaf 927296076)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 915377371) (.leaf 903623598)) (.branch 116 (.leaf 892031972) (.leaf 880599781))) (.branch 119 (.branch 118 (.leaf 869324377) (.leaf 858203178)) (.branch 120 (.leaf 847233662) (.leaf 836413370)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 4).prefactor = (6012132223762353/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 4).cutoff/(generalMeanRows 4).c)).2 =
    (539969618435087/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 4).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 4).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 4).q*(generalMeanRows 4).c/2-2 = (49/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable003.value]
    have hcontinuation : (generalMeanRows 4).q*(generalMeanRows 4).cutoff/2-2 = (25/11:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable004.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 4).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 4

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 4).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 4).criticalRate j.val*(generalMeanRows 4).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 4).c*(generalMeanRows 4).criticalPoint j.val)).2-
      (generalMeanRows 4).J/2-(generalMeanRows 4).error (generalMeanGrid j.val)+
      (generalMeanRows 4).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 4).c)).2-
      (generalMeanRows 4).J/2-(generalMeanRows 4).error 4 := by
  have he : (generalMeanRows 4).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 4) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 4)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0004

/-! Kernel-checked entropy margins for general spectral rectangle 5. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0005
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6823972305) (.branch 2 (.leaf 6600194454) (.leaf 6387644299))) (.branch 5 (.branch 4 (.leaf 6185613267) (.leaf 5993445131)) (.branch 6 (.leaf 5810531429) (.leaf 5636307372)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5470248168) (.leaf 5311865725)) (.branch 10 (.leaf 5160705678) (.leaf 5016344695))) (.branch 13 (.branch 12 (.leaf 4878388051) (.leaf 4746467411)) (.branch 14 (.leaf 4620238823) (.leaf 4499380890))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4383593093) (.branch 17 (.leaf 4272594267) (.leaf 4166121200))) (.branch 20 (.branch 19 (.leaf 4063927347) (.leaf 3965781654)) (.branch 21 (.leaf 3871467473) (.leaf 3780781561)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3693533162) (.leaf 3609543156)) (.branch 25 (.leaf 3528643277) (.leaf 3450675383))) (.branch 28 (.branch 27 (.leaf 3375490785) (.leaf 3302949628)) (.branch 29 (.leaf 3232920308) (.leaf 3165278942)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3099908868) (.branch 32 (.leaf 3036700181) (.leaf 2975549306))) (.branch 35 (.branch 34 (.leaf 2916358597) (.leaf 2859035962)) (.branch 36 (.leaf 2803494522) (.leaf 2749652278)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2697431819) (.leaf 2646760033)) (.branch 40 (.leaf 2597567849) (.leaf 2549789987))) (.branch 43 (.branch 42 (.leaf 2503364731) (.leaf 2458233716)) (.branch 44 (.leaf 2414341721) (.leaf 2371636490))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2330068548) (.branch 47 (.leaf 2289591042) (.leaf 2250159581))) (.branch 50 (.branch 49 (.leaf 2211732100) (.leaf 2174268716)) (.branch 51 (.leaf 2137731605) (.leaf 2102084884)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2067294496) (.leaf 2033328108)) (.branch 55 (.leaf 2000155011) (.leaf 1967746027))) (.branch 58 (.branch 57 (.leaf 1936073425) (.leaf 1905110835)) (.branch 59 (.leaf 1874833177) (.leaf 1845216583))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1816238333) (.branch 62 (.leaf 1787876791) (.leaf 1760111345))) (.branch 65 (.branch 64 (.leaf 1732922348) (.leaf 1706291069)) (.branch 66 (.leaf 1680199641) (.leaf 1654631015)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1629568912) (.leaf 1604997789)) (.branch 70 (.leaf 1580902791) (.leaf 1557269721))) (.branch 73 (.branch 72 (.leaf 1534085001) (.leaf 1511335641)) (.branch 74 (.leaf 1489009208) (.leaf 1467093796))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1445578000) (.branch 77 (.leaf 1424450888) (.leaf 1403701977))) (.branch 80 (.branch 79 (.leaf 1383321212) (.leaf 1363298942)) (.branch 81 (.leaf 1343625900) (.leaf 1324293185)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1305292241) (.leaf 1286614842)) (.branch 85 (.leaf 1268253074) (.leaf 1250199320))) (.branch 88 (.branch 87 (.leaf 1232446248) (.leaf 1214986793)) (.branch 89 (.leaf 1197814146) (.leaf 1180921743)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1164303250) (.branch 92 (.leaf 1147952555) (.leaf 1131863758))) (.branch 95 (.branch 94 (.leaf 1116031158) (.leaf 1100449244)) (.branch 96 (.leaf 1085112690) (.leaf 1070016345)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1055155220) (.leaf 1040524488)) (.branch 100 (.leaf 1026119475) (.leaf 1011935647))) (.branch 103 (.branch 102 (.leaf 997968614) (.leaf 984214114)) (.branch 104 (.leaf 970668016) (.leaf 957326306))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 944185090) (.leaf 931240582)) (.branch 108 (.leaf 918489106) (.leaf 905927086))) (.branch 111 (.branch 110 (.leaf 893551045) (.leaf 881357600)) (.branch 112 (.leaf 869343458) (.leaf 857505412)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 845840341) (.leaf 834345202)) (.branch 116 (.leaf 823017029) (.leaf 811852931))) (.branch 119 (.branch 118 (.leaf 800850088) (.leaf 790005749)) (.branch 120 (.leaf 779317229) (.leaf 768781906)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 5).prefactor = (3117195499358631/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 5).cutoff/(generalMeanRows 5).c)).2 =
    (131998356847093/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 5).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 5).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 5).q*(generalMeanRows 5).c/2-2 = (13/25:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable005.value]
    have hcontinuation : (generalMeanRows 5).q*(generalMeanRows 5).cutoff/2-2 = (25/11:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable004.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 5).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 5

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 5).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 5).criticalRate j.val*(generalMeanRows 5).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 5).c*(generalMeanRows 5).criticalPoint j.val)).2-
      (generalMeanRows 5).J/2-(generalMeanRows 5).error (generalMeanGrid j.val)+
      (generalMeanRows 5).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 5).c)).2-
      (generalMeanRows 5).J/2-(generalMeanRows 5).error 4 := by
  have he : (generalMeanRows 5).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 5) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 5)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0005

/-! Kernel-checked entropy margins for general spectral rectangle 6. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0006
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6919048990) (.branch 2 (.leaf 6687159855) (.leaf 6466911413))) (.branch 5 (.branch 4 (.leaf 6257570368) (.leaf 6058457583)) (.branch 6 (.leaf 5868943333) (.leaf 5688443075)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5516413641) (.leaf 5352349828)) (.branch 10 (.leaf 5195781317) (.leaf 5046269892))) (.branch 13 (.branch 12 (.leaf 4903406921) (.leaf 4766811071)) (.branch 14 (.leaf 4636126228) (.leaf 4511019602))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4391180000) (.branch 17 (.leaf 4276316243) (.leaf 4166155719))) (.branch 20 (.branch 19 (.leaf 4060443054) (.leaf 3958938896)) (.branch 21 (.leaf 3861418787) (.leaf 3767672139)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3677501274) (.leaf 3590720550)) (.branch 25 (.leaf 3507155549) (.leaf 3426642324))) (.branch 28 (.branch 27 (.leaf 3349026708) (.leaf 3274163668)) (.branch 29 (.leaf 3201916707) (.leaf 3132157314)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3064764446) (.branch 32 (.leaf 2999624054) (.leaf 2936628633))) (.branch 35 (.branch 34 (.leaf 2875676814) (.leaf 2816672976)) (.branch 36 (.leaf 2759526887) (.leaf 2704153371)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2650471995) (.leaf 2598406778)) (.branch 40 (.leaf 2547885919) (.leaf 2498841543))) (.branch 43 (.branch 42 (.leaf 2451209464) (.leaf 2404928964)) (.branch 44 (.leaf 2359942583) (.leaf 2316195928))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2273637490) (.branch 47 (.leaf 2232218470) (.leaf 2191892627))) (.branch 50 (.branch 49 (.leaf 2152616123) (.leaf 2114347384)) (.branch 51 (.leaf 2077046971) (.leaf 2040677454)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2005203298) (.leaf 1970590755)) (.branch 55 (.leaf 1936807760) (.leaf 1903823837))) (.branch 58 (.branch 57 (.leaf 1871610011) (.leaf 1840138720)) (.branch 59 (.leaf 1809383738) (.leaf 1779320100))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1749924033) (.branch 62 (.leaf 1721172888) (.leaf 1693045079))) (.branch 65 (.branch 64 (.leaf 1665520025) (.leaf 1638578097)) (.branch 66 (.leaf 1612200561) (.leaf 1586369536)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1561067944) (.leaf 1536279467)) (.branch 70 (.leaf 1511988508) (.leaf 1488180153))) (.branch 73 (.branch 72 (.leaf 1464840134) (.leaf 1441954792)) (.branch 74 (.leaf 1419511053) (.leaf 1397496389))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1375898796) (.branch 77 (.leaf 1354706763) (.leaf 1333909248))) (.branch 80 (.branch 79 (.leaf 1313495655) (.leaf 1293455810)) (.branch 81 (.leaf 1273779942) (.leaf 1254458660)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1235482935) (.leaf 1216844082)) (.branch 85 (.leaf 1198533745) (.leaf 1180543879))) (.branch 88 (.branch 87 (.leaf 1162866733) (.leaf 1145494840)) (.branch 89 (.leaf 1128421002) (.leaf 1111638274)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1095139957) (.branch 92 (.leaf 1078919583) (.leaf 1062970904))) (.branch 95 (.branch 94 (.leaf 1047287885) (.leaf 1031864692)) (.branch 96 (.leaf 1016695681) (.leaf 1001775394)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 987098546) (.leaf 972660022)) (.branch 100 (.leaf 958454863) (.leaf 944478267))) (.branch 103 (.branch 102 (.leaf 930725576) (.leaf 917192272)) (.branch 104 (.leaf 903873972) (.leaf 890766420))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 877865485) (.leaf 865167153)) (.branch 108 (.leaf 852667521) (.leaf 840362798))) (.branch 111 (.branch 110 (.leaf 828249294) (.leaf 816323421)) (.branch 112 (.leaf 804581685) (.leaf 793020686)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 781637112) (.leaf 770427735)) (.branch 116 (.leaf 759389412) (.leaf 748519076))) (.branch 119 (.branch 118 (.leaf 737813737) (.leaf 727270479)) (.branch 120 (.leaf 716886456) (.leaf 706658889)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 6).prefactor = (1616216580004111/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 6).cutoff/(generalMeanRows 6).c)).2 =
    (64519871217671/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 6).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 6).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 6).q*(generalMeanRows 6).cutoff/2-2 = (25/11:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable004.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 6).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 6

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 6).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 6).criticalRate j.val*(generalMeanRows 6).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 6).c*(generalMeanRows 6).criticalPoint j.val)).2-
      (generalMeanRows 6).J/2-(generalMeanRows 6).error (generalMeanGrid j.val)+
      (generalMeanRows 6).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 6).c)).2-
      (generalMeanRows 6).J/2-(generalMeanRows 6).error 4 := by
  have he : (generalMeanRows 6).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 6) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 6)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0006

/-! Kernel-checked entropy margins for general spectral rectangle 7. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0007
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6863749776) (.branch 2 (.leaf 6623948860) (.leaf 6396215053))) (.branch 5 (.branch 4 (.leaf 6179790712) (.leaf 5973974113)) (.branch 6 (.leaf 5778114546) (.leaf 5591607941)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5413892940) (.leaf 5244447369)) (.branch 10 (.leaf 5082785060) (.leaf 4928452977))) (.branch 13 (.branch 12 (.leaf 4781028615) (.leaf 4640117643)) (.branch 14 (.leaf 4505351751) (.leaf 4376386700))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4252900536) (.branch 17 (.leaf 4134591956) (.leaf 4021178816))) (.branch 20 (.branch 19 (.leaf 3912396762) (.leaf 3807997968)) (.branch 21 (.leaf 3707749982) (.leaf 3611434661)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3518847185) (.leaf 3429795158)) (.branch 25 (.leaf 3344097764) (.leaf 3261584996))) (.branch 28 (.branch 27 (.leaf 3182096940) (.leaf 3105483112)) (.branch 29 (.leaf 3031601839) (.leaf 2960319692)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2891510955) (.branch 32 (.leaf 2825057131) (.leaf 2760846484))) (.branch 35 (.branch 34 (.leaf 2698773615) (.leaf 2638739061)) (.branch 36 (.leaf 2580648929) (.leaf 2524414549)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2469952152) (.leaf 2417182572)) (.branch 40 (.leaf 2366030964) (.leaf 2316426544))) (.branch 43 (.branch 42 (.leaf 2268302343) (.leaf 2221594977)) (.branch 44 (.leaf 2176244436) (.leaf 2132193884))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2089389467) (.branch 47 (.leaf 2047780143) (.leaf 2007317515))) (.branch 50 (.branch 49 (.leaf 1967955679) (.leaf 1929651074)) (.branch 51 (.leaf 1892362354) (.leaf 1856050257)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1820677486) (.leaf 1786208598)) (.branch 55 (.leaf 1752609900) (.leaf 1719849346))) (.branch 58 (.branch 57 (.leaf 1687896451) (.leaf 1656722198)) (.branch 59 (.leaf 1626298960) (.leaf 1596600421))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1567601506) (.branch 62 (.leaf 1539278308) (.leaf 1511608033))) (.branch 65 (.branch 64 (.leaf 1484568930) (.leaf 1458140239)) (.branch 66 (.leaf 1432302140) (.leaf 1407035698)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1382322819) (.leaf 1358146202)) (.branch 70 (.leaf 1334489303) (.leaf 1311336288))) (.branch 73 (.branch 72 (.leaf 1288672003) (.leaf 1266481931)) (.branch 74 (.leaf 1244752168) (.leaf 1223469383))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1202620794) (.branch 77 (.leaf 1182194139) (.leaf 1162177647))) (.branch 80 (.branch 79 (.leaf 1142560019) (.leaf 1123330398)) (.branch 81 (.leaf 1104478351) (.leaf 1085993846)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1067867236) (.leaf 1050089235)) (.branch 85 (.leaf 1032650904) (.leaf 1015543634))) (.branch 88 (.branch 87 (.leaf 998759128) (.leaf 982289389)) (.branch 89 (.leaf 966126705) (.leaf 950263635)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 934692995) (.branch 92 (.leaf 919407850) (.leaf 904401500))) (.branch 95 (.branch 94 (.leaf 889667469) (.leaf 875199497)) (.branch 96 (.leaf 860991528) (.leaf 847037702)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 833332346) (.leaf 819869967)) (.branch 100 (.leaf 806645244) (.leaf 793653018))) (.branch 103 (.branch 102 (.leaf 780888288) (.leaf 768346205)) (.branch 104 (.leaf 756022062) (.leaf 743911291))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 732009458) (.leaf 720312253)) (.branch 108 (.leaf 708815491) (.leaf 697515102))) (.branch 111 (.branch 110 (.leaf 686407131) (.leaf 675487730)) (.branch 112 (.leaf 664753154) (.leaf 654199759)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 643823998) (.leaf 633622416)) (.branch 116 (.leaf 623591646) (.leaf 613728408))) (.branch 119 (.branch 118 (.leaf 604029507) (.leaf 594491824)) (.branch 120 (.leaf 585112319) (.leaf 575888027)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 7).prefactor = (837982742506089/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 7).cutoff/(generalMeanRows 7).c)).2 =
    (4929021075771/10000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 7).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 7).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 7).q*(generalMeanRows 7).c/2-2 = (61/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable006.value]
    have hcontinuation : (generalMeanRows 7).q*(generalMeanRows 7).cutoff/2-2 = (25/11:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable004.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 7).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 7

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 7).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 7).criticalRate j.val*(generalMeanRows 7).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 7).c*(generalMeanRows 7).criticalPoint j.val)).2-
      (generalMeanRows 7).J/2-(generalMeanRows 7).error (generalMeanGrid j.val)+
      (generalMeanRows 7).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 7).c)).2-
      (generalMeanRows 7).J/2-(generalMeanRows 7).error 4 := by
  have he : (generalMeanRows 7).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 7) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 7)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0007

/-! Kernel-checked entropy margins for general spectral rectangle 8. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0008
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6261488577) (.branch 2 (.leaf 6017108400) (.leaf 5785221446))) (.branch 5 (.branch 4 (.leaf 5565048564) (.leaf 5355867949)) (.branch 6 (.leaf 5157010112) (.leaf 4967853380)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4787819866) (.leaf 4616371849)) (.branch 10 (.leaf 4453008514) (.leaf 4297263000))) (.branch 13 (.branch 12 (.leaf 4148699736) (.leaf 4006912022)) (.branch 14 (.leaf 3871519828) (.leaf 3742167787))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3618523373) (.branch 17 (.leaf 3500275225) (.leaf 3387131620))) (.branch 20 (.branch 19 (.leaf 3278819069) (.leaf 3175081028)) (.branch 21 (.leaf 3075676718) (.leaf 2980380033)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2888978535) (.leaf 2801272527)) (.branch 25 (.leaf 2717074200) (.leaf 2636206839))) (.branch 28 (.branch 27 (.leaf 2558504092) (.leaf 2483809290)) (.branch 29 (.leaf 2411974822) (.leaf 2342861546)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2276338250) (.branch 32 (.leaf 2212281152) (.leaf 2150573425))) (.branch 35 (.branch 34 (.leaf 2091104765) (.leaf 2033770986)) (.branch 36 (.leaf 1978473641) (.leaf 1925119667)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1873621063) (.leaf 1823894576)) (.branch 40 (.leaf 1775861419) (.leaf 1729447002))) (.branch 43 (.branch 42 (.leaf 1684580680) (.leaf 1641195524)) (.branch 44 (.leaf 1599228097) (.leaf 1558618252))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1519308941) (.branch 47 (.leaf 1481246032) (.leaf 1444378143))) (.branch 50 (.branch 49 (.leaf 1408656486) (.leaf 1374034714)) (.branch 51 (.leaf 1340468788) (.leaf 1307916843)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1276339066) (.leaf 1245697583)) (.branch 55 (.leaf 1215956351) (.leaf 1187081054))) (.branch 58 (.branch 57 (.leaf 1159039012) (.leaf 1131799087)) (.branch 59 (.leaf 1105331604) (.leaf 1079608267))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1054602088) (.branch 62 (.leaf 1030287313) (.leaf 1006639361))) (.branch 65 (.branch 64 (.leaf 983634759) (.leaf 961251082)) (.branch 66 (.leaf 939466903) (.leaf 918261734)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 897615985) (.leaf 877510909)) (.branch 70 (.leaf 857928567) (.leaf 838851781))) (.branch 73 (.branch 72 (.leaf 820264098) (.leaf 802149753)) (.branch 74 (.leaf 784493633) (.leaf 767281247))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 750498693) (.branch 77 (.leaf 734132630) (.leaf 718170251))) (.branch 80 (.branch 79 (.leaf 702599255) (.leaf 687407824)) (.branch 81 (.leaf 672584601) (.leaf 658118666)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 643999515) (.leaf 630217042)) (.branch 85 (.leaf 616761520) (.leaf 603623582))) (.branch 88 (.branch 87 (.leaf 590794206) (.leaf 578264700)) (.branch 89 (.leaf 566026682) (.leaf 554072074)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 542393081) (.branch 92 (.leaf 530982182) (.leaf 519832118))) (.branch 95 (.branch 94 (.leaf 508935880) (.leaf 498286696)) (.branch 96 (.leaf 487878024) (.leaf 477703542)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 467757136) (.leaf 458032893)) (.branch 100 (.leaf 448525092) (.leaf 439228197))) (.branch 103 (.branch 102 (.leaf 430136849) (.leaf 421245858)) (.branch 104 (.leaf 412550197) (.leaf 404044996))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 395725533) (.leaf 387587231)) (.branch 108 (.leaf 379625653) (.leaf 371836493))) (.branch 111 (.branch 110 (.leaf 364215574) (.leaf 356758843)) (.branch 112 (.leaf 349462363) (.leaf 342322314)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 335334983) (.leaf 328496766)) (.branch 116 (.leaf 321804158) (.leaf 315253754))) (.branch 119 (.branch 118 (.leaf 308842244) (.leaf 302566407)) (.branch 120 (.leaf 296423115) (.leaf 290409319)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 8).prefactor = (3475846420217969/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 8).cutoff/(generalMeanRows 8).c)).2 =
    (106552683269607/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 8).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 8).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 8).q*(generalMeanRows 8).c/2-2 = (79/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable007.value]
    have hcontinuation : (generalMeanRows 8).q*(generalMeanRows 8).cutoff/2-2 = (25/11:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable004.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 8).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 8

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 8).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 8).criticalRate j.val*(generalMeanRows 8).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 8).c*(generalMeanRows 8).criticalPoint j.val)).2-
      (generalMeanRows 8).J/2-(generalMeanRows 8).error (generalMeanGrid j.val)+
      (generalMeanRows 8).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 8).c)).2-
      (generalMeanRows 8).J/2-(generalMeanRows 8).error 4 := by
  have he : (generalMeanRows 8).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 8) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 8)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0008

/-! Kernel-checked entropy margins for general spectral rectangle 9. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0009
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5642980589) (.branch 2 (.leaf 5397863076) (.leaf 5165637325))) (.branch 5 (.branch 4 (.leaf 4945500222) (.leaf 4736707580)) (.branch 6 (.leaf 4538568966) (.leaf 4350443079)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4171733609) (.leaf 4001885514)) (.branch 10 (.leaf 3840381675) (.leaf 3686739863))) (.branch 13 (.branch 12 (.leaf 3540510007) (.leaf 3401271706)) (.branch 14 (.leaf 3268631971) (.leaf 3142223173))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3021701163) (.branch 17 (.leaf 2906743561) (.leaf 2797048183))) (.branch 20 (.branch 19 (.leaf 2692331609) (.leaf 2592327856)) (.branch 21 (.leaf 2496787169) (.leaf 2405474900)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2318170483) (.leaf 2234666477)) (.branch 25 (.leaf 2154767697) (.leaf 2078290396))) (.branch 28 (.branch 27 (.leaf 2005061518) (.leaf 1934918001)) (.branch 29 (.leaf 1867706132) (.leaf 1803280950)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1741505689) (.branch 32 (.leaf 1682251263) (.leaf 1625395783))) (.branch 35 (.branch 34 (.leaf 1570824114) (.leaf 1518427456)) (.branch 36 (.leaf 1468102956) (.leaf 1419753345)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1373286607) (.leaf 1328615653)) (.branch 40 (.leaf 1285658039) (.leaf 1244335679))) (.branch 43 (.branch 42 (.leaf 1204574597) (.leaf 1166304683)) (.branch 44 (.leaf 1129459464) (.leaf 1093975901))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1059794185) (.branch 47 (.leaf 1026857556) (.leaf 995112125))) (.branch 50 (.branch 49 (.leaf 964506718) (.leaf 934992716)) (.branch 51 (.leaf 906523916) (.leaf 879056396)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 852548389) (.leaf 826960162)) (.branch 55 (.leaf 802253906) (.leaf 778393632))) (.branch 58 (.branch 57 (.leaf 755345071) (.leaf 733075582)) (.branch 59 (.leaf 711554061) (.leaf 690750868))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 670637737) (.branch 62 (.leaf 651187714) (.leaf 632375083))) (.branch 65 (.branch 64 (.leaf 614175300) (.leaf 596564937)) (.branch 66 (.leaf 579521620) (.leaf 563023977)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 547051584) (.leaf 531584922)) (.branch 70 (.leaf 516605325) (.leaf 502094942))) (.branch 73 (.branch 72 (.leaf 488036692) (.leaf 474414231)) (.branch 74 (.leaf 461211910) (.leaf 448414744))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 436008379) (.branch 77 (.leaf 423979061) (.leaf 412313606))) (.branch 80 (.branch 79 (.leaf 400999373) (.leaf 390024242)) (.branch 81 (.leaf 379376583) (.leaf 369045235)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 359019486) (.leaf 349289051)) (.branch 85 (.leaf 339844050) (.leaf 330674994))) (.branch 88 (.branch 87 (.leaf 321772760) (.leaf 313128581)) (.branch 89 (.leaf 304734029) (.leaf 296580993)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 288661675) (.branch 92 (.leaf 280968568) (.leaf 273494447))) (.branch 95 (.branch 94 (.leaf 266232355) (.leaf 259175593)) (.branch 96 (.leaf 252317707) (.leaf 245652477)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 239173912) (.leaf 232876233)) (.branch 100 (.leaf 226753868) (.leaf 220801445))) (.branch 103 (.branch 102 (.leaf 215013778) (.leaf 209385866)) (.branch 104 (.leaf 203912880) (.leaf 198590160))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 193413204) (.leaf 188377666)) (.branch 108 (.leaf 183479346) (.leaf 178714187))) (.branch 111 (.branch 110 (.leaf 174078268) (.leaf 169567798)) (.branch 112 (.leaf 165179113) (.leaf 160908668)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 156753036) (.leaf 152708901)) (.branch 116 (.leaf 148773055) (.leaf 144942393))) (.branch 119 (.branch 118 (.leaf 141213909) (.leaf 137584693)) (.branch 120 (.leaf 134051929) (.leaf 130612889)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 9).prefactor = (3604342823579767/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 9).cutoff/(generalMeanRows 9).c)).2 =
    (353640040243591/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 9).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 9).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 9).q*(generalMeanRows 9).c/2-2 = (1/1:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable008.value]
    have hcontinuation : (generalMeanRows 9).q*(generalMeanRows 9).cutoff/2-2 = (25/11:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable004.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 9).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 9

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 9).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 9).criticalRate j.val*(generalMeanRows 9).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 9).c*(generalMeanRows 9).criticalPoint j.val)).2-
      (generalMeanRows 9).J/2-(generalMeanRows 9).error (generalMeanGrid j.val)+
      (generalMeanRows 9).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 9).c)).2-
      (generalMeanRows 9).J/2-(generalMeanRows 9).error 4 := by
  have he : (generalMeanRows 9).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 9) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 9)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0009

/-! Kernel-checked entropy margins for general spectral rectangle 10. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0010
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5996375698) (.branch 2 (.leaf 5800820339) (.leaf 5615151222))) (.branch 5 (.branch 4 (.leaf 5438725540) (.leaf 5270949263)) (.branch 6 (.leaf 5111272829) (.leaf 4959187296)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4814220882) (.leaf 4675935858)) (.branch 10 (.leaf 4543925741) (.leaf 4417812756))) (.branch 13 (.branch 12 (.leaf 4297245544) (.leaf 4181897070)) (.branch 14 (.leaf 4071462732) (.leaf 3965658632))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3864220000) (.branch 17 (.leaf 3766899754) (.leaf 3673467184))) (.branch 20 (.branch 19 (.leaf 3583706742) (.leaf 3497416938)) (.branch 21 (.leaf 3414409321) (.leaf 3334507544)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3257546503) (.leaf 3183371545)) (.branch 25 (.leaf 3111837733) (.leaf 3042809178))) (.branch 28 (.branch 27 (.leaf 2976158408) (.leaf 2911765794)) (.branch 29 (.leaf 2849519019) (.leaf 2789312580)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2731047333) (.branch 32 (.leaf 2674630068) (.leaf 2619973115))) (.branch 35 (.branch 34 (.leaf 2566993980) (.leaf 2515615003)) (.branch 36 (.leaf 2465763045) (.leaf 2417369195)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2370368496) (.leaf 2324699691)) (.branch 40 (.leaf 2280304991) (.leaf 2237129847))) (.branch 43 (.branch 42 (.leaf 2195122752) (.leaf 2154235049)) (.branch 44 (.leaf 2114420749) (.leaf 2075636367))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2037840770) (.branch 47 (.leaf 2000995025) (.leaf 1965062271))) (.branch 50 (.branch 49 (.leaf 1930007590) (.leaf 1895797886)) (.branch 51 (.leaf 1862401779) (.leaf 1829789501)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1797932797) (.leaf 1766804837)) (.branch 55 (.leaf 1736380132) (.leaf 1706634452))) (.branch 58 (.branch 57 (.leaf 1677544757) (.leaf 1649089122)) (.branch 59 (.leaf 1621246676) (.leaf 1593997540))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1567322768) (.branch 62 (.leaf 1541204300) (.leaf 1515624902))) (.branch 65 (.branch 64 (.leaf 1490568128) (.leaf 1466018271)) (.branch 66 (.leaf 1441960324) (.leaf 1418379938)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1395263389) (.leaf 1372597544)) (.branch 70 (.leaf 1350369824) (.leaf 1328568179))) (.branch 73 (.branch 72 (.leaf 1307181057) (.leaf 1286197380)) (.branch 74 (.leaf 1265606514) (.leaf 1245398250))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1225562781) (.branch 77 (.leaf 1206090678) (.leaf 1186972875))) (.branch 80 (.branch 79 (.leaf 1168200648) (.leaf 1149765596)) (.branch 81 (.leaf 1131659628) (.leaf 1113874946)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1096404030) (.leaf 1079239626)) (.branch 85 (.leaf 1062374731) (.leaf 1045802581))) (.branch 88 (.branch 87 (.leaf 1029516642) (.leaf 1013510597)) (.branch 89 (.leaf 997778335) (.leaf 982313943)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 967111699) (.branch 92 (.leaf 952166057) (.leaf 937471645))) (.branch 95 (.branch 94 (.leaf 923023255) (.leaf 908815835)) (.branch 96 (.leaf 894844484) (.leaf 881104445)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 867591095) (.leaf 854299947)) (.branch 100 (.leaf 841226636) (.leaf 828366921))) (.branch 103 (.branch 102 (.leaf 815716675) (.leaf 803271883)) (.branch 104 (.leaf 791028636) (.leaf 778983129))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 767131654) (.leaf 755470598)) (.branch 108 (.leaf 743996441) (.leaf 732705748))) (.branch 111 (.branch 110 (.leaf 721595170) (.leaf 710661439)) (.branch 112 (.leaf 699901366) (.leaf 689311839)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 678889815) (.leaf 668632325)) (.branch 116 (.leaf 658536468) (.leaf 648599407))) (.branch 119 (.branch 118 (.leaf 638818369) (.leaf 629190644)) (.branch 120 (.leaf 619713580) (.leaf 610384584)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 10).prefactor = (2952209633110281/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 10).cutoff/(generalMeanRows 10).c)).2 =
    (549046836586203/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 10).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 10).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 10).q*(generalMeanRows 10).c/2-2 = (117/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable009.value]
    have hcontinuation : (generalMeanRows 10).q*(generalMeanRows 10).cutoff/2-2 = (52/21:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable010.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 10).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 10

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 10).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 10).criticalRate j.val*(generalMeanRows 10).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 10).c*(generalMeanRows 10).criticalPoint j.val)).2-
      (generalMeanRows 10).J/2-(generalMeanRows 10).error (generalMeanGrid j.val)+
      (generalMeanRows 10).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 10).c)).2-
      (generalMeanRows 10).J/2-(generalMeanRows 10).error 4 := by
  have he : (generalMeanRows 10).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 10) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 10)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0010

/-! Kernel-checked entropy margins for general spectral rectangle 11. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0011
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6038494422) (.branch 2 (.leaf 5837374025) (.leaf 5646435608))) (.branch 5 (.branch 4 (.leaf 5465018444) (.leaf 5292511906)) (.branch 6 (.leaf 5128351052) (.leaf 4972012662)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4823011690) (.leaf 4680898065)) (.branch 10 (.leaf 4545253813) (.leaf 4415690447))) (.branch 13 (.branch 12 (.leaf 4291846612) (.leaf 4173385939)) (.branch 14 (.leaf 4059995100) (.leaf 3951382032))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3847274319) (.branch 17 (.leaf 3747417716) (.leaf 3651574791))) (.branch 20 (.branch 19 (.leaf 3559523691) (.leaf 3471056999)) (.branch 21 (.leaf 3385980696) (.leaf 3304113194)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3225284457) (.leaf 3149335184)) (.branch 25 (.leaf 3076116061) (.leaf 3005487064))) (.branch 28 (.branch 27 (.leaf 2937316821) (.leaf 2871482020)) (.branch 29 (.leaf 2807866860) (.leaf 2746362546)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2686866816) (.branch 32 (.leaf 2629283509) (.leaf 2573522159))) (.branch 35 (.branch 34 (.leaf 2519497618) (.leaf 2467129713)) (.branch 36 (.leaf 2416342917) (.leaf 2367066050)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2319232000) (.leaf 2272777462)) (.branch 40 (.leaf 2227642695) (.leaf 2183771295))) (.branch 43 (.branch 42 (.leaf 2141109988) (.leaf 2099608429)) (.branch 44 (.leaf 2059219025) (.leaf 2019896758))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1981599029) (.branch 47 (.leaf 1944285512) (.leaf 1907918009))) (.branch 50 (.branch 49 (.leaf 1872460323) (.leaf 1837878140)) (.branch 51 (.leaf 1804138911) (.leaf 1771211749)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1739067327) (.leaf 1707677788)) (.branch 55 (.leaf 1677016659) (.leaf 1647058766))) (.branch 58 (.branch 57 (.leaf 1617780161) (.leaf 1589158049)) (.branch 59 (.leaf 1561170723) (.leaf 1533797502))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1507018668) (.branch 62 (.leaf 1480815417) (.leaf 1455169801))) (.branch 65 (.branch 64 (.leaf 1430064688) (.leaf 1405483707)) (.branch 66 (.leaf 1381411214) (.leaf 1357832247)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1334732489) (.leaf 1312098235)) (.branch 70 (.leaf 1289916357) (.leaf 1268174274))) (.branch 73 (.branch 72 (.leaf 1246859921) (.leaf 1225961724)) (.branch 74 (.leaf 1205468572) (.leaf 1185369795))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1165655139) (.branch 77 (.leaf 1146314745) (.leaf 1127339129))) (.branch 80 (.branch 79 (.leaf 1108719165) (.leaf 1090446062)) (.branch 81 (.leaf 1072511352) (.leaf 1054906874)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1037624753) (.leaf 1020657393)) (.branch 85 (.leaf 1003997462) (.leaf 987637875))) (.branch 88 (.branch 87 (.leaf 971571787) (.leaf 955792581)) (.branch 89 (.leaf 940293856) (.leaf 925069416)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 910113265) (.branch 92 (.leaf 895419594) (.leaf 880982772))) (.branch 95 (.branch 94 (.leaf 866797344) (.leaf 852858016)) (.branch 96 (.leaf 839159653) (.leaf 825697270)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 812466026) (.leaf 799461219)) (.branch 100 (.leaf 786678278) (.leaf 774112761))) (.branch 103 (.branch 102 (.leaf 761760346) (.leaf 749616829)) (.branch 104 (.leaf 737678118) (.leaf 725940231))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 714399286) (.leaf 703051504)) (.branch 108 (.leaf 691893201) (.leaf 680920787))) (.branch 111 (.branch 110 (.leaf 670130758) (.leaf 659519701)) (.branch 112 (.leaf 649084280) (.leaf 638821244)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 628727416) (.leaf 618799695)) (.branch 116 (.leaf 609035053) (.leaf 599430530))) (.branch 119 (.branch 118 (.leaf 589983233) (.leaf 580690335)) (.branch 120 (.leaf 571549073) (.leaf 562556743)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 11).prefactor = (1215676435184223/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 11).cutoff/(generalMeanRows 11).c)).2 =
    (107692945451133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 11).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 11).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 11).q*(generalMeanRows 11).c/2-2 = (49/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable011.value]
    have hcontinuation : (generalMeanRows 11).q*(generalMeanRows 11).cutoff/2-2 = (52/21:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable010.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 11).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 11

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 11).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 11).criticalRate j.val*(generalMeanRows 11).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 11).c*(generalMeanRows 11).criticalPoint j.val)).2-
      (generalMeanRows 11).J/2-(generalMeanRows 11).error (generalMeanGrid j.val)+
      (generalMeanRows 11).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 11).c)).2-
      (generalMeanRows 11).J/2-(generalMeanRows 11).error 4 := by
  have he : (generalMeanRows 11).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 11) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 11)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0011

/-! Kernel-checked entropy margins for general spectral rectangle 12. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0012
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6216407611) (.branch 2 (.leaf 6009361570) (.leaf 5812797502))) (.branch 5 (.branch 4 (.leaf 5626035212) (.leaf 5448446085)) (.branch 6 (.leaf 5279448532) (.leaf 5118503917)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4965112904) (.leaf 4818812161)) (.branch 10 (.leaf 4679171399) (.leaf 4545790686))) (.branch 13 (.branch 12 (.leaf 4418298019) (.leaf 4296347120)) (.branch 14 (.leaf 4179615427) (.leaf 4067802273))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3960627217) (.branch 17 (.leaf 3857828522) (.leaf 3759161761))) (.branch 20 (.branch 19 (.leaf 3664398543) (.leaf 3573325343)) (.branch 21 (.leaf 3485742422) (.leaf 3401462843)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3320311562) (.leaf 3242124583)) (.branch 25 (.leaf 3166748192) (.leaf 3094038241))) (.branch 28 (.branch 27 (.leaf 3023859487) (.leaf 2956084984)) (.branch 29 (.leaf 2890595519) (.leaf 2827279093)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2766030430) (.branch 32 (.leaf 2706750537) (.leaf 2649346280))) (.branch 35 (.branch 34 (.leaf 2593730005) (.leaf 2539819175)) (.branch 36 (.leaf 2487536039) (.leaf 2436807320)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2387563927) (.leaf 2339740692)) (.branch 40 (.leaf 2293276111) (.leaf 2248112121))) (.branch 43 (.branch 42 (.leaf 2204193876) (.leaf 2161469550)) (.branch 44 (.leaf 2119890145) (.leaf 2079409320))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2039983219) (.branch 47 (.leaf 2001570327) (.leaf 1964131321))) (.branch 50 (.branch 49 (.leaf 1927628940) (.leaf 1892027857)) (.branch 51 (.leaf 1857294563) (.leaf 1823397262)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1790305763) (.leaf 1757991390)) (.branch 55 (.leaf 1726426886) (.leaf 1695586339))) (.branch 58 (.branch 57 (.leaf 1665445093) (.leaf 1635979683)) (.branch 59 (.leaf 1607167762) (.leaf 1578988039))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1551420216) (.branch 62 (.leaf 1524444933) (.leaf 1498043717))) (.branch 65 (.branch 64 (.leaf 1472198927) (.leaf 1446893713)) (.branch 66 (.leaf 1422111968) (.leaf 1397838290)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1374057940) (.leaf 1350756809)) (.branch 70 (.leaf 1327921382) (.leaf 1305538708))) (.branch 73 (.branch 72 (.leaf 1283596367) (.leaf 1262082443)) (.branch 74 (.leaf 1240985498) (.leaf 1220294547))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1199999035) (.branch 77 (.leaf 1180088811) (.leaf 1160554114))) (.branch 80 (.branch 79 (.leaf 1141385546) (.leaf 1122574060)) (.branch 81 (.leaf 1104110937) (.leaf 1085987774)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1068196467) (.leaf 1050729196)) (.branch 85 (.leaf 1033578410) (.leaf 1016736818))) (.branch 88 (.branch 87 (.leaf 1000197372) (.leaf 983953261)) (.branch 89 (.leaf 967997894) (.leaf 952324894)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 936928087) (.branch 92 (.leaf 921801494) (.leaf 906939318))) (.branch 95 (.branch 94 (.leaf 892335942) (.leaf 877985917)) (.branch 96 (.leaf 863883957) (.leaf 850024929)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 836403851) (.leaf 823015881)) (.branch 100 (.leaf 809856314) (.leaf 796920577))) (.branch 103 (.branch 102 (.leaf 784204220) (.leaf 771702917)) (.branch 104 (.leaf 759412454) (.leaf 747328731))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 735447753) (.leaf 723765630)) (.branch 108 (.leaf 712278568) (.leaf 700982872))) (.branch 111 (.branch 110 (.leaf 689874935) (.leaf 678951242)) (.branch 112 (.leaf 668208361) (.leaf 657642943)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 647251719) (.leaf 637031496)) (.branch 116 (.leaf 626979157) (.leaf 617091653))) (.branch 119 (.branch 118 (.leaf 607366009) (.leaf 597799313)) (.branch 120 (.leaf 588388721) (.leaf 579131449)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 12).prefactor = (6257470584436529/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 12).cutoff/(generalMeanRows 12).c)).2 =
    (107692945451133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 12).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 12).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 12).q*(generalMeanRows 12).c/2-2 = (49/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable011.value]
    have hcontinuation : (generalMeanRows 12).q*(generalMeanRows 12).cutoff/2-2 = (52/21:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable010.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 12).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 12

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 12).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 12).criticalRate j.val*(generalMeanRows 12).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 12).c*(generalMeanRows 12).criticalPoint j.val)).2-
      (generalMeanRows 12).J/2-(generalMeanRows 12).error (generalMeanGrid j.val)+
      (generalMeanRows 12).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 12).c)).2-
      (generalMeanRows 12).J/2-(generalMeanRows 12).error 4 := by
  have he : (generalMeanRows 12).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 12) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 12)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0012

/-! Kernel-checked entropy margins for general spectral rectangle 13. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0013
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6261045034) (.branch 2 (.leaf 6048194331) (.leaf 5846138953))) (.branch 5 (.branch 4 (.leaf 5654179661) (.leaf 5471670209)) (.branch 6 (.leaf 5298012664) (.leaf 5132653215)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4975078426) (.leaf 4824811845)) (.branch 10 (.leaf 4681410965) (.leaf 4544464463))) (.branch 13 (.branch 12 (.leaf 4413589704) (.leaf 4288430481)) (.branch 14 (.leaf 4168654949) (.leaf 4053953755))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3944038321) (.branch 17 (.leaf 3838639286) (.leaf 3737505071))) (.branch 20 (.branch 19 (.leaf 3640400570) (.leaf 3547105950)) (.branch 21 (.leaf 3457415543) (.leaf 3371136834)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3288089522) (.leaf 3208104667)) (.branch 25 (.leaf 3131023888) (.leaf 3056698635))) (.branch 28 (.branch 27 (.leaf 2984989511) (.leaf 2915765647)) (.branch 29 (.leaf 2848904120) (.leaf 2784289422)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2721812957) (.branch 32 (.leaf 2661372589) (.leaf 2602872204))) (.branch 35 (.branch 34 (.leaf 2546221326) (.leaf 2491334737)) (.branch 36 (.leaf 2438132144) (.leaf 2386537855)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2336480485) (.leaf 2287892683)) (.branch 40 (.leaf 2240710872) (.leaf 2194875012))) (.branch 43 (.branch 42 (.leaf 2150328376) (.leaf 2107017347)) (.branch 44 (.leaf 2064891217) (.leaf 2023902016))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1984004333) (.branch 47 (.leaf 1945155168) (.leaf 1907313781))) (.branch 50 (.branch 49 (.leaf 1870441555) (.leaf 1834501866)) (.branch 51 (.leaf 1799459967) (.leaf 1765282875)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1731939264) (.leaf 1699399368)) (.branch 55 (.leaf 1667634890) (.leaf 1636618916))) (.branch 58 (.branch 57 (.leaf 1606325832) (.leaf 1576731255)) (.branch 59 (.leaf 1547811953) (.leaf 1519545787))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1491911645) (.branch 62 (.leaf 1464889385) (.leaf 1438459779))) (.branch 65 (.branch 64 (.leaf 1412604464) (.leaf 1387305893)) (.branch 66 (.leaf 1362547290) (.leaf 1338312607)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1314586483) (.leaf 1291354213)) (.branch 70 (.leaf 1268601703) (.leaf 1246315446))) (.branch 73 (.branch 72 (.leaf 1224482487) (.leaf 1203090393)) (.branch 74 (.leaf 1182127227) (.leaf 1161581524))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1141442263) (.branch 77 (.leaf 1121698846) (.leaf 1102341077))) (.branch 80 (.branch 79 (.leaf 1083359142) (.leaf 1064743589)) (.branch 81 (.leaf 1046485310) (.leaf 1028575524)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1011005761) (.leaf 993767850)) (.branch 85 (.leaf 976853900) (.leaf 960256288))) (.branch 88 (.branch 87 (.leaf 943967650) (.leaf 927980865)) (.branch 89 (.leaf 912289044) (.leaf 896885521)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 881763843) (.branch 92 (.leaf 866917759) (.leaf 852341213))) (.branch 95 (.branch 94 (.leaf 838028334) (.leaf 823973428)) (.branch 96 (.leaf 810170969) (.leaf 796615598)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 783302107) (.leaf 770225441)) (.branch 100 (.leaf 757380686) (.leaf 744763065))) (.branch 103 (.branch 102 (.leaf 732367936) (.leaf 720190779)) (.branch 104 (.leaf 708227201) (.leaf 696472921))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 684923774) (.leaf 673575701)) (.branch 108 (.leaf 662424750) (.leaf 651467067))) (.branch 111 (.branch 110 (.leaf 640698896) (.leaf 630116574)) (.branch 112 (.leaf 619716527) (.leaf 609495270)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 599449401) (.leaf 589575598)) (.branch 116 (.leaf 579870619) (.leaf 570331296))) (.branch 119 (.branch 118 (.leaf 560954535) (.leaf 551737314)) (.branch 120 (.leaf 542676677) (.leaf 533769738)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 13).prefactor = (3220917752605343/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 13).cutoff/(generalMeanRows 13).c)).2 =
    (131998356847093/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 13).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 13).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 13).q*(generalMeanRows 13).c/2-2 = (16/25:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable012.value]
    have hcontinuation : (generalMeanRows 13).q*(generalMeanRows 13).cutoff/2-2 = (52/21:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable010.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 13).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 13

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 13).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 13).criticalRate j.val*(generalMeanRows 13).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 13).c*(generalMeanRows 13).criticalPoint j.val)).2-
      (generalMeanRows 13).J/2-(generalMeanRows 13).error (generalMeanGrid j.val)+
      (generalMeanRows 13).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 13).c)).2-
      (generalMeanRows 13).J/2-(generalMeanRows 13).error 4 := by
  have he : (generalMeanRows 13).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 13) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 13)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0013

/-! Kernel-checked entropy margins for general spectral rectangle 14. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0014
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6493154019) (.branch 2 (.leaf 6276890556) (.leaf 6071575711))) (.branch 5 (.branch 4 (.leaf 5876499006) (.leaf 5691003841)) (.branch 6 (.leaf 5514482736) (.leaf 5346373076)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5186153294) (.leaf 5033339431)) (.branch 10 (.leaf 4887482044) (.leaf 4748163394))) (.branch 13 (.branch 12 (.leaf 4614994919) (.leaf 4487614923)) (.branch 14 (.leaf 4365686487) (.leaf 4248895557))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4136949206) (.branch 17 (.leaf 4029574046) (.leaf 3926514769))) (.branch 20 (.branch 19 (.leaf 3827532816) (.leaf 3732405154)) (.branch 21 (.leaf 3640923155) (.leaf 3552891559)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3468127528) (.leaf 3386459766)) (.branch 25 (.leaf 3307727716) (.leaf 3231780812))) (.branch 28 (.branch 27 (.leaf 3158477791) (.leaf 3087686055)) (.branch 29 (.leaf 3019281084) (.leaf 2953145893)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2889170519) (.branch 32 (.leaf 2827251561) (.leaf 2767291742))) (.branch 35 (.branch 34 (.leaf 2709199502) (.leaf 2652888632)) (.branch 36 (.leaf 2598277919) (.leaf 2545290822)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2493855178) (.leaf 2443902914)) (.branch 40 (.leaf 2395369790) (.leaf 2348195158))) (.branch 43 (.branch 42 (.leaf 2302321729) (.leaf 2257695372)) (.branch 44 (.leaf 2214264906) (.leaf 2171981927))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2130800627) (.branch 47 (.leaf 2090677643) (.leaf 2051571902))) (.branch 50 (.branch 49 (.leaf 2013444482) (.leaf 1976258484)) (.branch 51 (.leaf 1939978909) (.leaf 1904572544)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1870007855) (.leaf 1836254887)) (.branch 55 (.leaf 1803285173) (.leaf 1771071644))) (.branch 58 (.branch 57 (.leaf 1739588549) (.leaf 1708811377)) (.branch 59 (.leaf 1678716787) (.leaf 1649282539))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1620487433) (.branch 62 (.leaf 1592311245) (.leaf 1564734681))) (.branch 65 (.branch 64 (.leaf 1537739315) (.leaf 1511307545)) (.branch 66 (.leaf 1485422549) (.leaf 1460068238)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1435229218) (.leaf 1410890751)) (.branch 70 (.leaf 1387038721) (.leaf 1363659599))) (.branch 73 (.branch 72 (.leaf 1340740413) (.leaf 1318268717)) (.branch 74 (.leaf 1296232564) (.leaf 1274620479))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1253421436) (.branch 77 (.leaf 1232624835) (.leaf 1212220479))) (.branch 80 (.branch 79 (.leaf 1192198551) (.leaf 1172549602)) (.branch 81 (.leaf 1153264524) (.leaf 1134334542)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1115751189) (.leaf 1097506297)) (.branch 85 (.leaf 1079591981) (.leaf 1062000622))) (.branch 88 (.branch 87 (.leaf 1044724862) (.leaf 1027757584)) (.branch 89 (.leaf 1011091905) (.leaf 994721164)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 978638911) (.branch 92 (.leaf 962838901) (.leaf 947315080))) (.branch 95 (.branch 94 (.leaf 932061581) (.leaf 917072712)) (.branch 96 (.leaf 902342951) (.leaf 887866937)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 873639466) (.leaf 859655481)) (.branch 100 (.leaf 845910067) (.leaf 832398448))) (.branch 103 (.branch 102 (.leaf 819115976) (.leaf 806058130)) (.branch 104 (.leaf 793220512) (.leaf 780598837))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 768188934) (.leaf 755986737)) (.branch 108 (.leaf 743988287) (.leaf 732189720))) (.branch 111 (.branch 110 (.leaf 720587273) (.leaf 709177271)) (.branch 112 (.leaf 697956130) (.leaf 686920354)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 676066526) (.leaf 665391312)) (.branch 116 (.leaf 654891456) (.leaf 644563774))) (.branch 119 (.branch 118 (.leaf 634405156) (.leaf 624412564)) (.branch 120 (.leaf 614583024) (.leaf 604913630)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 14).prefactor = (6536045062452579/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 14).cutoff/(generalMeanRows 14).c)).2 =
    (107692945451133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 14).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 14).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 14).q*(generalMeanRows 14).c/2-2 = (49/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable011.value]
    have hcontinuation : (generalMeanRows 14).q*(generalMeanRows 14).cutoff/2-2 = (52/21:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable010.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 14).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 14

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 14).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 14).criticalRate j.val*(generalMeanRows 14).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 14).c*(generalMeanRows 14).criticalPoint j.val)).2-
      (generalMeanRows 14).J/2-(generalMeanRows 14).error (generalMeanGrid j.val)+
      (generalMeanRows 14).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 14).c)).2-
      (generalMeanRows 14).J/2-(generalMeanRows 14).error 4 := by
  have he : (generalMeanRows 14).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 14) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 14)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0014

/-! Kernel-checked entropy margins for general spectral rectangle 15. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0015
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8481061156) (.branch 2 (.leaf 8167121097) (.leaf 7868168576))) (.branch 5 (.branch 4 (.leaf 7583331537) (.leaf 7311799800)) (.branch 6 (.leaf 7052819570) (.leaf 6805688554)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6569751607) (.leaf 6344396845)) (.branch 10 (.leaf 6129052146) (.leaf 5923182009))) (.branch 13 (.branch 12 (.leaf 5726284723) (.leaf 5537889797)) (.branch 14 (.leaf 5357555633) (.leaf 5184867419))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5019435197) (.branch 17 (.leaf 4860892108) (.leaf 4708892782))) (.branch 20 (.branch 19 (.leaf 4563111871) (.leaf 4423242692)) (.branch 21 (.leaf 4288995983) (.leaf 4160098766)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4036293282) (.leaf 3917336023)) (.branch 25 (.leaf 3802996829) (.leaf 3693058051))) (.branch 28 (.branch 27 (.leaf 3587313780) (.leaf 3485569127)) (.branch 29 (.leaf 3387639555) (.leaf 3293350260)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3202535593) (.branch 32 (.leaf 3115038518) (.leaf 3030710114))) (.branch 35 (.branch 34 (.leaf 2949409102) (.leaf 2871001409)) (.branch 36 (.leaf 2795359756) (.leaf 2722363276)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2651897154) (.leaf 2583852290)) (.branch 40 (.leaf 2518124985) (.leaf 2454616641))) (.branch 43 (.branch 42 (.leaf 2393233486) (.leaf 2333886312)) (.branch 44 (.leaf 2276490227) (.leaf 2220964429))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2167231981) (.branch 47 (.leaf 2115219615) (.leaf 2064857533))) (.branch 50 (.branch 49 (.leaf 2016079227) (.leaf 1968821309)) (.branch 51 (.leaf 1923023348) (.leaf 1878627718)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1835579455) (.leaf 1793826121)) (.branch 55 (.leaf 1753317675) (.leaf 1714006352))) (.branch 58 (.branch 57 (.leaf 1675846549) (.leaf 1638794718)) (.branch 59 (.leaf 1602809260) (.leaf 1567850433))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1533880255) (.branch 62 (.leaf 1500862422) (.leaf 1468762222))) (.branch 65 (.branch 64 (.leaf 1437546463) (.leaf 1407183390)) (.branch 66 (.leaf 1377642625) (.leaf 1348895094)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1320912967) (.leaf 1293669600)) (.branch 70 (.leaf 1267139475) (.leaf 1241298149))) (.branch 73 (.branch 72 (.leaf 1216122201) (.leaf 1191589187)) (.branch 74 (.leaf 1167677593) (.leaf 1144366789))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1121636991) (.branch 77 (.leaf 1099469222) (.leaf 1077845271))) (.branch 80 (.branch 79 (.leaf 1056747661) (.leaf 1036159617)) (.branch 81 (.leaf 1016065027) (.leaf 996448420)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 977294931) (.leaf 958590278)) (.branch 85 (.leaf 940320732) (.leaf 922473095))) (.branch 88 (.branch 87 (.leaf 905034674) (.leaf 887993263)) (.branch 89 (.leaf 871337113) (.leaf 855054923)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 839135811) (.branch 92 (.leaf 823569300) (.leaf 808345300))) (.branch 95 (.branch 94 (.leaf 793454090) (.leaf 778886304)) (.branch 96 (.leaf 764632914) (.leaf 750685216)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 737034817) (.leaf 723673622)) (.branch 100 (.leaf 710593818) (.leaf 697787868))) (.branch 103 (.branch 102 (.leaf 685248493) (.leaf 672968667)) (.branch 104 (.leaf 660941604) (.leaf 649160746))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 637619758) (.leaf 626312516)) (.branch 108 (.leaf 615233098) (.leaf 604375778))) (.branch 111 (.branch 110 (.leaf 593735017) (.leaf 583305456)) (.branch 112 (.leaf 573081906) (.leaf 563059348)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 553232917) (.leaf 543597904)) (.branch 116 (.leaf 534149746) (.leaf 524884022))) (.branch 119 (.branch 118 (.leaf 515796446) (.leaf 506882861)) (.branch 120 (.leaf 498139238) (.leaf 489561668)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 15).prefactor = (462875340602437/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 15).cutoff/(generalMeanRows 15).c)).2 =
    (23855065969551/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 15).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 15).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 15).q*(generalMeanRows 15).cutoff/2-2 = (159/85:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable013.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 15).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 15

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 15).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 15).criticalRate j.val*(generalMeanRows 15).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 15).c*(generalMeanRows 15).criticalPoint j.val)).2-
      (generalMeanRows 15).J/2-(generalMeanRows 15).error (generalMeanGrid j.val)+
      (generalMeanRows 15).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 15).c)).2-
      (generalMeanRows 15).J/2-(generalMeanRows 15).error 4 := by
  have he : (generalMeanRows 15).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 15) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 15)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0015

/-! Kernel-checked entropy margins for general spectral rectangle 16. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0016
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7174872853) (.branch 2 (.leaf 6861218683) (.leaf 6563216231))) (.branch 5 (.branch 4 (.leaf 6279951832) (.leaf 6010576630)) (.branch 6 (.leaf 5754300808) (.leaf 5510388462)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5278153036) (.leaf 5056953231)) (.branch 10 (.leaf 4846189351) (.leaf 4645299999))) (.branch 13 (.branch 12 (.leaf 4453759113) (.leaf 4271073275)) (.branch 14 (.leaf 4096779277) (.leaf 3930441908))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3771651941) (.branch 17 (.leaf 3620024291) (.leaf 3475196339))) (.branch 20 (.branch 19 (.leaf 3336826389) (.leaf 3204592257)) (.branch 21 (.leaf 3078189976) (.leaf 2957332595)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2841749083) (.leaf 2731183307)) (.branch 25 (.leaf 2625393098) (.leaf 2524149372))) (.branch 28 (.branch 27 (.leaf 2427235332) (.leaf 2334445711)) (.branch 29 (.leaf 2245586084) (.leaf 2160472214)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2078929455) (.branch 32 (.leaf 2000792186) (.leaf 1925903293))) (.branch 35 (.branch 34 (.leaf 1854113674) (.leaf 1785281789)) (.branch 36 (.leaf 1719273226) (.leaf 1655960308)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1595221711) (.leaf 1536942121)) (.branch 40 (.leaf 1481011902) (.leaf 1427326783))) (.branch 43 (.branch 42 (.leaf 1375787574) (.leaf 1326299893)) (.branch 44 (.leaf 1278773905) (.leaf 1233124087))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1189268996) (.branch 47 (.leaf 1147131060) (.leaf 1106636373))) (.branch 50 (.branch 49 (.leaf 1067714509) (.leaf 1030298339)) (.branch 51 (.leaf 994323868) (.leaf 959730070)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 926458739) (.leaf 894454351)) (.branch 55 (.leaf 863663926) (.leaf 834036901))) (.branch 58 (.branch 57 (.leaf 805525013) (.leaf 778082181)) (.branch 59 (.leaf 751664405) (.leaf 726229657))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 701737792) (.branch 62 (.leaf 678150451) (.leaf 655430978))) (.branch 65 (.branch 64 (.leaf 633544336) (.leaf 612457034)) (.branch 66 (.leaf 592137047) (.leaf 572553750)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 553677852) (.leaf 535481332)) (.branch 70 (.leaf 517937379) (.leaf 501020337))) (.branch 73 (.branch 72 (.leaf 484705650) (.leaf 468969813)) (.branch 74 (.leaf 453790320) (.leaf 439145619))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 425015071) (.branch 77 (.leaf 411378906) (.leaf 398218183))) (.branch 80 (.branch 79 (.leaf 385514753) (.leaf 373251224)) (.branch 81 (.leaf 361410924) (.leaf 349977874)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 338936752) (.leaf 328272864)) (.branch 85 (.leaf 317972121) (.leaf 308021005))) (.branch 88 (.branch 87 (.leaf 298406550) (.leaf 289116314)) (.branch 89 (.leaf 280138357) (.leaf 271461221)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 263073906) (.branch 92 (.leaf 254965850) (.leaf 247126913))) (.branch 95 (.branch 94 (.leaf 239547359) (.leaf 232217832)) (.branch 96 (.leaf 225129349) (.leaf 218273277)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 211641322) (.leaf 205225513)) (.branch 100 (.leaf 199018189) (.leaf 193011984))) (.branch 103 (.branch 102 (.leaf 187199818) (.leaf 181574882)) (.branch 104 (.leaf 176130628) (.leaf 170860760))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 165759218) (.leaf 160820175)) (.branch 108 (.leaf 156038022) (.leaf 151407362))) (.branch 111 (.branch 110 (.leaf 146923002) (.leaf 142579940)) (.branch 112 (.leaf 138373364) (.leaf 134298638)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 130351300) (.leaf 126527050)) (.branch 116 (.leaf 122821748) (.leaf 119231405))) (.branch 119 (.branch 118 (.leaf 115752179) (.leaf 112380365)) (.branch 120 (.leaf 109112396) (.leaf 105944831)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 16).prefactor = (7863351962948147/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 16).cutoff/(generalMeanRows 16).c)).2 =
    (9366996736169/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 16).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 16).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 16).q*(generalMeanRows 16).c/2-2 = (17/16:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable002.value]
    have hcontinuation : (generalMeanRows 16).q*(generalMeanRows 16).cutoff/2-2 = (159/85:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable013.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 16).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 16

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 16).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 16).criticalRate j.val*(generalMeanRows 16).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 16).c*(generalMeanRows 16).criticalPoint j.val)).2-
      (generalMeanRows 16).J/2-(generalMeanRows 16).error (generalMeanGrid j.val)+
      (generalMeanRows 16).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 16).c)).2-
      (generalMeanRows 16).J/2-(generalMeanRows 16).error 4 := by
  have he : (generalMeanRows 16).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 16) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 16)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0016

/-! Kernel-checked entropy margins for general spectral rectangle 17. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0017
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6756176856) (.branch 2 (.leaf 6543658204) (.leaf 6341540418))) (.branch 5 (.branch 4 (.leaf 6149183406) (.leaf 5965993558)) (.branch 6 (.leaf 5791419685) (.leaf 5624949405)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5466105893) (.leaf 5314444971)) (.branch 10 (.leaf 5169552482) (.leaf 5031041921))) (.branch 13 (.branch 12 (.leaf 4898552288) (.leaf 4771746143)) (.branch 14 (.leaf 4650307834) (.leaf 4533941885))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4422371524) (.branch 17 (.leaf 4315337335) (.leaf 4212596024))) (.branch 20 (.branch 19 (.leaf 4113919291) (.leaf 4019092786)) (.branch 21 (.leaf 3927915154) (.leaf 3840197151)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3755760835) (.leaf 3674438811)) (.branch 25 (.leaf 3596073537) (.leaf 3520516681))) (.branch 28 (.branch 27 (.leaf 3447628525) (.leaf 3377277414)) (.branch 29 (.leaf 3309339238) (.leaf 3243696961)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3180240176) (.branch 32 (.leaf 3118864688) (.leaf 3059472137))) (.branch 35 (.branch 34 (.leaf 3001969633) (.leaf 2946269428)) (.branch 36 (.leaf 2892288599) (.leaf 2839948761)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2789175794) (.leaf 2739899587)) (.branch 40 (.leaf 2692053804) (.leaf 2645575658))) (.branch 43 (.branch 42 (.leaf 2600405704) (.leaf 2556487644)) (.branch 44 (.leaf 2513768146) (.leaf 2472196670))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2431725307) (.branch 47 (.leaf 2392308633) (.leaf 2353903560))) (.branch 50 (.branch 49 (.leaf 2316469211) (.leaf 2279966790)) (.branch 51 (.leaf 2244359466) (.leaf 2209612262)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2175691957) (.leaf 2142566979)) (.branch 55 (.leaf 2110207322) (.leaf 2078584455))) (.branch 58 (.branch 57 (.leaf 2047671244) (.leaf 2017441870)) (.branch 59 (.leaf 1987871767) (.leaf 1958937542))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1930616922) (.branch 62 (.leaf 1902888687) (.leaf 1875732616))) (.branch 65 (.branch 64 (.leaf 1849129435) (.leaf 1823060762)) (.branch 66 (.leaf 1797509064) (.leaf 1772457611)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1747890431) (.leaf 1723792274)) (.branch 70 (.leaf 1700148572) (.leaf 1676945404))) (.branch 73 (.branch 72 (.leaf 1654169463) (.leaf 1631808023)) (.branch 74 (.leaf 1609848909) (.leaf 1588280472))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1567091558) (.branch 77 (.leaf 1546271483) (.leaf 1525810013))) (.branch 80 (.branch 79 (.leaf 1505697339) (.leaf 1485924053)) (.branch 81 (.leaf 1466481132) (.leaf 1447359919)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1428552100) (.leaf 1410049692)) (.branch 85 (.leaf 1391845025) (.leaf 1373930726))) (.branch 88 (.branch 87 (.leaf 1356299706) (.leaf 1338945145)) (.branch 89 (.leaf 1321860479) (.leaf 1305039389)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1288475788) (.branch 92 (.leaf 1272163810) (.leaf 1256097802))) (.branch 95 (.branch 94 (.leaf 1240272309) (.leaf 1224682072)) (.branch 96 (.leaf 1209322010) (.leaf 1194187220)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1179272964) (.leaf 1164574663)) (.branch 100 (.leaf 1150087889) (.leaf 1135808361))) (.branch 103 (.branch 102 (.leaf 1121731933) (.leaf 1107854593)) (.branch 104 (.leaf 1094172456) (.leaf 1080681757))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1067378847) (.leaf 1054260186)) (.branch 108 (.leaf 1041322341) (.leaf 1028561981))) (.branch 111 (.branch 110 (.leaf 1015975871) (.leaf 1003560870)) (.branch 112 (.leaf 991313924) (.leaf 979232066)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 967312412) (.leaf 955552153)) (.branch 116 (.leaf 943948560) (.leaf 932498974))) (.branch 119 (.branch 118 (.leaf 921200804) (.leaf 910051530)) (.branch 120 (.leaf 899048692) (.leaf 888189894)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 17).prefactor = (1412623381930827/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 17).cutoff/(generalMeanRows 17).c)).2 =
    (2088952063271/4000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 17).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 17).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 17).q*(generalMeanRows 17).c/2-2 = (23/50:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable014.value]
    have hcontinuation : (generalMeanRows 17).q*(generalMeanRows 17).cutoff/2-2 = (73/34:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable015.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 17).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 17

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 17).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 17).criticalRate j.val*(generalMeanRows 17).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 17).c*(generalMeanRows 17).criticalPoint j.val)).2-
      (generalMeanRows 17).J/2-(generalMeanRows 17).error (generalMeanGrid j.val)+
      (generalMeanRows 17).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 17).c)).2-
      (generalMeanRows 17).J/2-(generalMeanRows 17).error 4 := by
  have he : (generalMeanRows 17).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 17) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 17)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0017

/-! Kernel-checked entropy margins for general spectral rectangle 18. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0018
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6870081346) (.branch 2 (.leaf 6649124418) (.leaf 6438977321))) (.branch 5 (.branch 4 (.leaf 6238976021) (.leaf 6048504698)) (.branch 6 (.leaf 5866991534) (.leaf 5693904958)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5528750277) (.leaf 5371066656)) (.branch 10 (.leaf 5220424393) (.leaf 5076422459))) (.branch 13 (.branch 12 (.leaf 4938686275) (.leaf 4806865689)) (.branch 14 (.leaf 4680633141) (.leaf 4559681993))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4443724995) (.branch 17 (.leaf 4332492895) (.leaf 4225733156))) (.branch 20 (.branch 19 (.leaf 4123208782) (.leaf 4024697243)) (.branch 21 (.leaf 3929989478) (.leaf 3838888987)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3751210981) (.leaf 3666781606)) (.branch 25 (.leaf 3585437225) (.leaf 3507023745))) (.branch 28 (.branch 27 (.leaf 3431396007) (.leaf 3358417208)) (.branch 29 (.leaf 3287958370) (.leaf 3219897846)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3154120862) (.branch 32 (.leaf 3090519086) (.leaf 3028990234))) (.branch 35 (.branch 34 (.leaf 2969437695) (.leaf 2911770189)) (.branch 36 (.leaf 2855901439) (.leaf 2801749875)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2749238346) (.leaf 2698293864)) (.branch 40 (.leaf 2648847352) (.leaf 2600833415))) (.branch 43 (.branch 42 (.leaf 2554190126) (.leaf 2508858821)) (.branch 44 (.leaf 2464783912) (.leaf 2421912710))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2380195255) (.branch 47 (.leaf 2339584164) (.leaf 2300034482))) (.branch 50 (.branch 49 (.leaf 2261503544) (.leaf 2223950847)) (.branch 51 (.leaf 2187337929) (.leaf 2151628253)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2116787102) (.leaf 2082781476)) (.branch 55 (.leaf 2049579998) (.leaf 2017152825))) (.branch 58 (.branch 57 (.leaf 1985471562) (.leaf 1954509188)) (.branch 59 (.leaf 1924239974) (.leaf 1894639419))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1865684181) (.branch 62 (.leaf 1837352016) (.leaf 1809621716))) (.branch 65 (.branch 64 (.leaf 1782473061) (.leaf 1755886757)) (.branch 66 (.leaf 1729844394) (.leaf 1704328397)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1679321983) (.leaf 1654809118)) (.branch 70 (.leaf 1630774479) (.leaf 1607203417))) (.branch 73 (.branch 72 (.leaf 1584081924) (.leaf 1561396596)) (.branch 74 (.leaf 1539134605) (.leaf 1517283669))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1495832026) (.branch 77 (.leaf 1474768403) (.leaf 1454081996))) (.branch 80 (.branch 79 (.leaf 1433762443) (.leaf 1413799807)) (.branch 81 (.leaf 1394184549) (.leaf 1374907510)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1355959896) (.leaf 1337333255)) (.branch 85 (.leaf 1319019463) (.leaf 1301010710))) (.branch 88 (.branch 87 (.leaf 1283299478) (.leaf 1265878535)) (.branch 89 (.leaf 1248740917) (.leaf 1231879915)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1215289066) (.branch 92 (.leaf 1198962137) (.leaf 1182893119))) (.branch 95 (.branch 94 (.leaf 1167076213) (.leaf 1151505821)) (.branch 96 (.leaf 1136176538) (.leaf 1121083144)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1106220591) (.leaf 1091584002)) (.branch 100 (.leaf 1077168656) (.leaf 1062969987))) (.branch 103 (.branch 102 (.leaf 1048983575) (.leaf 1035205139)) (.branch 104 (.leaf 1021630531) (.leaf 1008255732))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 995076843) (.leaf 982090084)) (.branch 108 (.leaf 969291787) (.leaf 956678390))) (.branch 111 (.branch 110 (.leaf 944246435) (.leaf 931992562)) (.branch 112 (.leaf 919913506) (.leaf 908006092)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 896267233) (.leaf 884693925)) (.branch 116 (.leaf 873283245) (.leaf 862032347))) (.branch 119 (.branch 118 (.leaf 850938458) (.leaf 839998877)) (.branch 120 (.leaf 829210973) (.leaf 818572179)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 18).prefactor = (5874479270049839/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 18).cutoff/(generalMeanRows 18).c)).2 =
    (102023331057081/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 18).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 18).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 18).q*(generalMeanRows 18).c/2-2 = (49/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable003.value]
    have hcontinuation : (generalMeanRows 18).q*(generalMeanRows 18).cutoff/2-2 = (73/34:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable015.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 18).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 18

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 18).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 18).criticalRate j.val*(generalMeanRows 18).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 18).c*(generalMeanRows 18).criticalPoint j.val)).2-
      (generalMeanRows 18).J/2-(generalMeanRows 18).error (generalMeanGrid j.val)+
      (generalMeanRows 18).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 18).c)).2-
      (generalMeanRows 18).J/2-(generalMeanRows 18).error 4 := by
  have he : (generalMeanRows 18).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 18) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 18)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0018

/-! Kernel-checked entropy margins for general spectral rectangle 19. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0019
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6987340764) (.branch 2 (.leaf 6757724581) (.leaf 6539343807))) (.branch 5 (.branch 4 (.leaf 6331509480) (.leaf 6133582649)) (.branch 6 (.leaf 5944970012) (.leaf 5765120010)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5593519336) (.leaf 5429689799)) (.branch 10 (.leaf 5273185496) (.leaf 5123590261))) (.branch 13 (.branch 12 (.leaf 4980515360) (.leaf 4843597387)) (.branch 14 (.leaf 4712496368) (.leaf 4586894018))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4466492163) (.branch 17 (.leaf 4351011286) (.leaf 4240189203))) (.branch 20 (.branch 19 (.leaf 4133779848) (.leaf 4031552148)) (.branch 21 (.leaf 3933289001) (.leaf 3838786325)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3747852182) (.leaf 3660305972)) (.branch 25 (.leaf 3575977688) (.leaf 3494707221))) (.branch 28 (.branch 27 (.leaf 3416343722) (.leaf 3340745007)) (.branch 29 (.leaf 3267777009) (.leaf 3197313259)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3129234416) (.branch 32 (.leaf 3063427821) (.leaf 2999787085))) (.branch 35 (.branch 34 (.leaf 2938211703) (.leaf 2878606698)) (.branch 36 (.leaf 2820882284) (.leaf 2764953554)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2710740189) (.leaf 2658166183)) (.branch 40 (.leaf 2607159591) (.leaf 2557652288))) (.branch 43 (.branch 42 (.leaf 2509579745) (.leaf 2462880820)) (.branch 44 (.leaf 2417497564) (.leaf 2373375034))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2330461123) (.branch 47 (.leaf 2288706394) (.leaf 2248063935))) (.branch 50 (.branch 49 (.leaf 2208489210) (.leaf 2169939927)) (.branch 51 (.leaf 2132375915) (.leaf 2095759001)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2060052902) (.leaf 2025223121)) (.branch 55 (.leaf 1991236845) (.leaf 1958062857))) (.branch 58 (.branch 57 (.leaf 1925671444) (.leaf 1894034320)) (.branch 59 (.leaf 1863124544) (.leaf 1832916453))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1803385586) (.branch 62 (.leaf 1774508627) (.leaf 1746263338))) (.branch 65 (.branch 64 (.leaf 1718628506) (.leaf 1691583885)) (.branch 66 (.leaf 1665110148) (.leaf 1639188840)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1613802325) (.leaf 1588933755)) (.branch 70 (.leaf 1564567016) (.leaf 1540686703))) (.branch 73 (.branch 72 (.leaf 1517278073) (.leaf 1494327017)) (.branch 74 (.leaf 1471820026) (.leaf 1449744161))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1428087024) (.branch 77 (.leaf 1406836731) (.leaf 1385981884))) (.branch 80 (.branch 79 (.leaf 1365511551) (.leaf 1345415240)) (.branch 81 (.leaf 1325682877) (.leaf 1306304787)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1287271674) (.leaf 1268574603)) (.branch 85 (.leaf 1250204980) (.leaf 1232154540))) (.branch 88 (.branch 87 (.leaf 1214415326) (.leaf 1196979681)) (.branch 89 (.leaf 1179840224) (.leaf 1162989850)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1146421703) (.branch 92 (.leaf 1130129176) (.leaf 1114105894))) (.branch 95 (.branch 94 (.leaf 1098345701) (.leaf 1082842658)) (.branch 96 (.leaf 1067591025) (.leaf 1052585255)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1037819988) (.leaf 1023290037)) (.branch 100 (.leaf 1008990387) (.leaf 994916180))) (.branch 103 (.branch 102 (.leaf 981062717) (.leaf 967425442)) (.branch 104 (.leaf 953999942) (.leaf 940781938))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 927767283) (.leaf 914951949)) (.branch 108 (.leaf 902332032) (.leaf 889903737))) (.branch 111 (.branch 110 (.leaf 877663382) (.leaf 865607386)) (.branch 112 (.leaf 853732271) (.leaf 842034656)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 830511248) (.leaf 819158849)) (.branch 116 (.leaf 807974342) (.leaf 796954694))) (.branch 119 (.branch 118 (.leaf 786096951) (.leaf 775398233)) (.branch 120 (.leaf 764855736) (.leaf 754466725)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 19).prefactor = (1526835953573329/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 19).cutoff/(generalMeanRows 19).c)).2 =
    (498140464238691/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 19).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 19).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 19).q*(generalMeanRows 19).c/2-2 = (13/25:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable005.value]
    have hcontinuation : (generalMeanRows 19).q*(generalMeanRows 19).cutoff/2-2 = (73/34:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable015.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 19).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 19

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 19).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 19).criticalRate j.val*(generalMeanRows 19).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 19).c*(generalMeanRows 19).criticalPoint j.val)).2-
      (generalMeanRows 19).J/2-(generalMeanRows 19).error (generalMeanGrid j.val)+
      (generalMeanRows 19).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 19).c)).2-
      (generalMeanRows 19).J/2-(generalMeanRows 19).error 4 := by
  have he : (generalMeanRows 19).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 19) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 19)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0019

/-! Kernel-checked entropy margins for general spectral rectangle 20. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0020
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7264319173) (.branch 2 (.leaf 7025600997) (.leaf 6798563603))) (.branch 5 (.branch 4 (.leaf 6582490716) (.leaf 6376718060)) (.branch 6 (.leaf 6180628812) (.leaf 5993649550)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5815246620) (.leaf 5644922875)) (.branch 10 (.leaf 5482214736) (.leaf 5326689542))) (.branch 13 (.branch 12 (.leaf 5177943146) (.leaf 5035597741)) (.branch 14 (.leaf 4899299873) (.leaf 4768718642))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4643544054) (.branch 17 (.leaf 4523485511) (.leaf 4408270437))) (.branch 20 (.branch 19 (.leaf 4297643012) (.leaf 4191363003)) (.branch 21 (.leaf 4089204702) (.leaf 3990955937)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3896417161) (.leaf 3805400617)) (.branch 25 (.leaf 3717729557) (.leaf 3633237526))) (.branch 28 (.branch 27 (.leaf 3551767695) (.leaf 3473172245)) (.branch 29 (.leaf 3397311793) (.leaf 3324054858)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3253277367) (.branch 32 (.leaf 3184862197) (.leaf 3118698740))) (.branch 35 (.branch 34 (.leaf 3054682508) (.leaf 2992714759)) (.branch 36 (.leaf 2932702147) (.leaf 2874556401)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2818194016) (.leaf 2763535975)) (.branch 40 (.leaf 2710507480) (.leaf 2659037706))) (.branch 43 (.branch 42 (.leaf 2609059565) (.leaf 2560509494)) (.branch 44 (.leaf 2513327244) (.leaf 2467455696))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2422840675) (.branch 47 (.leaf 2379430788) (.leaf 2337177261))) (.branch 50 (.branch 49 (.leaf 2296033792) (.leaf 2255956415)) (.branch 51 (.leaf 2216903364) (.leaf 2178834954)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2141713465) (.leaf 2105503030)) (.branch 55 (.leaf 2070169537) (.leaf 2035680530))) (.branch 58 (.branch 57 (.leaf 2002005121) (.leaf 1969113900)) (.branch 59 (.leaf 1936978860) (.leaf 1905573319))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1874871848) (.branch 62 (.leaf 1844850205) (.leaf 1815485272))) (.branch 65 (.branch 64 (.leaf 1786754994) (.leaf 1758638323)) (.branch 66 (.leaf 1731115167) (.leaf 1704166337)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1677773501) (.leaf 1651919139)) (.branch 70 (.leaf 1626586502) (.leaf 1601759573))) (.branch 73 (.branch 72 (.leaf 1577423023) (.leaf 1553562187)) (.branch 74 (.leaf 1530163018) (.leaf 1507212066))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1484696439) (.branch 77 (.leaf 1462603783) (.leaf 1440922250))) (.branch 80 (.branch 79 (.leaf 1419640472) (.leaf 1398747542)) (.branch 81 (.leaf 1378232988) (.leaf 1358086750)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1338299164) (.leaf 1318860940)) (.branch 85 (.leaf 1299763145) (.leaf 1280997185))) (.branch 88 (.branch 87 (.leaf 1262554788) (.leaf 1244427993)) (.branch 89 (.leaf 1226609128) (.leaf 1209090804)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1191865895) (.branch 92 (.leaf 1174927532) (.leaf 1158269086))) (.branch 95 (.branch 94 (.leaf 1141884160) (.leaf 1125766576)) (.branch 96 (.leaf 1109910367) (.leaf 1094309768)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1078959205) (.leaf 1063853287)) (.branch 100 (.leaf 1048986798) (.leaf 1034354689))) (.branch 103 (.branch 102 (.leaf 1019952074) (.leaf 1005774217)) (.branch 104 (.leaf 991816530) (.leaf 978074564))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 964544007) (.leaf 951220674)) (.branch 108 (.leaf 938100502) (.leaf 925179549))) (.branch 111 (.branch 110 (.leaf 912453986) (.leaf 899920090)) (.branch 112 (.leaf 887574246) (.leaf 875412936)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 863432741) (.leaf 851630332)) (.branch 116 (.leaf 840002471) (.leaf 828546003))) (.branch 119 (.branch 118 (.leaf 817257859) (.leaf 806135043)) (.branch 120 (.leaf 795174642) (.leaf 784373810)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 20).prefactor = (6349439116442803/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 20).cutoff/(generalMeanRows 20).c)).2 =
    (498140464238691/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 20).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 20).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 20).q*(generalMeanRows 20).c/2-2 = (13/25:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable005.value]
    have hcontinuation : (generalMeanRows 20).q*(generalMeanRows 20).cutoff/2-2 = (73/34:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable015.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 20).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 20

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 20).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 20).criticalRate j.val*(generalMeanRows 20).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 20).c*(generalMeanRows 20).criticalPoint j.val)).2-
      (generalMeanRows 20).J/2-(generalMeanRows 20).error (generalMeanGrid j.val)+
      (generalMeanRows 20).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 20).c)).2-
      (generalMeanRows 20).J/2-(generalMeanRows 20).error 4 := by
  have he : (generalMeanRows 20).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 20) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 20)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0020

/-! Kernel-checked entropy margins for general spectral rectangle 21. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0021
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6788126347) (.branch 2 (.leaf 6542081363) (.leaf 6308166513))) (.branch 5 (.branch 4 (.leaf 6085643247) (.leaf 5873826548)) (.branch 6 (.leaf 5672080245) (.leaf 5479812829)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5296473714) (.leaf 5121549871)) (.branch 10 (.leaf 4954562801) (.leaf 4795065806))) (.branch 13 (.branch 12 (.leaf 4642641509) (.leaf 4496899620)) (.branch 14 (.leaf 4357474890) (.leaf 4224025256))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4096230147) (.branch 17 (.leaf 3973788937) (.leaf 3856419521))) (.branch 20 (.branch 19 (.leaf 3743857019) (.leaf 3635852580)) (.branch 21 (.leaf 3532172280) (.leaf 3432596111)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3336917049) (.leaf 3244940188)) (.branch 25 (.leaf 3156481946) (.leaf 3071369327))) (.branch 28 (.branch 27 (.leaf 2989439234) (.leaf 2910537840)) (.branch 29 (.leaf 2834519996) (.leaf 2761248689)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2690594528) (.branch 32 (.leaf 2622435279) (.leaf 2556655418))) (.branch 35 (.branch 34 (.leaf 2493145723) (.leaf 2431802894)) (.branch 36 (.leaf 2372529195) (.leaf 2315232119)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2259824079) (.leaf 2206222117)) (.branch 40 (.leaf 2154347629) (.leaf 2104126115))) (.branch 43 (.branch 42 (.leaf 2055486939) (.leaf 2008363105)) (.branch 44 (.leaf 1962691045) (.leaf 1918410432))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1875463984) (.branch 47 (.leaf 1833797303) (.leaf 1793358705))) (.branch 50 (.branch 49 (.leaf 1754099071) (.leaf 1715971703)) (.branch 51 (.leaf 1678932193) (.leaf 1642938292)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1607949796) (.leaf 1573928429)) (.branch 55 (.leaf 1540837745) (.leaf 1508643022))) (.branch 58 (.branch 57 (.leaf 1477311174) (.leaf 1446810662)) (.branch 59 (.leaf 1417111409) (.leaf 1388184728))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1360003242) (.branch 62 (.leaf 1332540819) (.leaf 1305772506))) (.branch 65 (.branch 64 (.leaf 1279674466) (.leaf 1254223925)) (.branch 66 (.leaf 1229399109) (.leaf 1205179200)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1181544284) (.leaf 1158475305)) (.branch 70 (.leaf 1135954021) (.leaf 1113962964))) (.branch 73 (.branch 72 (.leaf 1092485402) (.leaf 1071505300)) (.branch 74 (.leaf 1051007287) (.leaf 1030976622))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1011399164) (.branch 77 (.leaf 992261344) (.leaf 973550132))) (.branch 80 (.branch 79 (.leaf 955253019) (.leaf 937357983)) (.branch 81 (.leaf 919853474) (.leaf 902728384)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 885972032) (.leaf 869574141)) (.branch 85 (.leaf 853524819) (.leaf 837814544))) (.branch 88 (.branch 87 (.leaf 822434141) (.leaf 807374772)) (.branch 89 (.leaf 792627920) (.leaf 778185369)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 764039196) (.branch 92 (.leaf 750181756) (.leaf 736605671))) (.branch 95 (.branch 94 (.leaf 723303814) (.leaf 710269302)) (.branch 96 (.leaf 697495486) (.leaf 684975936)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 672704437) (.leaf 660674976)) (.branch 100 (.leaf 648881735) (.leaf 637319085))) (.branch 103 (.branch 102 (.leaf 625981572) (.leaf 614863915)) (.branch 104 (.leaf 603960999) (.leaf 593267865))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 582779705) (.leaf 572491858)) (.branch 108 (.leaf 562399800) (.leaf 552499142))) (.branch 111 (.branch 110 (.leaf 542785624) (.leaf 533255111)) (.branch 112 (.leaf 523903583) (.leaf 514727138)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 505721982) (.leaf 496884428)) (.branch 116 (.leaf 488210890) (.leaf 479697881))) (.branch 119 (.branch 118 (.leaf 471342009) (.leaf 463139971)) (.branch 120 (.leaf 455088554) (.leaf 447184629)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 21).prefactor = (660113108403393/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 21).cutoff/(generalMeanRows 21).c)).2 =
    (440320893349863/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 21).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 21).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 21).q*(generalMeanRows 21).c/2-2 = (67/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable016.value]
    have hcontinuation : (generalMeanRows 21).q*(generalMeanRows 21).cutoff/2-2 = (73/34:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable015.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 21).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 21

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 21).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 21).criticalRate j.val*(generalMeanRows 21).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 21).c*(generalMeanRows 21).criticalPoint j.val)).2-
      (generalMeanRows 21).J/2-(generalMeanRows 21).error (generalMeanGrid j.val)+
      (generalMeanRows 21).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 21).c)).2-
      (generalMeanRows 21).J/2-(generalMeanRows 21).error 4 := by
  have he : (generalMeanRows 21).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 21) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 21)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0021

/-! Kernel-checked entropy margins for general spectral rectangle 22. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0022
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6013522851) (.branch 2 (.leaf 5765535644) (.leaf 5530111044))) (.branch 5 (.branch 4 (.leaf 5306487372) (.leaf 5093957974)) (.branch 6 (.leaf 4891866400) (.leaf 4699602101)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4516596576) (.leaf 4342319919)) (.branch 10 (.leaf 4176277698) (.leaf 4018008156))) (.branch 13 (.branch 12 (.leaf 3867079663) (.leaf 3723088416)) (.branch 14 (.leaf 3585656343) (.leaf 3454429199))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3329074824) (.branch 17 (.leaf 3209281556) (.leaf 3094756773))) (.branch 20 (.branch 19 (.leaf 2985225563) (.leaf 2880429494)) (.branch 21 (.leaf 2780125488) (.leaf 2684084787)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2592091990) (.leaf 2503944173)) (.branch 25 (.leaf 2419450072) (.leaf 2338429328))) (.branch 28 (.branch 27 (.leaf 2260711781) (.leaf 2186136830)) (.branch 29 (.leaf 2114552825) (.leaf 2045816507)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1979792489) (.branch 32 (.leaf 1916352774) (.leaf 1855376301))) (.branch 35 (.branch 34 (.leaf 1796748526) (.leaf 1740361031)) (.branch 36 (.leaf 1686111158) (.leaf 1633901665)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1583640413) (.leaf 1535240063)) (.branch 40 (.leaf 1488617797) (.leaf 1443695061))) (.branch 43 (.branch 42 (.leaf 1400397317) (.leaf 1358653813)) (.branch 44 (.leaf 1318397374) (.leaf 1279564192))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1242093647) (.branch 47 (.leaf 1205928122) (.leaf 1171012839))) (.branch 50 (.branch 49 (.leaf 1137295705) (.leaf 1104727159)) (.branch 51 (.leaf 1073260041) (.leaf 1042849458)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1013452661) (.leaf 985028934)) (.branch 55 (.leaf 957539481) (.leaf 930947325))) (.branch 58 (.branch 57 (.leaf 905217216) (.leaf 880315534)) (.branch 59 (.leaf 856210211) (.leaf 832870642))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 810267615) (.branch 62 (.leaf 788373240) (.leaf 767160877))) (.branch 65 (.branch 64 (.leaf 746605075) (.leaf 726681510)) (.branch 66 (.leaf 707366932) (.leaf 688639106)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 670476763) (.leaf 652859556)) (.branch 70 (.leaf 635768007) (.leaf 619183472))) (.branch 73 (.branch 72 (.leaf 603088094) (.leaf 587464768)) (.branch 74 (.leaf 572297103) (.leaf 557569390))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 543266566) (.branch 77 (.leaf 529374185) (.leaf 515878389))) (.branch 80 (.branch 79 (.leaf 502765881) (.leaf 490023896)) (.branch 81 (.leaf 477640177) (.leaf 465602953)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 453900917) (.leaf 442523202)) (.branch 85 (.leaf 431459362) (.leaf 420699353))) (.branch 88 (.branch 87 (.leaf 410233516) (.leaf 400052559)) (.branch 89 (.leaf 390147540) (.leaf 380509850)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 371131203) (.branch 92 (.leaf 362003616) (.leaf 353119403))) (.branch 95 (.branch 94 (.leaf 344471154) (.leaf 336051728)) (.branch 96 (.leaf 327854242) (.leaf 319872057)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 312098770) (.leaf 304528202)) (.branch 100 (.leaf 297154392) (.leaf 289971584))) (.branch 103 (.branch 102 (.leaf 282974222) (.leaf 276156938)) (.branch 104 (.leaf 269514550) (.leaf 263042049))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 256734593) (.leaf 250587503)) (.branch 108 (.leaf 244596254) (.leaf 238756472))) (.branch 111 (.branch 110 (.leaf 233063924) (.leaf 227514514)) (.branch 112 (.leaf 222104280) (.leaf 216829386)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 211686119) (.leaf 206670882)) (.branch 116 (.leaf 201780192) (.leaf 197010676))) (.branch 119 (.branch 118 (.leaf 192359065) (.leaf 187822191)) (.branch 120 (.leaf 183396982) (.leaf 179080463)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 22).prefactor = (6862800129188623/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 22).cutoff/(generalMeanRows 22).c)).2 =
    (17712314228931/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 22).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 22).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 22).q*(generalMeanRows 22).cutoff/2-2 = (73/34:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable015.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 22).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 22

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 22).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 22).criticalRate j.val*(generalMeanRows 22).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 22).c*(generalMeanRows 22).criticalPoint j.val)).2-
      (generalMeanRows 22).J/2-(generalMeanRows 22).error (generalMeanGrid j.val)+
      (generalMeanRows 22).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 22).c)).2-
      (generalMeanRows 22).J/2-(generalMeanRows 22).error 4 := by
  have he : (generalMeanRows 22).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 22) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 22)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0022

/-! Kernel-checked entropy margins for general spectral rectangle 23. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0023
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6126702914) (.branch 2 (.leaf 5929588365) (.leaf 5742232134))) (.branch 5 (.branch 4 (.leaf 5564016213) (.leaf 5394368562)) (.branch 6 (.leaf 5232759078) (.leaf 5078695992)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4931722641) (.leaf 4791414555)) (.branch 10 (.leaf 4657376844) (.leaf 4529241824))) (.branch 13 (.branch 12 (.leaf 4406666871) (.leaf 4289332476)) (.branch 14 (.leaf 4176940470) (.leaf 4069212411))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3965888112) (.branch 17 (.leaf 3866724291) (.leaf 3771493337))) (.branch 20 (.branch 19 (.leaf 3679982183) (.leaf 3591991263)) (.branch 21 (.leaf 3507333560) (.leaf 3425833725)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3347327272) (.leaf 3271659823)) (.branch 25 (.leaf 3198686427) (.leaf 3128270914))) (.branch 28 (.branch 27 (.leaf 3060285315) (.leaf 2994609306)) (.branch 29 (.leaf 2931129709) (.leaf 2869740021)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2810339977) (.branch 32 (.leaf 2752835148) (.leaf 2697136563))) (.branch 35 (.branch 34 (.leaf 2643160362) (.leaf 2590827468)) (.branch 36 (.leaf 2540063289) (.leaf 2490797431)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2442963439) (.leaf 2396498549)) (.branch 40 (.leaf 2351343464) (.leaf 2307442136))) (.branch 43 (.branch 42 (.leaf 2264741570) (.leaf 2223191637)) (.branch 44 (.leaf 2182744901) (.leaf 2143356453))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2104983767) (.branch 47 (.leaf 2067586549) (.leaf 2031126610))) (.branch 50 (.branch 49 (.leaf 1995567739) (.leaf 1960875587)) (.branch 51 (.leaf 1927017557) (.leaf 1893962704)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1861681638) (.leaf 1830146431)) (.branch 55 (.leaf 1799330538) (.leaf 1769208714))) (.branch 58 (.branch 57 (.leaf 1739756942) (.leaf 1710952362)) (.branch 59 (.leaf 1682773205) (.leaf 1655198735))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1628209187) (.branch 62 (.leaf 1601785716) (.leaf 1575910343))) (.branch 65 (.branch 64 (.leaf 1550565911) (.leaf 1525736037)) (.branch 66 (.leaf 1501405070) (.leaf 1477558055)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1454180688) (.leaf 1431259288)) (.branch 70 (.leaf 1408780761) (.leaf 1386732567))) (.branch 73 (.branch 72 (.leaf 1365102695) (.leaf 1343879631)) (.branch 74 (.leaf 1323052334) (.leaf 1302610211))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1282543095) (.branch 77 (.leaf 1262841220) (.leaf 1243495205))) (.branch 80 (.branch 79 (.leaf 1224496032) (.leaf 1205835024)) (.branch 81 (.leaf 1187503838) (.leaf 1169494437)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1151799083) (.leaf 1134410317)) (.branch 85 (.leaf 1117320951) (.leaf 1100524050))) (.branch 88 (.branch 87 (.leaf 1084012920) (.leaf 1067781101)) (.branch 89 (.leaf 1051822353) (.leaf 1036130643)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1020700140) (.branch 92 (.leaf 1005525206) (.leaf 990600381))) (.branch 95 (.branch 94 (.leaf 975920382) (.leaf 961480092)) (.branch 96 (.leaf 947274550) (.leaf 933298950)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 919548629) (.leaf 906019064)) (.branch 100 (.leaf 892705865) (.leaf 879604769))) (.branch 103 (.branch 102 (.leaf 866711634) (.leaf 854022435)) (.branch 104 (.leaf 841533262) (.leaf 829240308))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 817139872) (.leaf 805228352)) (.branch 108 (.leaf 793502240) (.leaf 781958119))) (.branch 111 (.branch 110 (.leaf 770592663) (.leaf 759402628)) (.branch 112 (.leaf 748384851) (.leaf 737536248)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 726853812) (.leaf 716334607)) (.branch 116 (.leaf 705975767) (.leaf 695774495))) (.branch 119 (.branch 118 (.leaf 685728058) (.leaf 675833787)) (.branch 120 (.leaf 666089073) (.leaf 656491366)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 23).prefactor = (710026367130571/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 23).cutoff/(generalMeanRows 23).c)).2 =
    (52988916255327/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 23).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 23).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 23).q*(generalMeanRows 23).c/2-2 = (223/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable017.value]
    have hcontinuation : (generalMeanRows 23).q*(generalMeanRows 23).cutoff/2-2 = (279/119:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable018.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 23).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 23

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 23).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 23).criticalRate j.val*(generalMeanRows 23).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 23).c*(generalMeanRows 23).criticalPoint j.val)).2-
      (generalMeanRows 23).J/2-(generalMeanRows 23).error (generalMeanGrid j.val)+
      (generalMeanRows 23).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 23).c)).2-
      (generalMeanRows 23).J/2-(generalMeanRows 23).error 4 := by
  have he : (generalMeanRows 23).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 23) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 23)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0023

/-! Kernel-checked entropy margins for general spectral rectangle 24. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0024
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6184302498) (.branch 2 (.leaf 5981147944) (.leaf 5788061673))) (.branch 5 (.branch 4 (.leaf 5604407271) (.leaf 5429595634)) (.branch 6 (.leaf 5263080823) (.leaf 5104356352)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4952951866) (.leaf 4808430143)) (.branch 10 (.leaf 4670384401) (.leaf 4538435856))) (.branch 13 (.branch 12 (.leaf 4412231516) (.leaf 4291442174)) (.branch 14 (.leaf 4175760586) (.leaf 4064899808))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3958591680) (.branch 17 (.leaf 3856585439) (.leaf 3758646453))) (.branch 20 (.branch 19 (.leaf 3664555051) (.leaf 3574105462)) (.branch 21 (.leaf 3487104824) (.leaf 3403372289)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3322738183) (.leaf 3245043239)) (.branch 25 (.leaf 3170137891) (.leaf 3097881613))) (.branch 28 (.branch 27 (.leaf 3028142317) (.leaf 2960795789)) (.branch 29 (.leaf 2895725167) (.leaf 2832820464)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2771978113) (.branch 32 (.leaf 2713100556) (.leaf 2656095857))) (.branch 35 (.branch 34 (.leaf 2600877341) (.leaf 2547363260)) (.branch 36 (.leaf 2495476482) (.leaf 2445144204)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2396297677) (.leaf 2348871956)) (.branch 40 (.leaf 2302805666) (.leaf 2258040784))) (.branch 43 (.branch 42 (.leaf 2214522428) (.leaf 2172198675)) (.branch 44 (.leaf 2131020374) (.leaf 2090940982))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2051916411) (.branch 47 (.leaf 2013904877) (.leaf 1976866764))) (.branch 50 (.branch 49 (.leaf 1940764499) (.leaf 1905562430)) (.branch 51 (.leaf 1871226712) (.leaf 1837725206)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1805027376) (.leaf 1773104199)) (.branch 55 (.leaf 1741928077) (.leaf 1711472758))) (.branch 58 (.branch 57 (.leaf 1681713255) (.leaf 1652625780)) (.branch 59 (.leaf 1624187671) (.leaf 1596377333))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1569174179) (.branch 62 (.leaf 1542558569) (.leaf 1516511763))) (.branch 65 (.branch 64 (.leaf 1491015869) (.leaf 1466053798)) (.branch 66 (.leaf 1441609219) (.leaf 1417666518)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1394210763) (.leaf 1371227663)) (.branch 70 (.leaf 1348703534) (.leaf 1326625272))) (.branch 73 (.branch 72 (.leaf 1304980316) (.leaf 1283756626)) (.branch 74 (.leaf 1262942650) (.leaf 1242527303))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1222499940) (.branch 77 (.leaf 1202850338) (.leaf 1183568668))) (.branch 80 (.branch 79 (.leaf 1164645482) (.leaf 1146071691)) (.branch 81 (.leaf 1127838543) (.leaf 1109937616)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1092360793) (.leaf 1075100250)) (.branch 85 (.leaf 1058148445) (.leaf 1041498100))) (.branch 88 (.branch 87 (.leaf 1025142190) (.leaf 1009073934)) (.branch 89 (.leaf 993286777) (.leaf 977774386)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 962530638) (.branch 92 (.leaf 947549609) (.leaf 932825564))) (.branch 95 (.branch 94 (.leaf 918352952) (.leaf 904126396)) (.branch 96 (.leaf 890140686) (.leaf 876390769)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 862871747) (.leaf 849578866)) (.branch 100 (.leaf 836507512) (.leaf 823653206))) (.branch 103 (.branch 102 (.leaf 811011595) (.leaf 798578450)) (.branch 104 (.leaf 786349662) (.leaf 774321231))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 762489270) (.leaf 750849993)) (.branch 108 (.leaf 739399717) (.leaf 728134854))) (.branch 111 (.branch 110 (.leaf 717051909) (.leaf 706147477)) (.branch 112 (.leaf 695418238) (.leaf 684860956)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 674472474) (.leaf 664249711)) (.branch 116 (.leaf 654189663) (.leaf 644289396))) (.branch 119 (.branch 118 (.leaf 634546045) (.leaf 624956811)) (.branch 120 (.leaf 615518961) (.leaf 606229825)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 24).prefactor = (1464646614651589/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 24).cutoff/(generalMeanRows 24).c)).2 =
    (519193873436521/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 24).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 24).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 24).q*(generalMeanRows 24).c/2-2 = (117/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable009.value]
    have hcontinuation : (generalMeanRows 24).q*(generalMeanRows 24).cutoff/2-2 = (279/119:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable018.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 24).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 24

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 24).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 24).criticalRate j.val*(generalMeanRows 24).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 24).c*(generalMeanRows 24).criticalPoint j.val)).2-
      (generalMeanRows 24).J/2-(generalMeanRows 24).error (generalMeanGrid j.val)+
      (generalMeanRows 24).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 24).c)).2-
      (generalMeanRows 24).J/2-(generalMeanRows 24).error 4 := by
  have he : (generalMeanRows 24).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 24) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 24)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0024

/-! Kernel-checked entropy margins for general spectral rectangle 25. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0025
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6243444585) (.branch 2 (.leaf 6034151333) (.leaf 5835246104))) (.branch 5 (.branch 4 (.leaf 5646073455) (.leaf 5466026641)) (.branch 6 (.leaf 5294543346) (.leaf 5131101867)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4975217684) (.leaf 4826440384)) (.branch 10 (.leaf 4684350882) (.leaf 4548558910))) (.branch 13 (.branch 12 (.leaf 4418700743) (.leaf 4294437139)) (.branch 14 (.leaf 4175451456) (.leaf 4061447949))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3952150202) (.branch 17 (.leaf 3847299708) (.leaf 3746654557))) (.branch 20 (.branch 19 (.leaf 3649988244) (.leaf 3557088562)) (.branch 21 (.leaf 3467756600) (.leaf 3381805806)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3299061133) (.leaf 3219358245)) (.branch 25 (.leaf 3142542794) (.leaf 3068469737))) (.branch 28 (.branch 27 (.leaf 2997002718) (.leaf 2928013487)) (.branch 29 (.leaf 2861381366) (.leaf 2796992751)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2734740654) (.branch 32 (.leaf 2674524273) (.leaf 2616248595))) (.branch 35 (.branch 34 (.leaf 2559824028) (.leaf 2505166052)) (.branch 36 (.leaf 2452194906) (.leaf 2400835285)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2351016062) (.leaf 2302670031)) (.branch 40 (.leaf 2255733667) (.leaf 2210146892))) (.branch 43 (.branch 42 (.leaf 2165852877) (.leaf 2122797833)) (.branch 44 (.leaf 2080930836) (.leaf 2040203650))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2000570569) (.branch 47 (.leaf 1961988264) (.leaf 1924415645))) (.branch 50 (.branch 49 (.leaf 1887813730) (.leaf 1852145515)) (.branch 51 (.leaf 1817375867) (.leaf 1783471411)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1750400428) (.leaf 1718132762)) (.branch 55 (.leaf 1686639730) (.leaf 1655894036))) (.branch 58 (.branch 57 (.leaf 1625869697) (.leaf 1596541964)) (.branch 59 (.leaf 1567887257) (.leaf 1539883097))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1512508046) (.branch 62 (.leaf 1485741649) (.leaf 1459564382))) (.branch 65 (.branch 64 (.leaf 1433957598) (.leaf 1408903482)) (.branch 66 (.leaf 1384385005) (.leaf 1360385880)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1336890526) (.leaf 1313884028)) (.branch 70 (.leaf 1291352103) (.leaf 1269281063))) (.branch 73 (.branch 72 (.leaf 1247657792) (.leaf 1226469707)) (.branch 74 (.leaf 1205704738) (.leaf 1185351296))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1165398252) (.branch 77 (.leaf 1145834914) (.leaf 1126651003))) (.branch 80 (.branch 79 (.leaf 1107836631) (.leaf 1089382287)) (.branch 81 (.leaf 1071278814) (.leaf 1053517392)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1036089524) (.leaf 1018987017)) (.branch 85 (.leaf 1002201971) (.leaf 985726764))) (.branch 88 (.branch 87 (.leaf 969554036) (.leaf 953676681)) (.branch 89 (.leaf 938087834) (.leaf 922780857)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 907749333) (.branch 92 (.leaf 892987053) (.leaf 878488008))) (.branch 95 (.branch 94 (.leaf 864246380) (.leaf 850256533)) (.branch 96 (.leaf 836513006) (.leaf 823010504)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 809743893) (.leaf 796708192)) (.branch 100 (.leaf 783898565) (.leaf 771310318))) (.branch 103 (.branch 102 (.leaf 758938892) (.leaf 746779856)) (.branch 104 (.leaf 734828905) (.leaf 723081850))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 711534620) (.leaf 700183252)) (.branch 108 (.leaf 689023889) (.leaf 678052775))) (.branch 111 (.branch 110 (.leaf 667266255) (.leaf 656660764)) (.branch 112 (.leaf 646232831) (.leaf 635979071)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 625896184) (.leaf 615980949)) (.branch 116 (.leaf 606230227) (.leaf 596640953))) (.branch 119 (.branch 118 (.leaf 587210135) (.leaf 577934851)) (.branch 120 (.leaf 568812249) (.leaf 559839542)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 25).prefactor = (6042563502197009/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 25).cutoff/(generalMeanRows 25).c)).2 =
    (508611764105983/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 25).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 25).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 25).q*(generalMeanRows 25).c/2-2 = (49/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable011.value]
    have hcontinuation : (generalMeanRows 25).q*(generalMeanRows 25).cutoff/2-2 = (279/119:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable018.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 25).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 25

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 25).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 25).criticalRate j.val*(generalMeanRows 25).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 25).c*(generalMeanRows 25).criticalPoint j.val)).2-
      (generalMeanRows 25).J/2-(generalMeanRows 25).error (generalMeanGrid j.val)+
      (generalMeanRows 25).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 25).c)).2-
      (generalMeanRows 25).J/2-(generalMeanRows 25).error 4 := by
  have he : (generalMeanRows 25).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 25) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 25)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0025

/-! Kernel-checked entropy margins for general spectral rectangle 26. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0026
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5800005134) (.branch 2 (.leaf 5586545027) (.leaf 5383812636))) (.branch 5 (.branch 4 (.leaf 5191135821) (.leaf 5007892230)) (.branch 6 (.leaf 4833504928) (.leaf 4667438493)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4509195511) (.leaf 4358313427)) (.branch 10 (.leaf 4214361701) (.leaf 4076939247))) (.branch 13 (.branch 12 (.leaf 3945672109) (.leaf 3820211348)) (.branch 14 (.leaf 3700231127) (.leaf 3585426968))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3475514149) (.branch 17 (.leaf 3370226259) (.leaf 3269313853))) (.branch 20 (.branch 19 (.leaf 3172543238) (.leaf 3079695346)) (.branch 21 (.leaf 2990564705) (.leaf 2904958489)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2822695644) (.leaf 2743606081)) (.branch 25 (.leaf 2667529929) (.leaf 2594316854))) (.branch 28 (.branch 27 (.leaf 2523825415) (.leaf 2455922477)) (.branch 29 (.leaf 2390482669) (.leaf 2327387873)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2266526754) (.branch 32 (.leaf 2207794329) (.leaf 2151091556))) (.branch 35 (.branch 34 (.leaf 2096324959) (.leaf 2043406279)) (.branch 36 (.leaf 1992252145) (.leaf 1942783772)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1894926675) (.leaf 1848610407)) (.branch 40 (.leaf 1803768311) (.leaf 1760337290))) (.branch 43 (.branch 42 (.leaf 1718257593) (.leaf 1677472611)) (.branch 44 (.leaf 1637928696) (.leaf 1599574977))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1562363203) (.branch 47 (.leaf 1526247582) (.leaf 1491184647))) (.branch 50 (.branch 49 (.leaf 1457133111) (.leaf 1424053748)) (.branch 51 (.leaf 1391909272) (.leaf 1360664225)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1330284877) (.leaf 1300739122)) (.branch 55 (.leaf 1271996394) (.leaf 1244027576))) (.branch 58 (.branch 57 (.leaf 1216804922) (.leaf 1190301977)) (.branch 59 (.leaf 1164493512) (.leaf 1139355454))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1114864822) (.branch 62 (.leaf 1090999669) (.leaf 1067739028))) (.branch 65 (.branch 64 (.leaf 1045062857) (.leaf 1022951991)) (.branch 66 (.leaf 1001388098) (.leaf 980353630)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 959831787) (.leaf 939806477)) (.branch 70 (.leaf 920262278) (.leaf 901184404))) (.branch 73 (.branch 72 (.leaf 882558675) (.leaf 864371484)) (.branch 74 (.leaf 846609769) (.leaf 829260987))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 812313084) (.branch 77 (.leaf 795754479) (.leaf 779574030))) (.branch 80 (.branch 79 (.leaf 763761025) (.leaf 748305152)) (.branch 81 (.leaf 733196482) (.leaf 718425453)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 703982854) (.leaf 689859802)) (.branch 85 (.leaf 676047734) (.leaf 662538389))) (.branch 88 (.branch 87 (.leaf 649323793) (.leaf 636396250)) (.branch 89 (.leaf 623748326) (.leaf 611372838)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 599262844) (.branch 92 (.leaf 587411633) (.leaf 575812714))) (.branch 95 (.branch 94 (.leaf 564459803) (.leaf 553346823)) (.branch 96 (.leaf 542467887) (.leaf 531817293)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 521389519) (.leaf 511179209)) (.branch 100 (.leaf 501181174) (.leaf 491390380))) (.branch 103 (.branch 102 (.leaf 481801944) (.leaf 472411127)) (.branch 104 (.leaf 463213329) (.leaf 454204085))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 445379056) (.leaf 436734028)) (.branch 108 (.leaf 428264906) (.leaf 419967709))) (.branch 111 (.branch 110 (.leaf 411838566) (.leaf 403873713)) (.branch 112 (.leaf 396069488) (.leaf 388422328)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 380928765) (.leaf 373585424)) (.branch 116 (.leaf 366389016) (.leaf 359336342))) (.branch 119 (.branch 118 (.leaf 352424283) (.leaf 345649799)) (.branch 120 (.leaf 339009931) (.leaf 332501792)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 26).prefactor = (3116158986136139/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 26).cutoff/(generalMeanRows 26).c)).2 =
    (228659234859217/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 26).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 26).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 26).q*(generalMeanRows 26).c/2-2 = (3/4:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable019.value]
    have hcontinuation : (generalMeanRows 26).q*(generalMeanRows 26).cutoff/2-2 = (279/119:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable018.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 26).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 26

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 26).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 26).criticalRate j.val*(generalMeanRows 26).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 26).c*(generalMeanRows 26).criticalPoint j.val)).2-
      (generalMeanRows 26).J/2-(generalMeanRows 26).error (generalMeanGrid j.val)+
      (generalMeanRows 26).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 26).c)).2-
      (generalMeanRows 26).J/2-(generalMeanRows 26).error 4 := by
  have he : (generalMeanRows 26).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 26) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 26)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0026

/-! Kernel-checked entropy margins for general spectral rectangle 27. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0027
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5518057631) (.branch 2 (.leaf 5301051084) (.leaf 5095108955))) (.branch 5 (.branch 4 (.leaf 4899540126) (.leaf 4713704542)) (.branch 6 (.leaf 4537008729) (.leaf 4368901785)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4208871788) (.leaf 4056442566)) (.branch 10 (.leaf 3911170785) (.leaf 3772643318))) (.branch 13 (.branch 12 (.leaf 3640474866) (.leaf 3514305794)) (.branch 14 (.leaf 3393800165) (.leaf 3278643954))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3168543413) (.branch 17 (.leaf 3063223580) (.leaf 2962426908))) (.branch 20 (.branch 19 (.leaf 2865912021) (.leaf 2773452559)) (.branch 21 (.leaf 2684836120) (.leaf 2599863295)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2518346767) (.leaf 2440110485)) (.branch 25 (.leaf 2364988906) (.leaf 2292826284))) (.branch 28 (.branch 27 (.leaf 2223476024) (.leaf 2156800076)) (.branch 29 (.leaf 2092668376) (.leaf 2030958326)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1971554317) (.branch 32 (.leaf 1914347278) (.leaf 1859234263))) (.branch 35 (.branch 34 (.leaf 1806118064) (.leaf 1754906852)) (.branch 36 (.leaf 1705513842) (.leaf 1657856982)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1611858661) (.leaf 1567445440)) (.branch 40 (.leaf 1524547797) (.leaf 1483099893))) (.branch 43 (.branch 42 (.leaf 1443039349) (.leaf 1404307042)) (.branch 44 (.leaf 1366846912) (.leaf 1330605781))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1295533185) (.branch 47 (.leaf 1261581215) (.leaf 1228704372))) (.branch 50 (.branch 49 (.leaf 1196859425) (.leaf 1166005283)) (.branch 51 (.leaf 1136102875) (.leaf 1107115032)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1079006385) (.leaf 1051743259)) (.branch 55 (.leaf 1025293584) (.leaf 999626802))) (.branch 58 (.branch 57 (.leaf 974713787) (.leaf 950526767)) (.branch 59 (.leaf 927039246) (.leaf 904225941))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 882062714) (.branch 62 (.leaf 860526510) (.leaf 839595304))) (.branch 65 (.branch 64 (.leaf 819248039) (.leaf 799464583)) (.branch 66 (.leaf 780225678) (.leaf 761512892)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 743308583) (.leaf 725595850)) (.branch 70 (.leaf 708358503) (.leaf 691581025))) (.branch 73 (.branch 72 (.leaf 675248536) (.leaf 659346762)) (.branch 74 (.leaf 643862008) (.leaf 628781127))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 614091494) (.branch 77 (.leaf 599780978) (.leaf 585837924))) (.branch 80 (.branch 79 (.leaf 572251125) (.leaf 559009804)) (.branch 81 (.leaf 546103592) (.leaf 533522509)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 521256947) (.leaf 509297653)) (.branch 85 (.leaf 497635711) (.leaf 486262528))) (.branch 88 (.branch 87 (.leaf 475169820) (.leaf 464349597)) (.branch 89 (.leaf 453794151) (.leaf 443496043)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 433448091) (.branch 92 (.leaf 423643360) (.leaf 414075149))) (.branch 95 (.branch 94 (.leaf 404736986) (.leaf 395622613)) (.branch 96 (.leaf 386725979) (.leaf 378041233)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 369562712) (.leaf 361284939)) (.branch 100 (.leaf 353202610) (.leaf 345310590))) (.branch 103 (.branch 102 (.leaf 337603905) (.leaf 330077737)) (.branch 104 (.leaf 322727418) (.leaf 315548420))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 308536358) (.leaf 301686975)) (.branch 108 (.leaf 294996144) (.leaf 288459861))) (.branch 111 (.branch 110 (.leaf 282074240) (.leaf 275835508)) (.branch 112 (.leaf 269740003) (.leaf 263784169)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 257964552) (.leaf 252277796)) (.branch 116 (.leaf 246720640) (.leaf 241289916))) (.branch 119 (.branch 118 (.leaf 235982543) (.leaf 230795527)) (.branch 120 (.leaf 225725955) (.leaf 220770996)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 27).prefactor = (3214015648605561/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 27).cutoff/(generalMeanRows 27).c)).2 =
    (418097756565151/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 27).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 27).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 27).q*(generalMeanRows 27).c/2-2 = (43/50:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable020.value]
    have hcontinuation : (generalMeanRows 27).q*(generalMeanRows 27).cutoff/2-2 = (279/119:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable018.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 27).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 27

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 27).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 27).criticalRate j.val*(generalMeanRows 27).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 27).c*(generalMeanRows 27).criticalPoint j.val)).2-
      (generalMeanRows 27).J/2-(generalMeanRows 27).error (generalMeanGrid j.val)+
      (generalMeanRows 27).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 27).c)).2-
      (generalMeanRows 27).J/2-(generalMeanRows 27).error 4 := by
  have he : (generalMeanRows 27).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 27) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 27)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0027

/-! Kernel-checked entropy margins for general spectral rectangle 28. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0028
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5471486054) (.branch 2 (.leaf 5249607983) (.leaf 5039136370))) (.branch 5 (.branch 4 (.leaf 4839359206) (.leaf 4649617023)) (.branch 6 (.leaf 4469298284) (.leaf 4297835258)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4134700324) (.leaf 3979402651)) (.branch 10 (.leaf 3831485197) (.leaf 3690522010))) (.branch 13 (.branch 12 (.leaf 3556115773) (.leaf 3427895584)) (.branch 14 (.leaf 3305514933) (.leaf 3188649864))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3076997294) (.branch 17 (.leaf 2970273478) (.leaf 2868212603))) (.branch 20 (.branch 19 (.leaf 2770565504) (.leaf 2677098480)) (.branch 21 (.leaf 2587592207) (.leaf 2501840740)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2419650589) (.leaf 2340839875)) (.branch 25 (.leaf 2265237542) (.leaf 2192682632))) (.branch 28 (.branch 27 (.leaf 2123023618) (.leaf 2056117780)) (.branch 29 (.leaf 1991830631) (.leaf 1930035385)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1870612462) (.branch 32 (.leaf 1813449027) (.leaf 1758438562))) (.branch 35 (.branch 34 (.leaf 1705480472) (.leaf 1654479713)) (.branch 36 (.leaf 1605346447) (.leaf 1557995723)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1512347179) (.leaf 1468324758)) (.branch 40 (.leaf 1425856453) (.leaf 1384874063))) (.branch 43 (.branch 42 (.leaf 1345312961) (.leaf 1307111891)) (.branch 44 (.leaf 1270212760) (.leaf 1234560457))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1200102682) (.branch 47 (.leaf 1166789777) (.leaf 1134574578))) (.branch 50 (.branch 49 (.leaf 1103412273) (.leaf 1073260263)) (.branch 51 (.leaf 1044078044) (.leaf 1015827082)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 988470708) (.leaf 961974013)) (.branch 55 (.leaf 936303748) (.leaf 911428238))) (.branch 58 (.branch 57 (.leaf 887317289) (.leaf 863942115)) (.branch 59 (.leaf 841275257) (.leaf 819290512))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 797962868) (.branch 62 (.leaf 777268441) (.leaf 757184413))) (.branch 65 (.branch 64 (.leaf 737688977) (.leaf 718761287)) (.branch 66 (.leaf 700381403) (.leaf 682530251)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 665189571) (.leaf 648341884)) (.branch 70 (.leaf 631970445) (.leaf 616059211))) (.branch 73 (.branch 72 (.leaf 600592804) (.leaf 585556479)) (.branch 74 (.leaf 570936092) (.leaf 556718071))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 542889388) (.branch 77 (.leaf 529437533) (.leaf 516350490))) (.branch 80 (.branch 79 (.leaf 503616712) (.leaf 491225099)) (.branch 81 (.leaf 479164979) (.leaf 467426086)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 455998541) (.leaf 444872836)) (.branch 85 (.leaf 434039816) (.leaf 423490663))) (.branch 88 (.branch 87 (.leaf 413216882) (.leaf 403210285)) (.branch 89 (.leaf 393462978) (.leaf 383967349)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 374716053) (.branch 92 (.leaf 365702006) (.leaf 356918366))) (.branch 95 (.branch 94 (.leaf 348358531) (.leaf 340016121)) (.branch 96 (.leaf 331884976) (.leaf 323959141)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 316232861) (.leaf 308700572)) (.branch 100 (.leaf 301356891) (.leaf 294196614))) (.branch 103 (.branch 102 (.leaf 287214702) (.leaf 280406281)) (.branch 104 (.leaf 273766632) (.leaf 267291184))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 260975511) (.leaf 254815326)) (.branch 108 (.leaf 248806472) (.leaf 242944925))) (.branch 111 (.branch 110 (.leaf 237226780) (.leaf 231648251)) (.branch 112 (.leaf 226205669) (.leaf 220895474)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 215714209) (.leaf 210658525)) (.branch 116 (.leaf 205725166) (.leaf 200910976))) (.branch 119 (.branch 118 (.leaf 196212888) (.leaf 191627924)) (.branch 120 (.leaf 187153192) (.leaf 182785883)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 28).prefactor = (6629890602783341/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 28).cutoff/(generalMeanRows 28).c)).2 =
    (399049561594459/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 28).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 28).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 28).q*(generalMeanRows 28).c/2-2 = (183/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable021.value]
    have hcontinuation : (generalMeanRows 28).q*(generalMeanRows 28).cutoff/2-2 = (279/119:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable018.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 28).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 28

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 28).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 28).criticalRate j.val*(generalMeanRows 28).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 28).c*(generalMeanRows 28).criticalPoint j.val)).2-
      (generalMeanRows 28).J/2-(generalMeanRows 28).error (generalMeanGrid j.val)+
      (generalMeanRows 28).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 28).c)).2-
      (generalMeanRows 28).J/2-(generalMeanRows 28).error 4 := by
  have he : (generalMeanRows 28).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 28) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 28)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0028

/-! Kernel-checked entropy margins for general spectral rectangle 29. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0029
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5643306994) (.branch 2 (.leaf 5414461291) (.leaf 5197380243))) (.branch 5 (.branch 4 (.leaf 4991329482) (.leaf 4795628830)) (.branch 6 (.leaf 4609647546) (.leaf 4432800071)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4264542215) (.leaf 4104367732)) (.branch 10 (.leaf 3951805231) (.leaf 3806415380))) (.branch 13 (.branch 12 (.leaf 3667788387) (.leaf 3535541703)) (.branch 14 (.leaf 3409317935) (.leaf 3288782956))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3173624163) (.branch 17 (.leaf 3063548901) (.leaf 2958283011))) (.branch 20 (.branch 19 (.leaf 2857569503) (.leaf 2761167337)) (.branch 21 (.leaf 2668850300) (.leaf 2580405982)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2495634816) (.leaf 2414349211)) (.branch 25 (.leaf 2336372740) (.leaf 2261539390))) (.branch 28 (.branch 27 (.leaf 2189692876) (.leaf 2120685995)) (.branch 29 (.leaf 2054380038) (.leaf 1990644238)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1929355258) (.branch 32 (.leaf 1870396721) (.leaf 1813658764))) (.branch 35 (.branch 34 (.leaf 1759037633) (.leaf 1706435298)) (.branch 36 (.leaf 1655759101) (.leaf 1606921424)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1559839379) (.leaf 1514434523)) (.branch 40 (.leaf 1470632588) (.leaf 1428363228))) (.branch 43 (.branch 42 (.leaf 1387559791) (.leaf 1348159093)) (.branch 44 (.leaf 1310101219) (.leaf 1273329328))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1237789476) (.branch 47 (.leaf 1203430447) (.leaf 1170203595))) (.branch 50 (.branch 49 (.leaf 1138062701) (.leaf 1106963828)) (.branch 51 (.leaf 1076865200) (.leaf 1047727074)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1019511629) (.leaf 992182859)) (.branch 55 (.leaf 965706471) (.leaf 940049796))) (.branch 58 (.branch 57 (.leaf 915181692) (.leaf 891072468)) (.branch 59 (.leaf 867693803) (.leaf 845018671))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 823021276) (.branch 62 (.leaf 801676982) (.leaf 780962256))) (.branch 65 (.branch 64 (.leaf 760854606) (.leaf 741332529)) (.branch 66 (.leaf 722375463) (.leaf 703963731)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 686078503) (.leaf 668701748)) (.branch 70 (.leaf 651816197) (.leaf 635405303))) (.branch 73 (.branch 72 (.leaf 619453205) (.leaf 603944695)) (.branch 74 (.leaf 588865184) (.leaf 574200674))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 559937729) (.branch 77 (.leaf 546063446) (.leaf 532565431))) (.branch 80 (.branch 79 (.leaf 519431775) (.leaf 506651028)) (.branch 81 (.leaf 494212185) (.leaf 482104655)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 470318251) (.leaf 458843166)) (.branch 85 (.leaf 447669957) (.leaf 436789530))) (.branch 88 (.branch 87 (.leaf 426193121) (.leaf 415872287)) (.branch 89 (.leaf 405818886) (.leaf 396025066)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 386483252) (.branch 92 (.leaf 377186136) (.leaf 368126664))) (.branch 95 (.branch 94 (.leaf 359298025) (.leaf 350693639)) (.branch 96 (.leaf 342307152) (.leaf 334132422)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 326163514) (.leaf 318394688)) (.branch 100 (.leaf 310820394) (.leaf 303435262))) (.branch 103 (.branch 102 (.leaf 296234098) (.leaf 289211873)) (.branch 104 (.leaf 282363719) (.leaf 275684922))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 269170919) (.leaf 262817285)) (.branch 108 (.leaf 256619736) (.leaf 250574118))) (.branch 111 (.branch 110 (.leaf 244676406) (.leaf 238922695)) (.branch 112 (.leaf 233309200) (.leaf 227832249)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 222488277) (.leaf 217273829)) (.branch 116 (.leaf 212185548) (.leaf 207220178))) (.branch 119 (.branch 118 (.leaf 202374556) (.leaf 197645610)) (.branch 120 (.leaf 193030359) (.leaf 188525904)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 29).prefactor = (6838088891064583/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 29).cutoff/(generalMeanRows 29).c)).2 =
    (399049561594459/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 29).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 29).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 29).q*(generalMeanRows 29).c/2-2 = (183/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable021.value]
    have hcontinuation : (generalMeanRows 29).q*(generalMeanRows 29).cutoff/2-2 = (279/119:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable018.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 29).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 29

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 29).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 29).criticalRate j.val*(generalMeanRows 29).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 29).c*(generalMeanRows 29).criticalPoint j.val)).2-
      (generalMeanRows 29).J/2-(generalMeanRows 29).error (generalMeanGrid j.val)+
      (generalMeanRows 29).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 29).c)).2-
      (generalMeanRows 29).J/2-(generalMeanRows 29).error 4 := by
  have he : (generalMeanRows 29).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 29) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 29)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0029

/-! Kernel-checked entropy margins for general spectral rectangle 30. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0030
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6999899868) (.branch 2 (.leaf 6784492646) (.leaf 6579360181))) (.branch 5 (.branch 4 (.leaf 6383886278) (.leaf 6197498828)) (.branch 6 (.leaf 6019665965) (.leaf 5849892630)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5687717502) (.leaf 5532710244)) (.branch 10 (.leaf 5384469020) (.leaf 5242618263))) (.branch 13 (.branch 12 (.leaf 5106806648) (.leaf 4976705257)) (.branch 14 (.leaf 4852005914) (.leaf 4732419662))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4617675382) (.branch 17 (.leaf 4507518519) (.leaf 4401709929))) (.branch 20 (.branch 19 (.leaf 4300024806) (.leaf 4202251711)) (.branch 21 (.leaf 4108191663) (.leaf 4017657316)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3930472188) (.leaf 3846469956)) (.branch 25 (.leaf 3765493798) (.leaf 3687395789))) (.branch 28 (.branch 27 (.leaf 3612036335) (.leaf 3539283655)) (.branch 29 (.leaf 3469013293) (.leaf 3401107665)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3335455645) (.branch 32 (.leaf 3271952167) (.leaf 3210497863))) (.branch 35 (.branch 34 (.leaf 3150998724) (.leaf 3093365781)) (.branch 36 (.leaf 3037514805) (.leaf 2983366034)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2930843913) (.leaf 2879876847)) (.branch 40 (.leaf 2830396977) (.leaf 2782339962))) (.branch 43 (.branch 42 (.leaf 2735644786) (.leaf 2690253563)) (.branch 44 (.leaf 2646111366) (.leaf 2603166058))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2561368139) (.branch 47 (.leaf 2520670599) (.leaf 2481028781))) (.branch 50 (.branch 49 (.leaf 2442400250) (.leaf 2404744674)) (.branch 51 (.leaf 2368023709) (.leaf 2332200890)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2297241531) (.leaf 2263112629)) (.branch 55 (.leaf 2229782774) (.leaf 2197222062))) (.branch 58 (.branch 57 (.leaf 2165402020) (.leaf 2134295525)) (.branch 59 (.leaf 2103876736) (.leaf 2074121026))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2045004916) (.branch 62 (.leaf 2016506022) (.leaf 1988602989))) (.branch 65 (.branch 64 (.leaf 1961275445) (.leaf 1934503947)) (.branch 66 (.leaf 1908269933) (.leaf 1882555681)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1857344259) (.leaf 1832619493)) (.branch 70 (.leaf 1808365920) (.leaf 1784568760))) (.branch 73 (.branch 72 (.leaf 1761213878) (.leaf 1738287750)) (.branch 74 (.leaf 1715777436) (.leaf 1693670550))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1671955230) (.branch 77 (.leaf 1650620116) (.leaf 1629654321))) (.branch 80 (.branch 79 (.leaf 1609047412) (.leaf 1588789386)) (.branch 81 (.leaf 1568870649) (.leaf 1549281994)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1530014587) (.leaf 1511059945)) (.branch 85 (.leaf 1492409923) (.leaf 1474056692))) (.branch 88 (.branch 87 (.leaf 1455992731) (.leaf 1438210807)) (.branch 89 (.leaf 1420703963) (.leaf 1403465507)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1386488997) (.branch 92 (.leaf 1369768230) (.leaf 1353297232))) (.branch 95 (.branch 94 (.leaf 1337070247) (.leaf 1321081726)) (.branch 96 (.leaf 1305326319) (.leaf 1289798863)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1274494378) (.leaf 1259408057)) (.branch 100 (.leaf 1244535254) (.leaf 1229871484))) (.branch 103 (.branch 102 (.leaf 1215412412) (.leaf 1201153845)) (.branch 104 (.leaf 1187091728) (.leaf 1173222138))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1159541278) (.leaf 1146045471)) (.branch 108 (.leaf 1132731155) (.leaf 1119594877))) (.branch 111 (.branch 110 (.leaf 1106633292) (.leaf 1093843154)) (.branch 112 (.leaf 1081221316) (.leaf 1068764721)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1056470402) (.leaf 1044335480)) (.branch 116 (.leaf 1032357155) (.leaf 1020532705))) (.branch 119 (.branch 118 (.leaf 1008859486) (.leaf 997334925)) (.branch 120 (.leaf 985956517) (.leaf 974721827)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 30).prefactor = (2743047204925973/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 30).cutoff/(generalMeanRows 30).c)).2 =
    (505520571536313/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 30).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 30).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 30).q*(generalMeanRows 30).c/2-2 = (43/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable022.value]
    have hcontinuation : (generalMeanRows 30).q*(generalMeanRows 30).cutoff/2-2 = (71/35:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable023.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 30).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 30

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 30).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 30).criticalRate j.val*(generalMeanRows 30).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 30).c*(generalMeanRows 30).criticalPoint j.val)).2-
      (generalMeanRows 30).J/2-(generalMeanRows 30).error (generalMeanGrid j.val)+
      (generalMeanRows 30).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 30).c)).2-
      (generalMeanRows 30).J/2-(generalMeanRows 30).error 4 := by
  have he : (generalMeanRows 30).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 30) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 30)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0030

/-! Kernel-checked entropy margins for general spectral rectangle 31. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0031
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7141727462) (.branch 2 (.leaf 6917062418) (.leaf 6703105804))) (.branch 5 (.branch 4 (.leaf 6499216546) (.leaf 6304799440)) (.branch 6 (.leaf 6119301145) (.leaf 5942206607)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5773035868) (.leaf 5611341195)) (.branch 10 (.leaf 5456704503) (.leaf 5308735024))) (.branch 13 (.branch 12 (.leaf 5167067201) (.leaf 5031358785)) (.branch 14 (.leaf 4901289089) (.leaf 4776557418))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4656881621) (.branch 17 (.leaf 4541996774) (.leaf 4431653972))) (.branch 20 (.branch 19 (.leaf 4325619225) (.leaf 4223672433)) (.branch 21 (.leaf 4125606455) (.leaf 4031226242)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3940348042) (.leaf 3852798664)) (.branch 25 (.leaf 3768414797) (.leaf 3687042374))) (.branch 28 (.branch 27 (.leaf 3608535995) (.leaf 3532758380)) (.branch 29 (.leaf 3459579862) (.leaf 3388877923)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3320536754) (.branch 32 (.leaf 3254446849) (.leaf 3190504627))) (.branch 35 (.branch 34 (.leaf 3128612075) (.leaf 3068676423)) (.branch 36 (.leaf 3010609829) (.leaf 2954329095)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2899755397) (.leaf 2846814028)) (.branch 40 (.leaf 2795434167) (.leaf 2745548654))) (.branch 43 (.branch 42 (.leaf 2697093782) (.leaf 2650009102)) (.branch 44 (.leaf 2604237243) (.leaf 2559723733))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2516416847) (.branch 47 (.leaf 2474267447) (.leaf 2433228844))) (.branch 50 (.branch 49 (.leaf 2393256661) (.leaf 2354308711)) (.branch 51 (.leaf 2316344872) (.leaf 2279326980)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2243218723) (.leaf 2207985538)) (.branch 55 (.leaf 2173594522) (.leaf 2140014342))) (.branch 58 (.branch 57 (.leaf 2107215152) (.leaf 2075168513)) (.branch 59 (.leaf 2043847321) (.leaf 2013225736))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1983279118) (.branch 62 (.leaf 1953983960) (.leaf 1925317834))) (.branch 65 (.branch 64 (.leaf 1897259336) (.leaf 1869788026)) (.branch 66 (.leaf 1842884389) (.leaf 1816529779)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1790706380) (.leaf 1765397162)) (.branch 70 (.leaf 1740585841) (.leaf 1716256843))) (.branch 73 (.branch 72 (.leaf 1692395267) (.leaf 1668986853)) (.branch 74 (.leaf 1646017949) (.leaf 1623475479))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1601346919) (.branch 77 (.leaf 1579620267) (.leaf 1558284018))) (.branch 80 (.branch 79 (.leaf 1537327138) (.leaf 1516739045)) (.branch 81 (.leaf 1496509584) (.leaf 1476629008)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1457087955) (.leaf 1437877436)) (.branch 85 (.leaf 1418988812) (.leaf 1400413778))) (.branch 88 (.branch 87 (.leaf 1382144350) (.leaf 1364172846)) (.branch 89 (.leaf 1346491876) (.leaf 1329094325)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1311973342) (.branch 92 (.leaf 1295122328) (.leaf 1278534921))) (.branch 95 (.branch 94 (.leaf 1262204992) (.leaf 1246126628)) (.branch 96 (.leaf 1230294123) (.leaf 1214701975)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1199344866) (.leaf 1184217665)) (.branch 100 (.leaf 1169315411) (.leaf 1154633311))) (.branch 103 (.branch 102 (.leaf 1140166730) (.leaf 1125911185)) (.branch 104 (.leaf 1111862337) (.leaf 1098015986))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1084368068) (.leaf 1070914642)) (.branch 108 (.leaf 1057651891) (.leaf 1044576115))) (.branch 111 (.branch 110 (.leaf 1031683725) (.leaf 1018971239)) (.branch 112 (.leaf 1006435278) (.leaf 994072562)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 981879905) (.leaf 969854212)) (.branch 116 (.leaf 957992475) (.leaf 946291770))) (.branch 119 (.branch 118 (.leaf 934749251) (.leaf 923362153)) (.branch 120 (.leaf 912127782) (.leaf 901043515)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 31).prefactor = (142997943685943/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 31).cutoff/(generalMeanRows 31).c)).2 =
    (493250478944497/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 31).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 31).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 31).q*(generalMeanRows 31).c/2-2 = (23/50:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable014.value]
    have hcontinuation : (generalMeanRows 31).q*(generalMeanRows 31).cutoff/2-2 = (71/35:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable023.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 31).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 31

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 31).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 31).criticalRate j.val*(generalMeanRows 31).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 31).c*(generalMeanRows 31).criticalPoint j.val)).2-
      (generalMeanRows 31).J/2-(generalMeanRows 31).error (generalMeanGrid j.val)+
      (generalMeanRows 31).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 31).c)).2-
      (generalMeanRows 31).J/2-(generalMeanRows 31).error 4 := by
  have he : (generalMeanRows 31).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 31) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 31)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0031

/-! Kernel-checked entropy margins for general spectral rectangle 32. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0032
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7287950385) (.branch 2 (.leaf 7053747577) (.leaf 6830705898))) (.branch 5 (.branch 4 (.leaf 6618158303) (.leaf 6415485472)) (.branch 6 (.leaf 6222111637) (.leaf 6037500863)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5861153722) (.leaf 5692604311)) (.branch 10 (.leaf 5531417563) (.leaf 5377186826))) (.branch 13 (.branch 12 (.leaf 5229531673) (.leaf 5088095911)) (.branch 14 (.leaf 4952545780) (.leaf 4822568307))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4697869806) (.branch 17 (.leaf 4578174504) (.leaf 4463223289))) (.branch 20 (.branch 19 (.leaf 4352772555) (.leaf 4246593142)) (.branch 21 (.leaf 4144469364) (.leaf 4046198111)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3951588018) (.leaf 3860458700)) (.branch 25 (.leaf 3772640046) (.leaf 3687971560))) (.branch 28 (.branch 27 (.leaf 3606301753) (.leaf 3527487582)) (.branch 29 (.leaf 3451393920) (.leaf 3377893073)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3306864322) (.branch 32 (.leaf 3238193506) (.leaf 3171772621))) (.branch 35 (.branch 34 (.leaf 3107499455) (.leaf 3045277249)) (.branch 36 (.leaf 2985014367) (.leaf 2926624006)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2870023908) (.leaf 2815136100)) (.branch 40 (.leaf 2761886651) (.leaf 2710205435))) (.branch 43 (.branch 42 (.leaf 2660025921) (.leaf 2611284967)) (.branch 44 (.leaf 2563922631) (.leaf 2517881992))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2473108981) (.branch 47 (.leaf 2429552226) (.leaf 2387162902))) (.branch 50 (.branch 49 (.leaf 2345894590) (.leaf 2305703149)) (.branch 51 (.leaf 2266546591) (.leaf 2228384965)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2191180246) (.leaf 2154896233)) (.branch 55 (.leaf 2119498454) (.leaf 2084954070))) (.branch 58 (.branch 57 (.leaf 2051231792) (.leaf 2018301797)) (.branch 59 (.leaf 1986135654) (.leaf 1954706246))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1923987710) (.branch 62 (.leaf 1893955363) (.leaf 1864585648))) (.branch 65 (.branch 64 (.leaf 1835856072) (.leaf 1807745153)) (.branch 66 (.leaf 1780232369) (.leaf 1753298107)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1726923621) (.leaf 1701090982)) (.branch 70 (.leaf 1675783044) (.leaf 1650983399))) (.branch 73 (.branch 72 (.leaf 1626676345) (.leaf 1602846846)) (.branch 74 (.leaf 1579480503) (.leaf 1556563522))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1534082681) (.branch 77 (.leaf 1512025306) (.leaf 1490379244))) (.branch 80 (.branch 79 (.leaf 1469132834) (.leaf 1448274887)) (.branch 81 (.leaf 1427794662) (.leaf 1407681845)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1387926528) (.leaf 1368519188)) (.branch 85 (.leaf 1349450673) (.leaf 1330712182))) (.branch 88 (.branch 87 (.leaf 1312295247) (.leaf 1294191721)) (.branch 89 (.leaf 1276393760) (.leaf 1258893812)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1241684598) (.branch 92 (.leaf 1224759108) (.leaf 1208110581))) (.branch 95 (.branch 94 (.leaf 1191732497) (.leaf 1175618568)) (.branch 96 (.leaf 1159762721) (.leaf 1144159097)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1128802036) (.leaf 1113686069)) (.branch 100 (.leaf 1098805910) (.leaf 1084156449))) (.branch 103 (.branch 102 (.leaf 1069732742) (.leaf 1055530007)) (.branch 104 (.leaf 1041543613) (.leaf 1027769079))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1014202062) (.leaf 1000838354)) (.branch 108 (.leaf 987673878) (.leaf 974704677))) (.branch 111 (.branch 110 (.leaf 961926916) (.leaf 949336871)) (.branch 112 (.leaf 936930930) (.leaf 924705582)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 912657420) (.leaf 900783131)) (.branch 116 (.leaf 889079494) (.leaf 877543380))) (.branch 119 (.branch 118 (.leaf 866171743) (.leaf 854961619)) (.branch 120 (.leaf 843910125) (.leaf 833014452)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 32).prefactor = (5963706891135313/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 32).cutoff/(generalMeanRows 32).c)).2 =
    (240564559206077/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 32).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 32).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 32).q*(generalMeanRows 32).c/2-2 = (49/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable003.value]
    have hcontinuation : (generalMeanRows 32).q*(generalMeanRows 32).cutoff/2-2 = (71/35:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable023.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 32).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 32

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 32).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 32).criticalRate j.val*(generalMeanRows 32).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 32).c*(generalMeanRows 32).criticalPoint j.val)).2-
      (generalMeanRows 32).J/2-(generalMeanRows 32).error (generalMeanGrid j.val)+
      (generalMeanRows 32).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 32).c)).2-
      (generalMeanRows 32).J/2-(generalMeanRows 32).error 4 := by
  have he : (generalMeanRows 32).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 32) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 32)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0032

/-! Kernel-checked entropy margins for general spectral rectangle 33. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0033
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7438718447) (.branch 2 (.leaf 7194688458) (.leaf 6962291982))) (.branch 5 (.branch 4 (.leaf 6740834858) (.leaf 6529672582)) (.branch 6 (.leaf 6328205968) (.leaf 6135877269)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5952166723) (.leaf 5776589442)) (.branch 10 (.leaf 5608692616) (.leaf 5448052995))) (.branch 13 (.branch 12 (.leaf 5294274607) (.leaf 5146986690)) (.branch 14 (.leaf 5005841813) (.leaf 4870514167))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4740698001) (.branch 17 (.leaf 4616106198) (.leaf 4496468966))) (.branch 20 (.branch 19 (.leaf 4381532639) (.leaf 4271058579)) (.branch 21 (.leaf 4164822157) (.leaf 4062611823)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3964228243) (.leaf 3869483501)) (.branch 25 (.leaf 3778200364) (.leaf 3690211602))) (.branch 28 (.branch 27 (.leaf 3605359350) (.leaf 3523494525)) (.branch 29 (.leaf 3444476279) (.leaf 3368171494)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3294454306) (.branch 32 (.leaf 3223205671) (.leaf 3154312950))) (.branch 35 (.branch 34 (.leaf 3087669530) (.leaf 3023174464)) (.branch 36 (.leaf 2960732142) (.leaf 2900251973)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2841648102) (.leaf 2784839128)) (.branch 40 (.leaf 2729747853) (.leaf 2676301044))) (.branch 43 (.branch 42 (.leaf 2624429203) (.leaf 2574066362)) (.branch 44 (.leaf 2525149882) (.leaf 2477620268))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2431420994) (.branch 47 (.leaf 2386498340) (.leaf 2342801238))) (.branch 50 (.branch 49 (.leaf 2300281127) (.leaf 2258891816)) (.branch 51 (.leaf 2218589355) (.leaf 2179331917)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2141079681) (.leaf 2103794726)) (.branch 55 (.leaf 2067440931) (.leaf 2031983877))) (.branch 58 (.branch 57 (.leaf 1997390762) (.leaf 1963630310)) (.branch 59 (.leaf 1930672696) (.leaf 1898489466))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1867053473) (.branch 62 (.leaf 1836338801) (.leaf 1806320706))) (.branch 65 (.branch 64 (.leaf 1776975559) (.leaf 1748280781)) (.branch 66 (.leaf 1720214796) (.leaf 1692756981)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1665887611) (.leaf 1639587820)) (.branch 70 (.leaf 1613839558) (.leaf 1588625546))) (.branch 73 (.branch 72 (.leaf 1563929240) (.leaf 1539734798)) (.branch 74 (.leaf 1516027039) (.leaf 1492791416))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1470013981) (.branch 77 (.leaf 1447681359) (.leaf 1425780720))) (.branch 80 (.branch 79 (.leaf 1404299749) (.leaf 1383226627)) (.branch 81 (.leaf 1362550000) (.leaf 1342258966)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1322343046) (.leaf 1302792166)) (.branch 85 (.leaf 1283596639) (.leaf 1264747149))) (.branch 88 (.branch 87 (.leaf 1246234727) (.leaf 1228050743)) (.branch 89 (.leaf 1210186884) (.leaf 1192635143)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1175387803) (.branch 92 (.leaf 1158437426) (.leaf 1141776839))) (.branch 95 (.branch 94 (.leaf 1125399122) (.leaf 1109297595)) (.branch 96 (.leaf 1093465812) (.leaf 1077897547)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1062586784) (.leaf 1047527711)) (.branch 100 (.leaf 1032714707) (.leaf 1018142338))) (.branch 103 (.branch 102 (.leaf 1003805343) (.leaf 989698635)) (.branch 104 (.leaf 975817287) (.leaf 962156526))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 948711728) (.leaf 935478414)) (.branch 108 (.leaf 922452240) (.leaf 909628991))) (.branch 111 (.branch 110 (.leaf 897004581) (.leaf 884575043)) (.branch 112 (.leaf 872336524) (.leaf 860285286)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 848417694) (.leaf 836730217)) (.branch 116 (.leaf 825219423) (.leaf 813881972))) (.branch 119 (.branch 118 (.leaf 802714619) (.leaf 791714203)) (.branch 120 (.leaf 780877648) (.leaf 770201960)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 33).prefactor = (6217886594489377/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 33).cutoff/(generalMeanRows 33).c)).2 =
    (469152927365437/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 33).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 33).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 33).q*(generalMeanRows 33).c/2-2 = (13/25:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable005.value]
    have hcontinuation : (generalMeanRows 33).q*(generalMeanRows 33).cutoff/2-2 = (71/35:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable023.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 33).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 33

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 33).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 33).criticalRate j.val*(generalMeanRows 33).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 33).c*(generalMeanRows 33).criticalPoint j.val)).2-
      (generalMeanRows 33).J/2-(generalMeanRows 33).error (generalMeanGrid j.val)+
      (generalMeanRows 33).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 33).c)).2-
      (generalMeanRows 33).J/2-(generalMeanRows 33).error 4 := by
  have he : (generalMeanRows 33).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 33) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 33)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0033

/-! Kernel-checked entropy margins for general spectral rectangle 34. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0034
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6722235700) (.branch 2 (.leaf 6471729798) (.leaf 6233330278))) (.branch 5 (.branch 4 (.leaf 6006320509) (.leaf 5790035024)) (.branch 6 (.leaf 5583855027) (.leaf 5387204407)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5199546155) (.leaf 5020379163)) (.branch 10 (.leaf 4849235343) (.leaf 4685677022))) (.branch 13 (.branch 12 (.leaf 4529294593) (.leaf 4379704387)) (.branch 14 (.leaf 4236546733) (.leaf 4099484202))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3968199992) (.branch 17 (.leaf 3842396469) (.leaf 3721793813))) (.branch 20 (.branch 19 (.leaf 3606128792) (.leaf 3495153626)) (.branch 21 (.leaf 3388634946) (.leaf 3286352835)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3188099940) (.leaf 3093680656)) (.branch 25 (.leaf 3002910372) (.leaf 2915614764))) (.branch 28 (.branch 27 (.leaf 2831629153) (.leaf 2750797899)) (.branch 29 (.leaf 2672973840) (.leaf 2598017776)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2525797983) (.branch 32 (.leaf 2456189761) (.leaf 2389075016))) (.branch 35 (.branch 34 (.leaf 2324341866) (.leaf 2261884277)) (.branch 36 (.leaf 2201601722) (.leaf 2143398856)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2087185225) (.leaf 2032874980)) (.branch 40 (.leaf 1980386620) (.leaf 1929642740))) (.branch 43 (.branch 42 (.leaf 1880569807) (.leaf 1833097943)) (.branch 44 (.leaf 1787160719) (.leaf 1742694967))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1699640602) (.branch 47 (.leaf 1657940452) (.leaf 1617540102))) (.branch 50 (.branch 49 (.leaf 1578387744) (.leaf 1540434035)) (.branch 51 (.leaf 1503631973) (.leaf 1467936763)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1433305707) (.leaf 1399698092)) (.branch 55 (.leaf 1367075086) (.leaf 1335399640))) (.branch 58 (.branch 57 (.leaf 1304636396) (.leaf 1274751599)) (.branch 59 (.leaf 1245713017) (.leaf 1217489861))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1190052712) (.branch 62 (.leaf 1163373453) (.leaf 1137425203))) (.branch 65 (.branch 64 (.leaf 1112182253) (.leaf 1087620013)) (.branch 66 (.leaf 1063714949) (.leaf 1040444536)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1017787208) (.leaf 995722310)) (.branch 70 (.leaf 974230053) (.leaf 953291474))) (.branch 73 (.branch 72 (.leaf 932888393) (.leaf 913003379)) (.branch 74 (.leaf 893619713) (.leaf 874721352))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 856292901) (.branch 77 (.leaf 838319579) (.leaf 820787190))) (.branch 80 (.branch 79 (.leaf 803682101) (.leaf 786991208)) (.branch 81 (.leaf 770701918) (.leaf 754802123)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 739280177) (.leaf 724124877)) (.branch 85 (.leaf 709325442) (.leaf 694871492))) (.branch 88 (.branch 87 (.leaf 680753034) (.leaf 666960443)) (.branch 89 (.leaf 653484444) (.leaf 640316098)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 627446790) (.branch 92 (.leaf 614868210) (.leaf 602572341))) (.branch 95 (.branch 94 (.leaf 590551449) (.leaf 578798070)) (.branch 96 (.leaf 567304997) (.leaf 556065269)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 545072163) (.leaf 534319182)) (.branch 100 (.leaf 523800047) (.leaf 513508685))) (.branch 103 (.branch 102 (.leaf 503439225) (.leaf 493585987)) (.branch 104 (.leaf 483943475) (.leaf 474506369))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 465269519) (.leaf 456227936)) (.branch 108 (.leaf 447376790) (.leaf 438711399))) (.branch 111 (.branch 110 (.leaf 430227225) (.leaf 421919870)) (.branch 112 (.leaf 413785070) (.leaf 405818686)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 398016707) (.leaf 390375236)) (.branch 116 (.leaf 382890494) (.leaf 375558811))) (.branch 119 (.branch 118 (.leaf 368376623) (.leaf 361340467)) (.branch 120 (.leaf 354446980) (.leaf 347692894)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 34).prefactor = (3241449857252337/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 34).cutoff/(generalMeanRows 34).c)).2 =
    (389110219691899/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 34).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 34).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 34).q*(generalMeanRows 34).c/2-2 = (73/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable024.value]
    have hcontinuation : (generalMeanRows 34).q*(generalMeanRows 34).cutoff/2-2 = (71/35:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable023.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 34).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 34

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 34).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 34).criticalRate j.val*(generalMeanRows 34).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 34).c*(generalMeanRows 34).criticalPoint j.val)).2-
      (generalMeanRows 34).J/2-(generalMeanRows 34).error (generalMeanGrid j.val)+
      (generalMeanRows 34).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 34).c)).2-
      (generalMeanRows 34).J/2-(generalMeanRows 34).error 4 := by
  have he : (generalMeanRows 34).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 34) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 34)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0034

/-! Kernel-checked entropy margins for general spectral rectangle 35. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0035
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5918440527) (.branch 2 (.leaf 5667676228) (.leaf 5429457828))) (.branch 5 (.branch 4 (.leaf 5203042818) (.leaf 4987741534)) (.branch 6 (.leaf 4782912527) (.leaf 4587958429)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4402322261) (.leaf 4225484123)) (.branch 10 (.leaf 4056958216) (.leaf 3896290157))) (.branch 13 (.branch 12 (.leaf 3743054555) (.leaf 3596852807)) (.branch 14 (.leaf 3457311107) (.leaf 3324078624))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3196825848) (.branch 17 (.leaf 3075243072) (.leaf 2959039009))) (.branch 20 (.branch 19 (.leaf 2847939519) (.leaf 2741686443)) (.branch 21 (.leaf 2640036528) (.leaf 2542760438)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2449641845) (.leaf 2360476581)) (.branch 25 (.leaf 2275071862) (.leaf 2193245566))) (.branch 28 (.branch 27 (.leaf 2114825567) (.leaf 2039649107)) (.branch 29 (.leaf 1967562228) (.leaf 1898419232)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1832082182) (.branch 32 (.leaf 1768420438) (.leaf 1707310228))) (.branch 35 (.branch 34 (.leaf 1648634237) (.leaf 1592281235)) (.branch 36 (.leaf 1538145724) (.leaf 1486127607)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1436131879) (.leaf 1388068343)) (.branch 40 (.leaf 1341851336) (.leaf 1297399473))) (.branch 43 (.branch 42 (.leaf 1254635417) (.leaf 1213485649)) (.branch 44 (.leaf 1173880261) (.leaf 1135752761))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1099039886) (.branch 47 (.leaf 1063681427) (.leaf 1029620071))) (.branch 50 (.branch 49 (.leaf 996801239) (.leaf 965172948)) (.branch 51 (.leaf 934685672) (.leaf 905292213)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 876947580) (.leaf 849608875)) (.branch 55 (.leaf 823235185) (.leaf 797787480))) (.branch 58 (.branch 57 (.leaf 773228518) (.leaf 749522753)) (.branch 59 (.leaf 726636251) (.leaf 704536607))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 683192869) (.branch 62 (.leaf 662575467) (.leaf 642656144))) (.branch 65 (.branch 64 (.leaf 623407890) (.leaf 604804882)) (.branch 66 (.leaf 586822427) (.leaf 569436905)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 552625718) (.leaf 536367241)) (.branch 70 (.leaf 520640774) (.leaf 505426501))) (.branch 73 (.branch 72 (.leaf 490705445) (.leaf 476459430)) (.branch 74 (.leaf 462671040) (.leaf 449323589))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 436401082) (.branch 77 (.leaf 423888187) (.leaf 411770200))) (.branch 80 (.branch 79 (.leaf 400033019) (.leaf 388663116)) (.branch 81 (.leaf 377647510) (.leaf 366973743)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 356629856) (.leaf 346604366)) (.branch 85 (.leaf 336886247) (.leaf 327464906))) (.branch 88 (.branch 87 (.leaf 318330166) (.leaf 309472248)) (.branch 89 (.leaf 300881752) (.leaf 292549643)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 284467230) (.branch 92 (.leaf 276626158) (.leaf 269018387))) (.branch 95 (.branch 94 (.leaf 261636182) (.leaf 254472102)) (.branch 96 (.leaf 247518980) (.leaf 240769920)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 234218280) (.leaf 227857663)) (.branch 100 (.leaf 221681909) (.leaf 215685079))) (.branch 103 (.branch 102 (.leaf 209861454) (.leaf 204205519)) (.branch 104 (.leaf 198711958) (.leaf 193375646))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 188191640) (.leaf 183155173)) (.branch 108 (.leaf 178261644) (.leaf 173506616))) (.branch 111 (.branch 110 (.leaf 168885806) (.leaf 164395078)) (.branch 112 (.leaf 160030443) (.leaf 155788046)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 151664165) (.leaf 147655204)) (.branch 116 (.leaf 143757692) (.leaf 139968272))) (.branch 119 (.branch 118 (.leaf 136283700) (.leaf 132700844)) (.branch 120 (.leaf 129216671) (.leaf 125828253)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 35).prefactor = (1689801995808841/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 35).cutoff/(generalMeanRows 35).c)).2 =
    (147399770110331/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 35).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 35).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 35).q*(generalMeanRows 35).c/2-2 = (1/1:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable008.value]
    have hcontinuation : (generalMeanRows 35).q*(generalMeanRows 35).cutoff/2-2 = (71/35:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable023.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 35).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 35

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 35).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 35).criticalRate j.val*(generalMeanRows 35).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 35).c*(generalMeanRows 35).criticalPoint j.val)).2-
      (generalMeanRows 35).J/2-(generalMeanRows 35).error (generalMeanGrid j.val)+
      (generalMeanRows 35).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 35).c)).2-
      (generalMeanRows 35).J/2-(generalMeanRows 35).error 4 := by
  have he : (generalMeanRows 35).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 35) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 35)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0035

/-! Kernel-checked entropy margins for general spectral rectangle 36. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0036
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6296163228) (.branch 2 (.leaf 6092700381) (.leaf 5899095560))) (.branch 5 (.branch 4 (.leaf 5714741329) (.leaf 5539074623)) (.branch 6 (.leaf 5371572874) (.leaf 5211750550)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5059156051) (.leaf 4913368921)) (.branch 10 (.leaf 4773997336) (.leaf 4640675833))) (.branch 13 (.branch 12 (.leaf 4513063253) (.leaf 4390840875)) (.branch 14 (.leaf 4273710722) (.leaf 4161394010))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4053629741) (.branch 17 (.leaf 3950173409) (.leaf 3850795819))) (.branch 20 (.branch 19 (.leaf 3755282003) (.leaf 3663430222)) (.branch 21 (.leaf 3575051053) (.leaf 3489966541)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3408009424) (.leaf 3329022411)) (.branch 25 (.leaf 3252857523) (.leaf 3179375472))) (.branch 28 (.branch 27 (.leaf 3108445097) (.leaf 3039942836)) (.branch 29 (.leaf 2973752234) (.leaf 2909763491)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2847873041) (.branch 32 (.leaf 2787983154) (.leaf 2730001579))) (.branch 35 (.branch 34 (.leaf 2673841195) (.leaf 2619419702)) (.branch 36 (.leaf 2566659319) (.leaf 2515486511)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2465831734) (.leaf 2417629190)) (.branch 40 (.leaf 2370816605) (.leaf 2325335019))) (.branch 43 (.branch 42 (.leaf 2281128589) (.leaf 2238144405)) (.branch 44 (.leaf 2196332319) (.leaf 2155644781))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2116036692) (.branch 47 (.leaf 2077465261) (.leaf 2039889870))) (.branch 50 (.branch 49 (.leaf 2003271951) (.leaf 1967574871)) (.branch 51 (.leaf 1932763821) (.leaf 1898805712)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1865669079) (.leaf 1833323991)) (.branch 55 (.leaf 1801741965) (.leaf 1770895885))) (.branch 58 (.branch 57 (.leaf 1740759929) (.leaf 1711309495)) (.branch 59 (.leaf 1682521135) (.leaf 1654372494))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1626842250) (.branch 62 (.leaf 1599910056) (.leaf 1573556491))) (.branch 65 (.branch 64 (.leaf 1547763009) (.leaf 1522511891)) (.branch 66 (.leaf 1497786205) (.leaf 1473569761)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1449847073) (.leaf 1426603323)) (.branch 70 (.leaf 1403824327) (.leaf 1381496499))) (.branch 73 (.branch 72 (.leaf 1359606825) (.leaf 1338142828)) (.branch 74 (.leaf 1317092547) (.leaf 1296444506))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1276187691) (.branch 77 (.leaf 1256311529) (.leaf 1236805861))) (.branch 80 (.branch 79 (.leaf 1217660929) (.leaf 1198867348)) (.branch 81 (.leaf 1180416094) (.leaf 1162298484)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1144506157) (.leaf 1127031065)) (.branch 85 (.leaf 1109865451) (.leaf 1093001840))) (.branch 88 (.branch 87 (.leaf 1076433023) (.leaf 1060152048)) (.branch 89 (.leaf 1044152202) (.leaf 1028427006)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1012970201) (.branch 92 (.leaf 997775739) (.leaf 982837773))) (.branch 95 (.branch 94 (.leaf 968150648) (.leaf 953708893)) (.branch 96 (.leaf 939507212) (.leaf 925540478)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 911803724) (.leaf 898292135)) (.branch 100 (.leaf 885001044) (.leaf 871925926))) (.branch 103 (.branch 102 (.leaf 859062388) (.leaf 846406170)) (.branch 104 (.leaf 833953131) (.leaf 821699254))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 809640631) (.leaf 797773466)) (.branch 108 (.leaf 786094068) (.leaf 774598846))) (.branch 111 (.branch 110 (.leaf 763284306) (.leaf 752147048)) (.branch 112 (.leaf 741183759) (.leaf 730391216)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 719766274) (.leaf 709305874)) (.branch 116 (.leaf 699007027) (.leaf 688866824))) (.branch 119 (.branch 118 (.leaf 678882423) (.leaf 669051054)) (.branch 120 (.leaf 659370012) (.leaf 649836655)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 36).prefactor = (1123020520500103/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 36).cutoff/(generalMeanRows 36).c)).2 =
    (500901625680017/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 36).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 36).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 36).q*(generalMeanRows 36).c/2-2 = (223/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable017.value]
    have hcontinuation : (generalMeanRows 36).q*(generalMeanRows 36).cutoff/2-2 = (544/245:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable025.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 36).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 36

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 36).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 36).criticalRate j.val*(generalMeanRows 36).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 36).c*(generalMeanRows 36).criticalPoint j.val)).2-
      (generalMeanRows 36).J/2-(generalMeanRows 36).error (generalMeanGrid j.val)+
      (generalMeanRows 36).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 36).c)).2-
      (generalMeanRows 36).J/2-(generalMeanRows 36).error 4 := by
  have he : (generalMeanRows 36).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 36) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 36)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0036

/-! Kernel-checked entropy margins for general spectral rectangle 37. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0037
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6372405775) (.branch 2 (.leaf 6162312036) (.leaf 5962409760))) (.branch 5 (.branch 4 (.leaf 5772072069) (.leaf 5590717854)) (.branch 6 (.leaf 5417807780) (.leaf 5252840714)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5095350522) (.leaf 4944903196)) (.branch 10 (.leaf 4801094255) (.leaf 4663546409))) (.branch 13 (.branch 12 (.leaf 4531907434) (.leaf 4405848249)) (.branch 14 (.leaf 4285061165) (.leaf 4169258289))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4058170071) (.branch 17 (.leaf 3951543968) (.leaf 3849143232))) (.branch 20 (.branch 19 (.leaf 3750745784) (.leaf 3656143190)) (.branch 21 (.leaf 3565139719) (.leaf 3477551468)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3393205560) (.leaf 3311939407)) (.branch 25 (.leaf 3233600020) (.leaf 3158043380))) (.branch 28 (.branch 27 (.leaf 3085133850) (.leaf 3014743628)) (.branch 29 (.leaf 2946752249) (.leaf 2881046110)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2817518040) (.branch 32 (.leaf 2756066892) (.leaf 2696597168))) (.branch 35 (.branch 34 (.leaf 2639018668) (.leaf 2583246164)) (.branch 36 (.leaf 2529199094) (.leaf 2476801278)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2425980652) (.leaf 2376669024)) (.branch 40 (.leaf 2328801838) (.leaf 2282317959))) (.branch 43 (.branch 42 (.leaf 2237159471) (.leaf 2193271488)) (.branch 44 (.leaf 2150601974) (.leaf 2109101581))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2068723490) (.branch 47 (.leaf 2029423264) (.leaf 1991158718))) (.branch 50 (.branch 49 (.leaf 1953889781) (.leaf 1917578384)) (.branch 51 (.leaf 1882188343) (.leaf 1847685251)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1814036384) (.leaf 1781210601)) (.branch 55 (.leaf 1749178261) (.leaf 1717911138))) (.branch 58 (.branch 57 (.leaf 1687382342) (.leaf 1657566249)) (.branch 59 (.leaf 1628438429) (.leaf 1599975584))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1572155484) (.branch 62 (.leaf 1544956911) (.leaf 1518359607))) (.branch 65 (.branch 64 (.leaf 1492344218) (.leaf 1466892252)) (.branch 66 (.leaf 1441986028) (.leaf 1417608638)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1393743904) (.leaf 1370376341)) (.branch 70 (.leaf 1347491121) (.leaf 1325074038))) (.branch 73 (.branch 72 (.leaf 1303111480) (.leaf 1281590394)) (.branch 74 (.leaf 1260498262) (.leaf 1239823070))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1219553286) (.branch 77 (.leaf 1199677834) (.leaf 1180186075))) (.branch 80 (.branch 79 (.leaf 1161067779) (.leaf 1142313110)) (.branch 81 (.leaf 1123912608) (.leaf 1105857165)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1088138014) (.leaf 1070746710)) (.branch 85 (.leaf 1053675112) (.leaf 1036915376))) (.branch 88 (.branch 87 (.leaf 1020459935) (.leaf 1004301486)) (.branch 89 (.leaf 988432983) (.leaf 972847620)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 957538822) (.branch 92 (.leaf 942500235) (.leaf 927725716))) (.branch 95 (.branch 94 (.leaf 913209323) (.leaf 898945306)) (.branch 96 (.leaf 884928098) (.leaf 871152311)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 857612722) (.leaf 844304272)) (.branch 100 (.leaf 831222054) (.leaf 818361310))) (.branch 103 (.branch 102 (.leaf 805717424) (.leaf 793285915)) (.branch 104 (.leaf 781062432) (.leaf 769042750))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 757222764) (.leaf 745598483)) (.branch 108 (.leaf 734166026) (.leaf 722921622))) (.branch 111 (.branch 110 (.leaf 711861597) (.leaf 700982380)) (.branch 112 (.leaf 690280491) (.leaf 679752543)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 669395235) (.leaf 659205352)) (.branch 116 (.leaf 649179760) (.leaf 639315403))) (.branch 119 (.branch 118 (.leaf 629609299) (.leaf 620058541)) (.branch 120 (.leaf 610660292) (.leaf 601411783)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 37).prefactor = (5803389675077831/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 37).cutoff/(generalMeanRows 37).c)).2 =
    (49020633656327/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 37).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 37).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 37).q*(generalMeanRows 37).c/2-2 = (117/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable009.value]
    have hcontinuation : (generalMeanRows 37).q*(generalMeanRows 37).cutoff/2-2 = (544/245:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable025.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 37).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 37

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 37).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 37).criticalRate j.val*(generalMeanRows 37).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 37).c*(generalMeanRows 37).criticalPoint j.val)).2-
      (generalMeanRows 37).J/2-(generalMeanRows 37).error (generalMeanGrid j.val)+
      (generalMeanRows 37).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 37).c)).2-
      (generalMeanRows 37).J/2-(generalMeanRows 37).error 4 := by
  have he : (generalMeanRows 37).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 37) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 37)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0037

/-! Kernel-checked entropy margins for general spectral rectangle 38. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0038
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6066771017) (.branch 2 (.leaf 5851228202) (.leaf 5646228751))) (.branch 5 (.branch 4 (.leaf 5451127884) (.leaf 5265327804)) (.branch 6 (.leaf 5088273585) (.leaf 4919449506)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4758375759) (.leaf 4604605499)) (.branch 10 (.leaf 4457722180) (.leaf 4317337150))) (.branch 13 (.branch 12 (.leaf 4183087476) (.leaf 4054633967)) (.branch 14 (.leaf 3931659378) (.leaf 3813866774))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3700978041) (.branch 17 (.leaf 3592732512) (.leaf 3488885727))) (.branch 20 (.branch 19 (.leaf 3389208277) (.leaf 3293484758)) (.branch 21 (.leaf 3201512799) (.leaf 3113102172)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3028073967) (.leaf 2946259835)) (.branch 25 (.leaf 2867501288) (.leaf 2791649045))) (.branch 28 (.branch 27 (.leaf 2718562437) (.leaf 2648108845)) (.branch 29 (.leaf 2580163187) (.leaf 2514607439)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2451330184) (.branch 32 (.leaf 2390226203) (.leaf 2331196089))) (.branch 35 (.branch 34 (.leaf 2274145884) (.leaf 2218986747)) (.branch 36 (.leaf 2165634645) (.leaf 2114010056)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2064037700) (.leaf 2015646287)) (.branch 40 (.leaf 1968768278) (.leaf 1923339663))) (.branch 43 (.branch 42 (.leaf 1879299755) (.leaf 1836590994)) (.branch 44 (.leaf 1795158768) (.leaf 1754951239))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1715919187) (.branch 47 (.leaf 1678015858) (.leaf 1641196827))) (.branch 50 (.branch 49 (.leaf 1605419862) (.leaf 1570644803)) (.branch 51 (.leaf 1536833448) (.leaf 1503949439)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1471958163) (.leaf 1440826659)) (.branch 55 (.leaf 1410523520) (.leaf 1381018814))) (.branch 58 (.branch 57 (.leaf 1352284001) (.leaf 1324291862)) (.branch 59 (.leaf 1297016423) (.leaf 1270432889))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1244517586) (.branch 62 (.leaf 1219247897) (.leaf 1194602209))) (.branch 65 (.branch 64 (.leaf 1170559858) (.leaf 1147101083)) (.branch 66 (.leaf 1124206975) (.leaf 1101859438)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1080041142) (.leaf 1058735490)) (.branch 70 (.leaf 1037926575) (.leaf 1017599149))) (.branch 73 (.branch 72 (.leaf 997738590) (.leaf 978330866)) (.branch 74 (.leaf 959362515) (.leaf 940820606))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 922692722) (.branch 77 (.leaf 904966930) (.leaf 887631760))) (.branch 80 (.branch 79 (.leaf 870676180) (.leaf 854089580)) (.branch 81 (.leaf 837861746) (.leaf 821982845)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 806443408) (.leaf 791234309)) (.branch 85 (.leaf 776346753) (.leaf 761772260))) (.branch 88 (.branch 87 (.leaf 747502650) (.leaf 733530028)) (.branch 89 (.leaf 719846774) (.leaf 706445529)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 693319185) (.branch 92 (.leaf 680460872) (.leaf 667863950))) (.branch 95 (.branch 94 (.leaf 655521994) (.leaf 643428793)) (.branch 96 (.leaf 631578334) (.leaf 619964795)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 608582540) (.leaf 597426109)) (.branch 100 (.leaf 586490209) (.leaf 575769711))) (.branch 103 (.branch 102 (.leaf 565259642) (.leaf 554955177)) (.branch 104 (.leaf 544851634) (.leaf 534944470))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 525229274) (.leaf 515701762)) (.branch 108 (.leaf 506357773) (.leaf 497193262))) (.branch 111 (.branch 110 (.leaf 488204299) (.leaf 479387063)) (.branch 112 (.leaf 470737837) (.leaf 462253005)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 453929049) (.leaf 445762547)) (.branch 116 (.leaf 437750163) (.leaf 429888654))) (.branch 119 (.branch 118 (.leaf 422174856) (.leaf 414605691)) (.branch 120 (.leaf 407178157) (.leaf 399889329)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 38).prefactor = (5997990438465347/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 38).cutoff/(generalMeanRows 38).c)).2 =
    (448533640162701/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 38).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 38).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 38).q*(generalMeanRows 38).c/2-2 = (139/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable026.value]
    have hcontinuation : (generalMeanRows 38).q*(generalMeanRows 38).cutoff/2-2 = (544/245:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable025.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 38).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 38

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 38).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 38).criticalRate j.val*(generalMeanRows 38).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 38).c*(generalMeanRows 38).criticalPoint j.val)).2-
      (generalMeanRows 38).J/2-(generalMeanRows 38).error (generalMeanGrid j.val)+
      (generalMeanRows 38).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 38).c)).2-
      (generalMeanRows 38).J/2-(generalMeanRows 38).error 4 := by
  have he : (generalMeanRows 38).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 38) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 38)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0038

/-! Kernel-checked entropy margins for general spectral rectangle 39. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0039
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5465516978) (.branch 2 (.leaf 5248144697) (.leaf 5041666813))) (.branch 5 (.branch 4 (.leaf 4845420292) (.leaf 4658790213)) (.branch 6 (.leaf 4481205564) (.leaf 4312135481)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4151085877) (.leaf 3997596425)) (.branch 10 (.leaf 3851237823) (.leaf 3711609342))) (.branch 13 (.branch 12 (.leaf 3578336592) (.leaf 3451069504)) (.branch 14 (.leaf 3329480492) (.leaf 3213262780))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3102128877) (.branch 17 (.leaf 2995809178) (.leaf 2894050688))) (.branch 20 (.branch 19 (.leaf 2796615850) (.leaf 2703281468)) (.branch 21 (.leaf 2613837719) (.leaf 2528087241)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2445844292) (.leaf 2366933975)) (.branch 25 (.leaf 2291191523) (.leaf 2218461633))) (.branch 28 (.branch 27 (.leaf 2148597855) (.leaf 2081462023)) (.branch 29 (.leaf 2016923725) (.leaf 1954859816)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1895153959) (.branch 32 (.leaf 1837696206) (.leaf 1782382602))) (.branch 35 (.branch 34 (.leaf 1729114815) (.leaf 1677799800)) (.branch 36 (.leaf 1628349475) (.leaf 1580680426)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1534713628) (.leaf 1490374187)) (.branch 40 (.leaf 1447591095) (.leaf 1406297005))) (.branch 43 (.branch 42 (.leaf 1366428017) (.leaf 1327923481)) (.branch 44 (.leaf 1290725809) (.leaf 1254780302))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1220034986) (.branch 47 (.leaf 1186440459) (.leaf 1153949744))) (.branch 50 (.branch 49 (.leaf 1122518160) (.leaf 1092103189)) (.branch 51 (.leaf 1062664360) (.leaf 1034163137)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1006562812) (.leaf 979828409)) (.branch 55 (.leaf 953926589) (.leaf 928825559))) (.branch 58 (.branch 57 (.leaf 904494998) (.leaf 880905972)) (.branch 59 (.leaf 858030862) (.leaf 835843299))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 814318095) (.branch 62 (.leaf 793431183) (.leaf 773159560))) (.branch 65 (.branch 64 (.leaf 753481233) (.leaf 734375164)) (.branch 66 (.leaf 715821227) (.leaf 697800159)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 680293514) (.leaf 663283631)) (.branch 70 (.leaf 646753584) (.leaf 630687156))) (.branch 73 (.branch 72 (.leaf 615068797) (.leaf 599883596)) (.branch 74 (.leaf 585117248) (.leaf 570756024))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 556786748) (.branch 77 (.leaf 543196765) (.leaf 529973920))) (.branch 80 (.branch 79 (.leaf 517106533) (.leaf 504583378)) (.branch 81 (.leaf 492393662) (.leaf 480527003)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 468973414) (.leaf 457723284)) (.branch 85 (.leaf 446767359) (.leaf 436096730))) (.branch 88 (.branch 87 (.leaf 425702813) (.leaf 415577340)) (.branch 89 (.leaf 405712339) (.leaf 396100127)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 386733293) (.branch 92 (.leaf 377604688) (.leaf 368707414))) (.branch 95 (.branch 94 (.leaf 360034815) (.leaf 351580461)) (.branch 96 (.leaf 343338145) (.leaf 335301872)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 327465847) (.leaf 319824471)) (.branch 100 (.leaf 312372330) (.leaf 305104190))) (.branch 103 (.branch 102 (.leaf 298014987) (.leaf 291099824)) (.branch 104 (.leaf 284353960) (.leaf 277772806))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 271351922) (.leaf 265087004)) (.branch 108 (.leaf 258973888) (.leaf 253008535))) (.branch 111 (.branch 110 (.leaf 247187035) (.leaf 241505596)) (.branch 112 (.leaf 235960542) (.leaf 230548311)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 225265445) (.leaf 220108591)) (.branch 116 (.leaf 215074496) (.leaf 210160005))) (.branch 119 (.branch 118 (.leaf 205362051) (.leaf 200677662)) (.branch 120 (.leaf 196103948) (.leaf 191638106)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 39).prefactor = (1239823320995217/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 39).cutoff/(generalMeanRows 39).c)).2 =
    (379540768675747/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 39).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 39).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 39).q*(generalMeanRows 39).c/2-2 = (71/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable027.value]
    have hcontinuation : (generalMeanRows 39).q*(generalMeanRows 39).cutoff/2-2 = (544/245:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable025.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 39).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 39

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 39).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 39).criticalRate j.val*(generalMeanRows 39).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 39).c*(generalMeanRows 39).criticalPoint j.val)).2-
      (generalMeanRows 39).J/2-(generalMeanRows 39).error (generalMeanGrid j.val)+
      (generalMeanRows 39).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 39).c)).2-
      (generalMeanRows 39).J/2-(generalMeanRows 39).error 4 := by
  have he : (generalMeanRows 39).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 39) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 39)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0039

/-! Kernel-checked entropy margins for general spectral rectangle 40. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0040
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4964194725) (.branch 2 (.leaf 4747331601) (.leaf 4541681217))) (.branch 5 (.branch 4 (.leaf 4346559830) (.leaf 4161333154)) (.branch 6 (.leaf 3985412044) (.leaf 3818248632)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3659332869) (.leaf 3508189418)) (.branch 10 (.leaf 3364374859) (.leaf 3227475157))) (.branch 13 (.branch 12 (.leaf 3097103383) (.leaf 2972897629)) (.branch 14 (.leaf 2854519134) (.leaf 2741650558))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2633994417) (.branch 17 (.leaf 2531271654) (.leaf 2433220321))) (.branch 20 (.branch 19 (.leaf 2339594384) (.leaf 2250162611)) (.branch 21 (.leaf 2164707563) (.leaf 2083024653)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2004921286) (.leaf 1930216065)) (.branch 25 (.leaf 1858738049) (.leaf 1790326082))) (.branch 28 (.branch 27 (.leaf 1724828151) (.leaf 1662100812)) (.branch 29 (.leaf 1602008642) (.leaf 1544423736)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1489225243) (.branch 32 (.leaf 1436298925) (.leaf 1385536756))) (.branch 35 (.branch 34 (.leaf 1336836543) (.leaf 1290101575)) (.branch 36 (.leaf 1245240293) (.leaf 1202165985)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1160796500) (.leaf 1121053979)) (.branch 40 (.leaf 1082864609) (.leaf 1046158382))) (.branch 43 (.branch 42 (.leaf 1010868883) (.leaf 976933081)) (.branch 44 (.leaf 944291137) (.leaf 912886225))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 882664363) (.branch 47 (.leaf 853574252) (.leaf 825567131))) (.branch 50 (.branch 49 (.leaf 798596634) (.leaf 772618660)) (.branch 51 (.leaf 747591250) (.leaf 723474469)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 700230299) (.leaf 677822534)) (.branch 55 (.leaf 656216687) (.leaf 635379895))) (.branch 58 (.branch 57 (.leaf 615280834) (.leaf 595889642)) (.branch 59 (.leaf 577177836) (.leaf 559118247))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 541684949) (.branch 62 (.leaf 524853195) (.leaf 508599357))) (.branch 65 (.branch 64 (.leaf 492900869) (.leaf 477736175)) (.branch 66 (.leaf 463084676) (.leaf 448926684)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 435243373) (.leaf 422016742)) (.branch 70 (.leaf 409229569) (.leaf 396865377))) (.branch 73 (.branch 72 (.leaf 384908394) (.leaf 373343521)) (.branch 74 (.leaf 362156301) (.leaf 351332883))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 340860000) (.branch 77 (.leaf 330724934) (.leaf 320915497))) (.branch 80 (.branch 79 (.leaf 311420001) (.leaf 302227237)) (.branch 81 (.leaf 293326451) (.leaf 284707327)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 276359961) (.leaf 268274847)) (.branch 85 (.leaf 260442856) (.leaf 252855222))) (.branch 88 (.branch 87 (.leaf 245503520) (.leaf 238379658)) (.branch 89 (.leaf 231475856) (.leaf 224784637)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 218298811) (.branch 92 (.leaf 212011461) (.leaf 205915934))) (.branch 95 (.branch 94 (.leaf 200005830) (.leaf 194274988)) (.branch 96 (.leaf 188717477) (.leaf 183327589)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 178099824) (.leaf 173028887)) (.branch 100 (.leaf 168109675) (.leaf 163337273))) (.branch 103 (.branch 102 (.leaf 158706942) (.leaf 154214113)) (.branch 104 (.leaf 149854385) (.leaf 145623509))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 141517390) (.leaf 137532076)) (.branch 108 (.leaf 133663755) (.leaf 129908748))) (.branch 111 (.branch 110 (.leaf 126263503) (.leaf 122724593)) (.branch 112 (.leaf 119288706) (.leaf 115952647)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 112713329) (.leaf 109567768)) (.branch 116 (.leaf 106513083) (.leaf 103546490))) (.branch 119 (.branch 118 (.leaf 100665297) (.leaf 97866904)) (.branch 120 (.leaf 95148796) (.leaf 92508541)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 40).prefactor = (6406986986115087/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 40).cutoff/(generalMeanRows 40).c)).2 =
    (315002247538181/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 40).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 40).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 40).q*(generalMeanRows 40).cutoff/2-2 = (544/245:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable025.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 40).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 40

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 40).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 40).criticalRate j.val*(generalMeanRows 40).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 40).c*(generalMeanRows 40).criticalPoint j.val)).2-
      (generalMeanRows 40).J/2-(generalMeanRows 40).error (generalMeanGrid j.val)+
      (generalMeanRows 40).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 40).c)).2-
      (generalMeanRows 40).J/2-(generalMeanRows 40).error 4 := by
  have he : (generalMeanRows 40).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 40) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 40)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0040

/-! Kernel-checked entropy margins for general spectral rectangle 41. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0041
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5398606179) (.branch 2 (.leaf 5227258891) (.leaf 5064295019))) (.branch 5 (.branch 4 (.leaf 4909178062) (.leaf 4761412031)) (.branch 6 (.leaf 4620537876) (.leaf 4486130292)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4357794842) (.leaf 4235165383)) (.branch 10 (.leaf 4117901734) (.leaf 4005687572))) (.branch 13 (.branch 12 (.leaf 3898228522) (.leaf 3795250434)) (.branch 14 (.leaf 3696497802) (.leaf 3601732334))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3510731647) (.branch 17 (.leaf 3423288067) (.leaf 3339207541))) (.branch 20 (.branch 19 (.leaf 3258308633) (.leaf 3180421604)) (.branch 21 (.leaf 3105387574) (.leaf 3033057739)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2963292662) (.leaf 2895961611)) (.branch 25 (.leaf 2830941957) (.leaf 2768118611))) (.branch 28 (.branch 27 (.leaf 2707383506) (.leaf 2648635120)) (.branch 29 (.leaf 2591778032) (.leaf 2536722515)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2483384152) (.branch 32 (.leaf 2431683488) (.leaf 2381545699))) (.branch 35 (.branch 34 (.leaf 2332900293) (.leaf 2285680825)) (.branch 36 (.leaf 2239824636) (.leaf 2195272611)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2151968950) (.leaf 2109860960)) (.branch 40 (.leaf 2068898856) (.leaf 2029035580))) (.branch 43 (.branch 42 (.leaf 1990226628) (.leaf 1952429896)) (.branch 44 (.leaf 1915605525) (.leaf 1879715769))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1844724863) (.branch 47 (.leaf 1810598899) (.leaf 1777305721))) (.branch 50 (.branch 49 (.leaf 1744814815) (.leaf 1713097208)) (.branch 51 (.leaf 1682125383) (.leaf 1651873188)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1622315755) (.leaf 1593429428)) (.branch 55 (.leaf 1565191691) (.leaf 1537581101))) (.branch 58 (.branch 57 (.leaf 1510577226) (.leaf 1484160590)) (.branch 59 (.leaf 1458312615) (.leaf 1433015571))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1408252530) (.branch 62 (.leaf 1384007321) (.leaf 1360264484))) (.branch 65 (.branch 64 (.leaf 1337009237) (.leaf 1314227431)) (.branch 66 (.leaf 1291905525) (.leaf 1270030544)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1248590054) (.leaf 1227572132)) (.branch 70 (.leaf 1206965336) (.leaf 1186758686))) (.branch 73 (.branch 72 (.leaf 1166941633) (.leaf 1147504039)) (.branch 74 (.leaf 1128436159) (.leaf 1109728617))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1091372387) (.branch 77 (.leaf 1073358780) (.leaf 1055679421))) (.branch 80 (.branch 79 (.leaf 1038326238) (.leaf 1021291447)) (.branch 81 (.leaf 1004567534) (.leaf 988147248)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 972023581) (.leaf 956189764)) (.branch 85 (.leaf 940639252) (.leaf 925365712))) (.branch 88 (.branch 87 (.leaf 910363017) (.leaf 895625236)) (.branch 89 (.leaf 881146621) (.leaf 866921604)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 852944788) (.branch 92 (.leaf 839210935) (.leaf 825714967))) (.branch 95 (.branch 94 (.leaf 812451951) (.leaf 799417099)) (.branch 96 (.leaf 786605759) (.leaf 774013411)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 761635658) (.leaf 749468227)) (.branch 100 (.leaf 737506959) (.leaf 725747806))) (.branch 103 (.branch 102 (.leaf 714186828) (.leaf 702820187)) (.branch 104 (.leaf 691644144) (.leaf 680655056))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 669849371) (.leaf 659223625)) (.branch 108 (.leaf 648774440) (.leaf 638498520))) (.branch 111 (.branch 110 (.leaf 628392648) (.leaf 618453683)) (.branch 112 (.leaf 608678559) (.leaf 599064280)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 589607921) (.leaf 580306621)) (.branch 116 (.leaf 571157586) (.leaf 562158083))) (.branch 119 (.branch 118 (.leaf 553305441) (.leaf 544597045)) (.branch 120 (.leaf 536030339) (.leaf 527602821)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 41).prefactor = (5183689353571203/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 41).cutoff/(generalMeanRows 41).c)).2 =
    (107692945451133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 41).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 41).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 41).q*(generalMeanRows 41).c/2-2 = (49/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable011.value]
    have hcontinuation : (generalMeanRows 41).q*(generalMeanRows 41).cutoff/2-2 = (52/21:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable010.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 41).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 41

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 41).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 41).criticalRate j.val*(generalMeanRows 41).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 41).c*(generalMeanRows 41).criticalPoint j.val)).2-
      (generalMeanRows 41).J/2-(generalMeanRows 41).error (generalMeanGrid j.val)+
      (generalMeanRows 41).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 41).c)).2-
      (generalMeanRows 41).J/2-(generalMeanRows 41).error 4 := by
  have he : (generalMeanRows 41).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 41) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 41)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0041

/-! Kernel-checked entropy margins for general spectral rectangle 42. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0042
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5539471414) (.branch 2 (.leaf 5363653181) (.leaf 5196437110))) (.branch 5 (.branch 4 (.leaf 5037272703) (.leaf 4885651029)) (.branch 6 (.leaf 4741101061) (.leaf 4603186394)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4471502302) (.leaf 4345673086)) (.branch 10 (.leaf 4225349690) (.leaf 4110207535))) (.branch 13 (.branch 12 (.leaf 3999944569) (.leaf 3894279485)) (.branch 14 (.leaf 3792950111) (.leaf 3695711939))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3602336780) (.branch 17 (.leaf 3512611545) (.leaf 3426337115))) (.branch 20 (.branch 19 (.leaf 3343327320) (.leaf 3263407994)) (.branch 21 (.leaf 3186416110) (.leaf 3112198980)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3040613530) (.leaf 2971525618)) (.branch 25 (.leaf 2904809413) (.leaf 2840346825))) (.branch 28 (.branch 27 (.leaf 2778026965) (.leaf 2717745664)) (.branch 29 (.leaf 2659405010) (.leaf 2602912936)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2548182821) (.branch 32 (.leaf 2495133137) (.leaf 2443687109))) (.branch 35 (.branch 34 (.leaf 2393772403) (.leaf 2345320843)) (.branch 36 (.leaf 2298268133) (.leaf 2252553617)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2208120039) (.leaf 2164913330)) (.branch 40 (.leaf 2122882406) (.leaf 2081978981))) (.branch 43 (.branch 42 (.leaf 2042157392) (.leaf 2003374434)) (.branch 44 (.leaf 1965589209) (.leaf 1928762986))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1892859065) (.branch 47 (.leaf 1857842656) (.leaf 1823680763))) (.branch 50 (.branch 49 (.leaf 1790342075) (.leaf 1757796864)) (.branch 51 (.leaf 1726016895) (.leaf 1694975332)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1664646661) (.leaf 1635006606)) (.branch 55 (.leaf 1606032065) (.leaf 1577701035))) (.branch 58 (.branch 57 (.leaf 1549992551) (.leaf 1522886628)) (.branch 59 (.leaf 1496364205) (.leaf 1470407088))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1444997908) (.branch 62 (.leaf 1420120071) (.leaf 1395757716))) (.branch 65 (.branch 64 (.leaf 1371895671) (.leaf 1348519423)) (.branch 66 (.leaf 1325615073) (.leaf 1303169311)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1281169377) (.leaf 1259603036)) (.branch 70 (.leaf 1238458550) (.leaf 1217724650))) (.branch 73 (.branch 72 (.leaf 1197390512) (.leaf 1177445736)) (.branch 74 (.leaf 1157880320) (.leaf 1138684643))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1119849447) (.branch 77 (.leaf 1101365812) (.leaf 1083225147))) (.branch 80 (.branch 79 (.leaf 1065419170) (.leaf 1047939892)) (.branch 81 (.leaf 1030779604) (.leaf 1013930865)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 997386485) (.leaf 981139518)) (.branch 85 (.leaf 965183248) (.leaf 949511177))) (.branch 88 (.branch 87 (.leaf 934117019) (.leaf 918994686)) (.branch 89 (.leaf 904138282) (.leaf 889542094)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 875200582) (.branch 92 (.leaf 861108373) (.leaf 847260256))) (.branch 95 (.branch 94 (.leaf 833651170) (.leaf 820276201)) (.branch 96 (.leaf 807130577) (.leaf 794209657)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 781508934) (.leaf 769024019)) (.branch 100 (.leaf 756750647) (.leaf 744684664))) (.branch 103 (.branch 102 (.leaf 732822026) (.leaf 721158796)) (.branch 104 (.leaf 709691138) (.leaf 698415313))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 687327676) (.leaf 676424674)) (.branch 108 (.leaf 665702840) (.leaf 655158791))) (.branch 111 (.branch 110 (.leaf 644789228) (.leaf 634590926)) (.branch 112 (.leaf 624560741) (.leaf 614695598)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 604992495) (.leaf 595448498)) (.branch 116 (.leaf 586060738) (.leaf 576826412))) (.branch 119 (.branch 118 (.leaf 567742778) (.leaf 558807155)) (.branch 120 (.leaf 550016919) (.leaf 541369503)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 42).prefactor = (5318946788015599/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 42).cutoff/(generalMeanRows 42).c)).2 =
    (107692945451133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 42).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 42).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 42).q*(generalMeanRows 42).c/2-2 = (49/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable011.value]
    have hcontinuation : (generalMeanRows 42).q*(generalMeanRows 42).cutoff/2-2 = (52/21:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable010.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 42).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 42

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 42).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 42).criticalRate j.val*(generalMeanRows 42).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 42).c*(generalMeanRows 42).criticalPoint j.val)).2-
      (generalMeanRows 42).J/2-(generalMeanRows 42).error (generalMeanGrid j.val)+
      (generalMeanRows 42).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 42).c)).2-
      (generalMeanRows 42).J/2-(generalMeanRows 42).error 4 := by
  have he : (generalMeanRows 42).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 42) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 42)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0042

/-! Kernel-checked entropy margins for general spectral rectangle 43. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0043
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5684012231) (.branch 2 (.leaf 5503606392) (.leaf 5332027170))) (.branch 5 (.branch 4 (.leaf 5168709704) (.leaf 5013131783)) (.branch 6 (.leaf 4864810088) (.leaf 4723296829)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4588176718) (.leaf 4459064255)) (.branch 10 (.leaf 4335601273) (.leaf 4217454727))) (.branch 13 (.branch 12 (.leaf 4104314681) (.leaf 3995892490)) (.branch 14 (.leaf 3891919140) (.leaf 3792143742))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3696332157) (.branch 17 (.leaf 3604265730) (.leaf 3515740151))) (.branch 20 (.branch 19 (.leaf 3430564391) (.leaf 3348559739)) (.branch 21 (.leaf 3269558914) (.leaf 3193405245)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3119951923) (.leaf 3049061308)) (.branch 25 (.leaf 2980604285) (.leaf 2914459681))) (.branch 28 (.branch 27 (.leaf 2850513716) (.leaf 2788659501)) (.branch 29 (.leaf 2728796572) (.leaf 2670830456)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2614672274) (.branch 32 (.leaf 2560238371) (.leaf 2507449967))) (.branch 35 (.branch 34 (.leaf 2456232842) (.leaf 2406517041)) (.branch 36 (.leaf 2358236590) (.leaf 2311329250)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2265736271) (.leaf 2221402174)) (.branch 40 (.leaf 2178274542) (.leaf 2136303829))) (.branch 43 (.branch 42 (.leaf 2095443180) (.leaf 2055648262)) (.branch 44 (.leaf 2016877111) (.leaf 1979089985))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1942249228) (.branch 47 (.leaf 1906319140) (.leaf 1871265864))) (.branch 50 (.branch 49 (.leaf 1837057273) (.leaf 1803662864)) (.branch 51 (.leaf 1771053664) (.leaf 1739202137)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1708082102) (.leaf 1677668653)) (.branch 55 (.leaf 1647938083) (.leaf 1618867814))) (.branch 58 (.branch 57 (.leaf 1590436336) (.leaf 1562623141)) (.branch 59 (.leaf 1535408671) (.leaf 1508774258))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1482702079) (.branch 62 (.leaf 1457175108) (.leaf 1432177068))) (.branch 65 (.branch 64 (.leaf 1407692394) (.leaf 1383706191)) (.branch 66 (.leaf 1360204201) (.leaf 1337172764)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1314598788) (.leaf 1292469719)) (.branch 70 (.leaf 1270773512) (.leaf 1249498605))) (.branch 73 (.branch 72 (.leaf 1228633891) (.leaf 1208168697)) (.branch 74 (.leaf 1188092763) (.leaf 1168396216))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1149069555) (.branch 77 (.leaf 1130103629) (.leaf 1111489622))) (.branch 80 (.branch 79 (.leaf 1093219035) (.leaf 1075283672)) (.branch 81 (.leaf 1057675623) (.leaf 1040387251)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1023411180) (.leaf 1006740283)) (.branch 85 (.leaf 990367668) (.leaf 974286668))) (.branch 88 (.branch 87 (.leaf 958490831) (.leaf 942973913)) (.branch 89 (.leaf 927729863) (.leaf 912752818)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 898037094) (.branch 92 (.leaf 883577179) (.leaf 869367724))) (.branch 95 (.branch 94 (.leaf 855403538) (.leaf 841679577)) (.branch 96 (.leaf 828190946) (.leaf 814932882)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 801900760) (.leaf 789090078)) (.branch 100 (.leaf 776496458) (.leaf 764115638))) (.branch 103 (.branch 102 (.leaf 751943470) (.leaf 739975913)) (.branch 104 (.leaf 728209031) (.leaf 716638987))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 705262042) (.leaf 694074548)) (.branch 108 (.leaf 683072950) (.leaf 672253777))) (.branch 111 (.branch 110 (.leaf 661613642) (.leaf 651149238)) (.branch 112 (.leaf 640857336) (.leaf 630734783)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 620778498) (.leaf 610985470)) (.branch 116 (.leaf 601352756) (.leaf 591877480))) (.branch 119 (.branch 118 (.leaf 582556828) (.leaf 573388049)) (.branch 120 (.leaf 564368450) (.leaf 555495398)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 43).prefactor = (5457733479775513/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 43).cutoff/(generalMeanRows 43).c)).2 =
    (107692945451133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 43).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 43).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 43).q*(generalMeanRows 43).c/2-2 = (49/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable011.value]
    have hcontinuation : (generalMeanRows 43).q*(generalMeanRows 43).cutoff/2-2 = (52/21:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable010.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 43).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 43

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 43).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 43).criticalRate j.val*(generalMeanRows 43).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 43).c*(generalMeanRows 43).criticalPoint j.val)).2-
      (generalMeanRows 43).J/2-(generalMeanRows 43).error (generalMeanGrid j.val)+
      (generalMeanRows 43).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 43).c)).2-
      (generalMeanRows 43).J/2-(generalMeanRows 43).error 4 := by
  have he : (generalMeanRows 43).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 43) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 43)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0043

/-! Kernel-checked entropy margins for general spectral rectangle 44. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0044
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5757690856) (.branch 2 (.leaf 5574946518) (.leaf 5401143213))) (.branch 5 (.branch 4 (.leaf 5235708755) (.leaf 5078114165)) (.branch 6 (.leaf 4927869861) (.leaf 4784522246)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4647650649) (.leaf 4516864574)) (.branch 10 (.leaf 4391801212) (.leaf 4272123199))) (.branch 13 (.branch 12 (.leaf 4157516583) (.leaf 4047688976)) (.branch 14 (.leaf 3942367879) (.leaf 3841299150))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3744245613) (.branch 17 (.leaf 3650985782) (.leaf 3561312696))) (.branch 20 (.branch 19 (.leaf 3475032851) (.leaf 3391965219)) (.branch 21 (.leaf 3311940350) (.leaf 3234799545)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3160394090) (.leaf 3088584559)) (.branch 25 (.leaf 3019240167) (.leaf 2952238168))) (.branch 28 (.branch 27 (.leaf 2887463308) (.leaf 2824807312)) (.branch 29 (.leaf 2764168413) (.leaf 2705450915)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2648564787) (.branch 32 (.leaf 2593425288) (.leaf 2539952618))) (.branch 35 (.branch 34 (.leaf 2488071595) (.leaf 2437711355)) (.branch 36 (.leaf 2388805073) (.leaf 2341289699)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2295105725) (.leaf 2250196950)) (.branch 40 (.leaf 2206510279) (.leaf 2163995523))) (.branch 43 (.branch 42 (.leaf 2122605221) (.leaf 2082294464)) (.branch 44 (.leaf 2043020745) (.leaf 2004743806))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1967425502) (.branch 47 (.leaf 1931029673) (.leaf 1895522022))) (.branch 50 (.branch 49 (.leaf 1860870004) (.leaf 1827042722)) (.branch 51 (.leaf 1794010827) (.leaf 1761746427)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1730223001) (.leaf 1699415320)) (.branch 55 (.leaf 1669299369) (.leaf 1639852279))) (.branch 58 (.branch 57 (.leaf 1611052259) (.leaf 1582878538)) (.branch 59 (.leaf 1555311302) (.leaf 1528331642))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1501921505) (.branch 62 (.leaf 1476063642) (.leaf 1450741566))) (.branch 65 (.branch 64 (.leaf 1425939511) (.leaf 1401642389)) (.branch 66 (.leaf 1377835756) (.leaf 1354505776)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1331639186) (.leaf 1309223270)) (.branch 70 (.leaf 1287245828) (.leaf 1265695146))) (.branch 73 (.branch 72 (.leaf 1244559974) (.leaf 1223829502)) (.branch 74 (.leaf 1203493335) (.leaf 1183541473))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1163964291) (.branch 77 (.leaf 1144752521) (.leaf 1125897231))) (.branch 80 (.branch 79 (.leaf 1107389813) (.leaf 1089221964)) (.branch 81 (.leaf 1071385672) (.leaf 1053873200)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1036677079) (.leaf 1019790086)) (.branch 85 (.leaf 1003205242) (.leaf 986915793))) (.branch 88 (.branch 87 (.leaf 970915204) (.leaf 955197149)) (.branch 89 (.leaf 939755499) (.leaf 924584315)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 909677839) (.branch 92 (.leaf 895030489) (.leaf 880636845))) (.branch 95 (.branch 94 (.leaf 866491648) (.leaf 852589792)) (.branch 96 (.leaf 838926315) (.leaf 825496395)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 812295344) (.leaf 799318605)) (.branch 100 (.leaf 786561741) (.leaf 774020436))) (.branch 103 (.branch 102 (.leaf 761690487) (.leaf 749567801)) (.branch 104 (.leaf 737648391) (.leaf 725928371))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 714403953) (.leaf 703071443)) (.branch 108 (.leaf 691927237) (.leaf 680967821))) (.branch 111 (.branch 110 (.leaf 670189764) (.leaf 659589716)) (.branch 112 (.leaf 649164406) (.leaf 638910640)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 628825297) (.leaf 618905328)) (.branch 116 (.leaf 609147751) (.leaf 599549652))) (.branch 119 (.branch 118 (.leaf 590108182) (.leaf 580820553)) (.branch 120 (.leaf 571684038) (.leaf 562695970)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 44).prefactor = (1382119745419287/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 44).cutoff/(generalMeanRows 44).c)).2 =
    (107692945451133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 44).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 44).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 44).q*(generalMeanRows 44).c/2-2 = (49/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable011.value]
    have hcontinuation : (generalMeanRows 44).q*(generalMeanRows 44).cutoff/2-2 = (52/21:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable010.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 44).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 44

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 44).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 44).criticalRate j.val*(generalMeanRows 44).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 44).c*(generalMeanRows 44).criticalPoint j.val)).2-
      (generalMeanRows 44).J/2-(generalMeanRows 44).error (generalMeanGrid j.val)+
      (generalMeanRows 44).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 44).c)).2-
      (generalMeanRows 44).J/2-(generalMeanRows 44).error 4 := by
  have he : (generalMeanRows 44).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 44) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 44)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0044

/-! Kernel-checked entropy margins for general spectral rectangle 45. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0045
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7386863928) (.branch 2 (.leaf 7160149562) (.leaf 6943957597))) (.branch 5 (.branch 4 (.leaf 6737673265) (.leaf 6540725265)) (.branch 6 (.leaf 6352581949) (.leaf 6172747935)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6000761078) (.leaf 5836189751)) (.branch 10 (.leaf 5678630410) (.leaf 5527705394))) (.branch 13 (.branch 12 (.leaf 5383060935) (.leaf 5244365363)) (.branch 14 (.leaf 5111307466) (.leaf 4983595003))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4860953352) (.branch 17 (.leaf 4743124262) (.leaf 4629864725))) (.branch 20 (.branch 19 (.leaf 4520945928) (.leaf 4416152302)) (.branch 21 (.leaf 4315280640) (.leaf 4218139281)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4124547368) (.leaf 4034334152)) (.branch 25 (.leaf 3947338352) (.leaf 3863407562))) (.branch 28 (.branch 27 (.leaf 3782397699) (.leaf 3704172497)) (.branch 29 (.leaf 3628603024) (.leaf 3555567247)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3484949616) (.branch 32 (.leaf 3416640682) (.leaf 3350536738))) (.branch 35 (.branch 34 (.leaf 3286539484) (.leaf 3224555717)) (.branch 36 (.leaf 3164497035) (.leaf 3106279565)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3049823710) (.leaf 2995053902)) (.branch 40 (.leaf 2941898384) (.leaf 2890288993))) (.branch 43 (.branch 42 (.leaf 2840160966) (.leaf 2791452750)) (.branch 44 (.leaf 2744105832) (.leaf 2698064566))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2653276029) (.branch 47 (.leaf 2609689865) (.leaf 2567258153))) (.branch 50 (.branch 49 (.leaf 2525935280) (.leaf 2485677814)) (.branch 51 (.leaf 2446444390) (.leaf 2408195605)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2370893913) (.leaf 2334503531)) (.branch 55 (.leaf 2298990345) (.leaf 2264321825))) (.branch 58 (.branch 57 (.leaf 2230466945) (.leaf 2197396106)) (.branch 59 (.leaf 2165081062) (.leaf 2133494855))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2102611743) (.branch 62 (.leaf 2072407149) (.leaf 2042857592))) (.branch 65 (.branch 64 (.leaf 2013940641) (.leaf 1985634857)) (.branch 66 (.leaf 1957919748) (.leaf 1930775720)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1904184032) (.leaf 1878126757)) (.branch 70 (.leaf 1852586741) (.leaf 1827547562))) (.branch 73 (.branch 72 (.leaf 1802993503) (.leaf 1778909508)) (.branch 74 (.leaf 1755281156) (.leaf 1732094632))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1709336692) (.branch 77 (.leaf 1686994641) (.leaf 1665056304))) (.branch 80 (.branch 79 (.leaf 1643510003) (.leaf 1622344533)) (.branch 81 (.leaf 1601549142) (.leaf 1581113503)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1561027703) (.leaf 1541282217)) (.branch 85 (.leaf 1521867894) (.leaf 1502775938))) (.branch 88 (.branch 87 (.leaf 1483997893) (.leaf 1465525623)) (.branch 89 (.leaf 1447351304) (.leaf 1429467407)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1411866681) (.branch 92 (.leaf 1394542148) (.leaf 1377487082))) (.branch 95 (.branch 94 (.leaf 1360695005) (.leaf 1344159672)) (.branch 96 (.leaf 1327875063) (.leaf 1311835371)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1296034992) (.leaf 1280468520)) (.branch 100 (.leaf 1265130734) (.leaf 1250016592))) (.branch 103 (.branch 102 (.leaf 1235121225) (.leaf 1220439926)) (.branch 104 (.leaf 1205968144) (.leaf 1191701479))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1177635674) (.leaf 1163766611)) (.branch 108 (.leaf 1150090302) (.leaf 1136602886))) (.branch 111 (.branch 110 (.leaf 1123300624) (.leaf 1110179890)) (.branch 112 (.leaf 1097237172) (.leaf 1084469063)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1071872260) (.leaf 1059443557)) (.branch 116 (.leaf 1047179842) (.leaf 1035078093))) (.branch 119 (.branch 118 (.leaf 1023135376) (.leaf 1011348840)) (.branch 120 (.leaf 999715715) (.leaf 988233305)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 45).prefactor = (2773206945032943/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 45).cutoff/(generalMeanRows 45).c)).2 =
    (95469938913923/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 45).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 45).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 45).q*(generalMeanRows 45).c/2-2 = (43/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable022.value]
    have hcontinuation : (generalMeanRows 45).q*(generalMeanRows 45).cutoff/2-2 = (23/12:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable028.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 45).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 45

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 45).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 45).criticalRate j.val*(generalMeanRows 45).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 45).c*(generalMeanRows 45).criticalPoint j.val)).2-
      (generalMeanRows 45).J/2-(generalMeanRows 45).error (generalMeanGrid j.val)+
      (generalMeanRows 45).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 45).c)).2-
      (generalMeanRows 45).J/2-(generalMeanRows 45).error 4 := by
  have he : (generalMeanRows 45).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 45) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 45)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0045

/-! Kernel-checked entropy margins for general spectral rectangle 46. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0046
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7565767494) (.branch 2 (.leaf 7328599301) (.leaf 7102432973))) (.branch 5 (.branch 4 (.leaf 6886626774) (.leaf 6680584342)) (.branch 6 (.leaf 6483750708) (.leaf 6295608753)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6115676052) (.leaf 5943502031)) (.branch 10 (.leaf 5778665421) (.leaf 5620771968))) (.branch 13 (.branch 12 (.leaf 5469452349) (.leaf 5324360300)) (.branch 14 (.leaf 5185170903) (.leaf 5051579038))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4923297964) (.branch 17 (.leaf 4800058024) (.leaf 4681605460))) (.branch 20 (.branch 19 (.leaf 4567701328) (.leaf 4458120497)) (.branch 21 (.leaf 4352650732) (.leaf 4251091847)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4153254921) (.leaf 4058961580)) (.branch 25 (.leaf 3968043326) (.leaf 3880340919))) (.branch 28 (.branch 27 (.leaf 3795703802) (.leaf 3713989568)) (.branch 29 (.leaf 3635063464) (.leaf 3558797933)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3485072178) (.branch 32 (.leaf 3413771768) (.leaf 3344788262))) (.branch 35 (.branch 34 (.leaf 3278018858) (.leaf 3213366072)) (.branch 36 (.leaf 3150737426) (.leaf 3090045172)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3031206015) (.leaf 2974140871)) (.branch 40 (.leaf 2918774627) (.leaf 2865035921))) (.branch 43 (.branch 42 (.leaf 2812856939) (.leaf 2762173216)) (.branch 44 (.leaf 2712923458) (.leaf 2665049366))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2618495479) (.branch 47 (.leaf 2573209016) (.leaf 2529139741))) (.branch 50 (.branch 49 (.leaf 2486239821) (.leaf 2444463702)) (.branch 51 (.leaf 2403767991) (.leaf 2364111339)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2325454338) (.leaf 2287759420)) (.branch 55 (.leaf 2250990761) (.leaf 2215114189))) (.branch 58 (.branch 57 (.leaf 2180097107) (.leaf 2145908405)) (.branch 59 (.leaf 2112518387) (.leaf 2079898704))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2048022277) (.branch 62 (.leaf 2016863244) (.leaf 1986396890))) (.branch 65 (.branch 64 (.leaf 1956599596) (.leaf 1927448782)) (.branch 66 (.leaf 1898922856) (.leaf 1871001167)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1843663955) (.leaf 1816892313)) (.branch 70 (.leaf 1790668141) (.leaf 1764974108))) (.branch 73 (.branch 72 (.leaf 1739793617) (.leaf 1715110766)) (.branch 74 (.leaf 1690910317) (.leaf 1667177666))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1643898809) (.branch 77 (.leaf 1621060315) (.leaf 1598649299))) (.branch 80 (.branch 79 (.leaf 1576653399) (.leaf 1555060746)) (.branch 81 (.leaf 1533859945) (.leaf 1513040051)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1492590552) (.leaf 1472501342)) (.branch 85 (.leaf 1452762708) (.leaf 1433365310))) (.branch 88 (.branch 87 (.leaf 1414300165) (.leaf 1395558628)) (.branch 89 (.leaf 1377132380) (.leaf 1359013412)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1341194009) (.branch 92 (.leaf 1323666740) (.leaf 1306424445))) (.branch 95 (.branch 94 (.leaf 1289460221) (.leaf 1272767410)) (.branch 96 (.leaf 1256339592) (.leaf 1240170571)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1224254369) (.leaf 1208585211)) (.branch 100 (.leaf 1193157521) (.leaf 1177965911))) (.branch 103 (.branch 102 (.leaf 1163005174) (.leaf 1148270277)) (.branch 104 (.leaf 1133756350) (.leaf 1119458685))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1105372722) (.leaf 1091494050)) (.branch 108 (.leaf 1077818397) (.leaf 1064341622))) (.branch 111 (.branch 110 (.leaf 1051059715) (.leaf 1037968788)) (.branch 112 (.leaf 1025065072) (.leaf 1012344910)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 999804754) (.leaf 987441160)) (.branch 116 (.leaf 975250785) (.leaf 963230381))) (.branch 119 (.branch 118 (.leaf 951376794) (.leaf 939686958)) (.branch 120 (.leaf 928157891) (.leaf 916786696)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 46).prefactor = (1450359956917193/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 46).cutoff/(generalMeanRows 46).c)).2 =
    (2325398009889/5000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 46).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 46).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 46).q*(generalMeanRows 46).c/2-2 = (23/50:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable014.value]
    have hcontinuation : (generalMeanRows 46).q*(generalMeanRows 46).cutoff/2-2 = (23/12:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable028.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 46).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 46

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 46).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 46).criticalRate j.val*(generalMeanRows 46).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 46).c*(generalMeanRows 46).criticalPoint j.val)).2-
      (generalMeanRows 46).J/2-(generalMeanRows 46).error (generalMeanGrid j.val)+
      (generalMeanRows 46).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 46).c)).2-
      (generalMeanRows 46).J/2-(generalMeanRows 46).error 4 := by
  have he : (generalMeanRows 46).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 46) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 46)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0046

/-! Kernel-checked entropy margins for general spectral rectangle 47. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0047
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7750640603) (.branch 2 (.leaf 7502655925) (.leaf 7266175159))) (.branch 5 (.branch 4 (.leaf 7040528329) (.leaf 6825092822)) (.branch 6 (.leaf 6619289240) (.leaf 6422577696)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6234454515) (.leaf 6054449265)) (.branch 10 (.leaf 5882122109) (.leaf 5717061393))) (.branch 13 (.branch 12 (.leaf 5558881493) (.leaf 5407220842)) (.branch 14 (.leaf 5261740152) (.leaf 5122120796))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4988063321) (.branch 17 (.leaf 4859286103) (.leaf 4735524110))) (.branch 20 (.branch 19 (.leaf 4616527761) (.leaf 4502061894)) (.branch 21 (.leaf 4391904796) (.leaf 4285847329)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4183692108) (.leaf 4085252750)) (.branch 25 (.leaf 3990353177) (.leaf 3898826969))) (.branch 28 (.branch 27 (.leaf 3810516766) (.leaf 3725273709)) (.branch 29 (.leaf 3642956928) (.leaf 3563433056)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3486575782) (.branch 32 (.leaf 3412265436) (.leaf 3340388597))) (.branch 35 (.branch 34 (.leaf 3270837728) (.leaf 3203510841)) (.branch 36 (.leaf 3138311172) (.leaf 3075146889)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3013930812) (.leaf 2954580151)) (.branch 40 (.leaf 2897016261) (.leaf 2841164413))) (.branch 43 (.branch 42 (.leaf 2786953579) (.leaf 2734316228)) (.branch 44 (.leaf 2683188136) (.leaf 2633508210))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2585218314) (.branch 47 (.leaf 2538263115) (.leaf 2492589932))) (.branch 50 (.branch 49 (.leaf 2448148596) (.leaf 2404891320)) (.branch 51 (.leaf 2362772567) (.leaf 2321748942)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2281779072) (.leaf 2242823508)) (.branch 55 (.leaf 2204844623) (.leaf 2167806517))) (.branch 58 (.branch 57 (.leaf 2131674933) (.leaf 2096417169)) (.branch 59 (.leaf 2062002003) (.leaf 2028399617))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1995581526) (.branch 62 (.leaf 1963520512) (.leaf 1932190559))) (.branch 65 (.branch 64 (.leaf 1901566798) (.leaf 1871625445)) (.branch 66 (.leaf 1842343750) (.leaf 1813699949)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1785673210) (.leaf 1758243592)) (.branch 70 (.leaf 1731392000) (.leaf 1705100145))) (.branch 73 (.branch 72 (.leaf 1679350506) (.leaf 1654126290)) (.branch 74 (.leaf 1629411401) (.leaf 1605190405))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1581448497) (.branch 77 (.leaf 1558171475) (.leaf 1535345709))) (.branch 80 (.branch 79 (.leaf 1512958115) (.leaf 1490996129)) (.branch 81 (.leaf 1469447684) (.leaf 1448301186)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1427545491) (.leaf 1407169888)) (.branch 85 (.leaf 1387164075) (.leaf 1367518143))) (.branch 88 (.branch 87 (.leaf 1348222556) (.leaf 1329268138)) (.branch 89 (.leaf 1310646052) (.leaf 1292347788)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1274365148) (.branch 92 (.leaf 1256690229) (.leaf 1239315415))) (.branch 95 (.branch 94 (.leaf 1222233361) (.leaf 1205436982)) (.branch 96 (.leaf 1188919442) (.leaf 1172674140)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1156694707) (.leaf 1140974988)) (.branch 100 (.leaf 1125509037) (.leaf 1110291108))) (.branch 103 (.branch 102 (.leaf 1095315646) (.leaf 1080577278)) (.branch 104 (.leaf 1066070808) (.leaf 1051791206))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1037733602) (.leaf 1023893283)) (.branch 108 (.leaf 1010265682) (.leaf 996846375))) (.branch 111 (.branch 110 (.leaf 983631071) (.leaf 970615613)) (.branch 112 (.leaf 957795968) (.leaf 945168223)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 932728580) (.leaf 920473353)) (.branch 116 (.leaf 908398962) (.leaf 896501929))) (.branch 119 (.branch 118 (.leaf 884778875) (.leaf 873226515)) (.branch 120 (.leaf 861841655) (.leaf 850621190)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 47).prefactor = (6068191941885833/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 47).cutoff/(generalMeanRows 47).c)).2 =
    (90591648289091/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 47).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 47).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 47).q*(generalMeanRows 47).c/2-2 = (49/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable003.value]
    have hcontinuation : (generalMeanRows 47).q*(generalMeanRows 47).cutoff/2-2 = (23/12:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable028.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 47).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 47

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 47).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 47).criticalRate j.val*(generalMeanRows 47).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 47).c*(generalMeanRows 47).criticalPoint j.val)).2-
      (generalMeanRows 47).J/2-(generalMeanRows 47).error (generalMeanGrid j.val)+
      (generalMeanRows 47).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 47).c)).2-
      (generalMeanRows 47).J/2-(generalMeanRows 47).error 4 := by
  have he : (generalMeanRows 47).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 47) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 47)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0047

/-! Kernel-checked entropy margins for general spectral rectangle 48. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0048
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6915530823) (.branch 2 (.leaf 6660543284) (.leaf 6417562340))) (.branch 5 (.branch 4 (.leaf 6185894631) (.leaf 5964895728)) (.branch 6 (.leaf 5753965824) (.leaf 5552545909)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5360114346) (.leaf 5176183810)) (.branch 10 (.leaf 5000298533) (.leaf 4832031829))) (.branch 13 (.branch 12 (.leaf 4670983848) (.leaf 4516779554)) (.branch 14 (.leaf 4369066879) (.leaf 4227515053))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4091813074) (.branch 17 (.leaf 3961668314) (.leaf 3836805244))) (.branch 20 (.branch 19 (.leaf 3716964264) (.leaf 3601900629)) (.branch 21 (.leaf 3491383457) (.leaf 3385194826)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3283128926) (.leaf 3184991290)) (.branch 25 (.leaf 3090598072) (.leaf 2999775384))) (.branch 28 (.branch 27 (.leaf 2912358680) (.leaf 2828192183)) (.branch 29 (.leaf 2747128354) (.leaf 2669027397)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2593756799) (.branch 32 (.leaf 2521190902) (.leaf 2451210499))) (.branch 35 (.branch 34 (.leaf 2383702466) (.leaf 2318559406)) (.branch 36 (.leaf 2255679330) (.leaf 2194965344)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2136325369) (.leaf 2079671870)) (.branch 40 (.leaf 2024921606) (.leaf 1971995392))) (.branch 43 (.branch 42 (.leaf 1920817881) (.leaf 1871317352)) (.branch 44 (.leaf 1823425521) (.leaf 1777077349))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1732210877) (.branch 47 (.leaf 1688767057) (.leaf 1646689604))) (.branch 50 (.branch 49 (.leaf 1605924848) (.leaf 1566421601)) (.branch 51 (.leaf 1528131026) (.leaf 1491006517)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1455003589) (.leaf 1420079761)) (.branch 55 (.leaf 1386194465) (.leaf 1353308942))) (.branch 58 (.branch 57 (.leaf 1321386154) (.leaf 1290390701)) (.branch 59 (.leaf 1260288734) (.leaf 1231047884))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1202637184) (.branch 62 (.leaf 1175027007) (.leaf 1148188994))) (.branch 65 (.branch 64 (.leaf 1122095996) (.leaf 1096722017)) (.branch 66 (.leaf 1072042155) (.leaf 1048032552)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1024670346) (.leaf 1001933618)) (.branch 70 (.leaf 979801354) (.leaf 958253400))) (.branch 73 (.branch 72 (.leaf 937270420) (.leaf 916833862)) (.branch 74 (.leaf 896925916) (.leaf 877529486))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 858628153) (.branch 77 (.leaf 840206147) (.leaf 822248314))) (.branch 80 (.branch 79 (.leaf 804740091) (.leaf 787667478)) (.branch 81 (.leaf 771017014) (.leaf 754775751)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 738931234) (.leaf 723471477)) (.branch 85 (.leaf 708384940) (.leaf 693660517))) (.branch 88 (.branch 87 (.leaf 679287509) (.leaf 665255611)) (.branch 89 (.leaf 651554893) (.leaf 638175787)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 625109066) (.branch 92 (.leaf 612345834) (.leaf 599877511))) (.branch 95 (.branch 94 (.leaf 587695818) (.leaf 575792767)) (.branch 96 (.leaf 564160647) (.leaf 552792013)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 541679675) (.leaf 530816687)) (.branch 100 (.leaf 520196339) (.leaf 509812145))) (.branch 103 (.branch 102 (.leaf 499657835) (.leaf 489727346)) (.branch 104 (.leaf 480014815) (.leaf 470514570))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 461221121) (.leaf 452129155)) (.branch 108 (.leaf 443233530) (.leaf 434529265))) (.branch 111 (.branch 110 (.leaf 426011536) (.leaf 417675670)) (.branch 112 (.leaf 409517138) (.leaf 401531551)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 393714653) (.leaf 386062319)) (.branch 116 (.leaf 378570546) (.leaf 371235451))) (.branch 119 (.branch 118 (.leaf 364053269) (.leaf 357020341)) (.branch 120 (.leaf 350133120) (.leaf 343388158)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 48).prefactor = (6347209406180287/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 48).cutoff/(generalMeanRows 48).c)).2 =
    (90234835681301/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 48).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 48).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 48).q*(generalMeanRows 48).c/2-2 = (73/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable024.value]
    have hcontinuation : (generalMeanRows 48).q*(generalMeanRows 48).cutoff/2-2 = (23/12:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable028.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 48).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 48

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 48).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 48).criticalRate j.val*(generalMeanRows 48).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 48).c*(generalMeanRows 48).criticalPoint j.val)).2-
      (generalMeanRows 48).J/2-(generalMeanRows 48).error (generalMeanGrid j.val)+
      (generalMeanRows 48).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 48).c)).2-
      (generalMeanRows 48).J/2-(generalMeanRows 48).error 4 := by
  have he : (generalMeanRows 48).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 48) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 48)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0048

/-! Kernel-checked entropy margins for general spectral rectangle 49. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0049
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6498888530) (.branch 2 (.leaf 6296969963) (.leaf 6104601603))) (.branch 5 (.branch 4 (.leaf 5921208206) (.leaf 5746255930)) (.branch 6 (.leaf 5579248720) (.leaf 5419725093)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5267255251) (.leaf 5121438491)) (.branch 10 (.leaf 4981900873) (.leaf 4848293110))) (.branch 13 (.branch 12 (.leaf 4720288670) (.leaf 4597582036)) (.branch 14 (.leaf 4479887144) (.leaf 4366935942))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4258477088) (.branch 17 (.leaf 4154274752) (.leaf 4054107519))) (.branch 20 (.branch 19 (.leaf 3957767388) (.leaf 3865058847)) (.branch 21 (.leaf 3775798020) (.leaf 3689811891)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3606937573) (.leaf 3527021647)) (.branch 25 (.leaf 3449919541) (.leaf 3375494962))) (.branch 28 (.branch 27 (.leaf 3303619361) (.leaf 3234171447)) (.branch 29 (.leaf 3167036728) (.leaf 3102107086)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3039280382) (.branch 32 (.leaf 2978460094) (.leaf 2919554967))) (.branch 35 (.branch 34 (.leaf 2862478698) (.leaf 2807149640)) (.branch 36 (.leaf 2753490519) (.leaf 2701428178)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2650893333) (.leaf 2601820348)) (.branch 40 (.leaf 2554147018) (.leaf 2507814373))) (.branch 43 (.branch 42 (.leaf 2462766492) (.leaf 2418950328)) (.branch 44 (.leaf 2376315541) (.leaf 2334814350))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2294401384) (.branch 47 (.leaf 2255033548) (.leaf 2216669897))) (.branch 50 (.branch 49 (.leaf 2179271515) (.leaf 2142801403)) (.branch 51 (.leaf 2107224374) (.leaf 2072506952)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2038617281) (.leaf 2005525035)) (.branch 55 (.leaf 1973201336) (.leaf 1941618674))) (.branch 58 (.branch 57 (.leaf 1910750838) (.leaf 1880572843)) (.branch 59 (.leaf 1851060864) (.leaf 1822192178))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1793945104) (.branch 62 (.leaf 1766298948) (.leaf 1739233951))) (.branch 65 (.branch 64 (.leaf 1712731241) (.leaf 1686772787)) (.branch 66 (.leaf 1661341356) (.leaf 1636420472)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1611994374) (.leaf 1588047985)) (.branch 70 (.leaf 1564566872) (.leaf 1541537216))) (.branch 73 (.branch 72 (.leaf 1518945783) (.leaf 1496779890)) (.branch 74 (.leaf 1475027382) (.leaf 1453676602))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1432716368) (.branch 77 (.leaf 1412135951) (.leaf 1391925050))) (.branch 80 (.branch 79 (.leaf 1372073775) (.leaf 1352572621)) (.branch 81 (.leaf 1333412456) (.leaf 1314584499)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1296080304) (.leaf 1277891743)) (.branch 85 (.leaf 1260010996) (.leaf 1242430528))) (.branch 88 (.branch 87 (.leaf 1225143083) (.leaf 1208141668)) (.branch 89 (.leaf 1191419541) (.leaf 1174970200)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1158787369) (.branch 92 (.leaf 1142864993) (.leaf 1127197225))) (.branch 95 (.branch 94 (.leaf 1111778414) (.leaf 1096603102)) (.branch 96 (.leaf 1081666011) (.leaf 1066962036)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1052486241) (.leaf 1038233843)) (.branch 100 (.leaf 1024200215) (.leaf 1010380874))) (.branch 103 (.branch 102 (.leaf 996771476) (.leaf 983367810)) (.branch 104 (.leaf 970165791) (.leaf 957161458))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 944350967) (.leaf 931730585)) (.branch 108 (.leaf 919296686) (.leaf 907045750))) (.branch 111 (.branch 110 (.leaf 894974354) (.leaf 883079169)) (.branch 112 (.leaf 871356961) (.leaf 859804581)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 848418964) (.leaf 837197127)) (.branch 116 (.leaf 826136166) (.leaf 815233251))) (.branch 119 (.branch 118 (.leaf 804485623) (.leaf 793890595)) (.branch 120 (.leaf 783445544) (.leaf 773147915)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 49).prefactor = (5347170257036201/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 49).cutoff/(generalMeanRows 49).c)).2 =
    (494470735349727/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 49).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 49).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 49).q*(generalMeanRows 49).c/2-2 = (201/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable029.value]
    have hcontinuation : (generalMeanRows 49).q*(generalMeanRows 49).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable030.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 49).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 49

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 49).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 49).criticalRate j.val*(generalMeanRows 49).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 49).c*(generalMeanRows 49).criticalPoint j.val)).2-
      (generalMeanRows 49).J/2-(generalMeanRows 49).error (generalMeanGrid j.val)+
      (generalMeanRows 49).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 49).c)).2-
      (generalMeanRows 49).J/2-(generalMeanRows 49).error 4 := by
  have he : (generalMeanRows 49).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 49) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 49)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0049

/-! Kernel-checked entropy margins for general spectral rectangle 50. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0050
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6594304763) (.branch 2 (.leaf 6385191816) (.leaf 6185973917))) (.branch 5 (.branch 4 (.leaf 5996056135) (.leaf 5814886340)) (.branch 6 (.leaf 5641951474) (.leaf 5476774218)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5318910009) (.leaf 5167944361)) (.branch 10 (.leaf 5023490454) (.leaf 4885186952))) (.branch 13 (.branch 12 (.leaf 4752696039) (.leaf 4625701624)) (.branch 14 (.leaf 4503907720) (.leaf 4387036959))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4274829244) (.branch 17 (.leaf 4167040510) (.leaf 4063441594))) (.branch 20 (.branch 19 (.leaf 3963817194) (.leaf 3867964917)) (.branch 21 (.leaf 3775694398) (.leaf 3686826493)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3601192532) (.leaf 3518633626)) (.branch 25 (.leaf 3439000033) (.leaf 3362150568))) (.branch 28 (.branch 27 (.leaf 3287952051) (.leaf 3216278801)) (.branch 29 (.leaf 3147012169) (.leaf 3080040091)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3015256689) (.branch 32 (.leaf 2952561885) (.leaf 2891861052))) (.branch 35 (.branch 34 (.leaf 2833064681) (.leaf 2776088073)) (.branch 36 (.leaf 2720851058) (.leaf 2667277717)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2615296139) (.leaf 2564838183)) (.branch 40 (.leaf 2515839259) (.leaf 2468238124))) (.branch 43 (.branch 42 (.leaf 2421976687) (.leaf 2376999827)) (.branch 44 (.leaf 2333255231) (.leaf 2290693228))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2249266641) (.branch 47 (.leaf 2208930652) (.leaf 2169642665))) (.branch 50 (.branch 49 (.leaf 2131362186) (.leaf 2094050704)) (.branch 51 (.leaf 2057671585) (.leaf 2022189967)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1987572665) (.leaf 1953788080)) (.branch 55 (.leaf 1920806111) (.leaf 1888598076))) (.branch 58 (.branch 57 (.leaf 1857136639) (.leaf 1826395734)) (.branch 59 (.leaf 1796350498) (.leaf 1766977210))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1738253230) (.branch 62 (.leaf 1710156940) (.leaf 1682667695))) (.branch 65 (.branch 64 (.leaf 1655765769) (.leaf 1629432308)) (.branch 66 (.leaf 1603649286) (.leaf 1578399465)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1553666348) (.leaf 1529434148)) (.branch 70 (.leaf 1505687749) (.leaf 1482412673))) (.branch 73 (.branch 72 (.leaf 1459595047) (.leaf 1437221574)) (.branch 74 (.leaf 1415279506) (.leaf 1393756611))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1372641154) (.branch 77 (.leaf 1351921870) (.leaf 1331587940))) (.branch 80 (.branch 79 (.leaf 1311628973) (.leaf 1292034979)) (.branch 81 (.leaf 1272796357) (.leaf 1253903873)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1235348639) (.leaf 1217122105)) (.branch 85 (.leaf 1199216034) (.leaf 1181622496))) (.branch 88 (.branch 87 (.leaf 1164333845) (.leaf 1147342713)) (.branch 89 (.leaf 1130641995) (.leaf 1114224833)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1098084611) (.branch 92 (.leaf 1082214942) (.leaf 1066609653))) (.branch 95 (.branch 94 (.leaf 1051262784) (.leaf 1036168571)) (.branch 96 (.leaf 1021321440) (.leaf 1006716001)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 992347037) (.leaf 978209497)) (.branch 100 (.leaf 964298490) (.leaf 950609276))) (.branch 103 (.branch 102 (.leaf 937137264) (.leaf 923878000)) (.branch 104 (.leaf 910827165) (.leaf 897980570))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 885334147) (.leaf 872883948)) (.branch 108 (.leaf 860626137) (.leaf 848556987))) (.branch 111 (.branch 110 (.leaf 836672878) (.leaf 824970288)) (.branch 112 (.leaf 813445791) (.leaf 802096056)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 790917840) (.leaf 779907985)) (.branch 116 (.leaf 769063418) (.leaf 758381142))) (.branch 119 (.branch 118 (.leaf 747858239) (.leaf 737491865)) (.branch 120 (.leaf 727279244) (.leaf 717217673)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 50).prefactor = (5539061945954633/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 50).cutoff/(generalMeanRows 50).c)).2 =
    (483541664817537/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 50).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 50).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 50).q*(generalMeanRows 50).c/2-2 = (53/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable031.value]
    have hcontinuation : (generalMeanRows 50).q*(generalMeanRows 50).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable030.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 50).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 50

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 50).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 50).criticalRate j.val*(generalMeanRows 50).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 50).c*(generalMeanRows 50).criticalPoint j.val)).2-
      (generalMeanRows 50).J/2-(generalMeanRows 50).error (generalMeanGrid j.val)+
      (generalMeanRows 50).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 50).c)).2-
      (generalMeanRows 50).J/2-(generalMeanRows 50).error 4 := by
  have he : (generalMeanRows 50).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 50) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 50)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0050

/-! Kernel-checked entropy margins for general spectral rectangle 51. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0051
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6692246725) (.branch 2 (.leaf 6475774217) (.leaf 6269554244))) (.branch 5 (.branch 4 (.leaf 6072971439) (.leaf 5885454690)) (.branch 6 (.leaf 5706473286) (.leaf 5535533464)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5372175328) (.leaf 5215970075)) (.branch 10 (.leaf 5066517506) (.leaf 4923443768))) (.branch 13 (.branch 12 (.leaf 4786399320) (.leaf 4655057081)) (.branch 14 (.leaf 4529110751) (.leaf 4408273278))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4292275462) (.branch 17 (.leaf 4180864677) (.leaf 4073803699))) (.branch 20 (.branch 19 (.leaf 3970869635) (.leaf 3871852933)) (.branch 21 (.leaf 3776556476) (.leaf 3684794746)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3596393050) (.leaf 3511186811)) (.branch 25 (.leaf 3429020903) (.leaf 3349749047))) (.branch 28 (.branch 27 (.leaf 3273233241) (.leaf 3199343235)) (.branch 29 (.leaf 3127956047) (.leaf 3058955508)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2992231840) (.branch 32 (.leaf 2927681265) (.leaf 2865205639))) (.branch 35 (.branch 34 (.leaf 2804712114) (.leaf 2746112814)) (.branch 36 (.leaf 2689324546) (.leaf 2634268515)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2580870073) (.leaf 2529058468)) (.branch 40 (.leaf 2478766625) (.leaf 2429930930))) (.branch 43 (.branch 42 (.leaf 2382491028) (.leaf 2336389645)) (.branch 44 (.leaf 2291572403) (.leaf 2247987664))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2205586373) (.branch 47 (.leaf 2164321911) (.leaf 2124149965))) (.branch 50 (.branch 49 (.leaf 2085028395) (.leaf 2046917116)) (.branch 51 (.leaf 2009777987) (.leaf 1973574703)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1938272694) (.leaf 1903839035)) (.branch 55 (.leaf 1870242353) (.leaf 1837452748))) (.branch 58 (.branch 57 (.leaf 1805441710) (.leaf 1774182051)) (.branch 59 (.leaf 1743647827) (.leaf 1713814281))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1684657774) (.branch 62 (.leaf 1656155732) (.leaf 1628286587))) (.branch 65 (.branch 64 (.leaf 1601029725) (.leaf 1574365440)) (.branch 66 (.leaf 1548274884) (.leaf 1522740027)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1497743609) (.leaf 1473269110)) (.branch 70 (.leaf 1449300705) (.leaf 1425823232))) (.branch 73 (.branch 72 (.leaf 1402822161) (.leaf 1380283559)) (.branch 74 (.leaf 1358194062) (.leaf 1336540848))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1315311610) (.branch 77 (.leaf 1294494530) (.leaf 1274078256))) (.branch 80 (.branch 79 (.leaf 1254051878) (.leaf 1234404912)) (.branch 81 (.leaf 1215127271) (.leaf 1196209255)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1177641526) (.leaf 1159415095)) (.branch 85 (.leaf 1141521305) (.leaf 1123951814))) (.branch 88 (.branch 87 (.leaf 1106698581) (.leaf 1089753854)) (.branch 89 (.leaf 1073110155) (.leaf 1056760267)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1040697224) (.branch 92 (.leaf 1024914300) (.leaf 1009404994))) (.branch 95 (.branch 94 (.leaf 994163028) (.leaf 979182328)) (.branch 96 (.leaf 964457022) (.leaf 949981428)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 935750047) (.leaf 921757555)) (.branch 100 (.leaf 907998794) (.leaf 894468768))) (.branch 103 (.branch 102 (.leaf 881162634) (.leaf 868075695)) (.branch 104 (.leaf 855203396) (.leaf 842541318))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 830085170) (.leaf 817830788)) (.branch 108 (.leaf 805774126) (.leaf 793911252))) (.branch 111 (.branch 110 (.leaf 782238346) (.leaf 770751694)) (.branch 112 (.leaf 759447682) (.leaf 748322797)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 737373617) (.leaf 726596814)) (.branch 116 (.leaf 715989144) (.leaf 705547449))) (.branch 119 (.branch 118 (.leaf 695268652) (.leaf 685149754)) (.branch 120 (.leaf 675187832) (.leaf 665380032)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 51).prefactor = (5737839972600481/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 51).cutoff/(generalMeanRows 51).c)).2 =
    (472730748713323/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 51).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 51).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 51).q*(generalMeanRows 51).c/2-2 = (223/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable017.value]
    have hcontinuation : (generalMeanRows 51).q*(generalMeanRows 51).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable030.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 51).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 51

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 51).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 51).criticalRate j.val*(generalMeanRows 51).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 51).c*(generalMeanRows 51).criticalPoint j.val)).2-
      (generalMeanRows 51).J/2-(generalMeanRows 51).error (generalMeanGrid j.val)+
      (generalMeanRows 51).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 51).c)).2-
      (generalMeanRows 51).J/2-(generalMeanRows 51).error 4 := by
  have he : (generalMeanRows 51).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 51) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 51)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0051

/-! Kernel-checked entropy margins for general spectral rectangle 52. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0052
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5918914385) (.branch 2 (.leaf 5698677959) (.leaf 5489074954))) (.branch 5 (.branch 4 (.leaf 5289473054) (.leaf 5099285246)) (.branch 6 (.leaf 4917965856) (.leaf 4745007020)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4579935522) (.leaf 4422309959)) (.branch 10 (.leaf 4271718182) (.leaf 4127774993))) (.branch 13 (.branch 12 (.leaf 3990120059) (.leaf 3858416019)) (.branch 14 (.leaf 3732346767) (.leaf 3611615885))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3495945214) (.branch 17 (.leaf 3385073548) (.leaf 3278755440))) (.branch 20 (.branch 19 (.leaf 3176760105) (.leaf 3078870409)) (.branch 21 (.leaf 2984881948) (.leaf 2894602189)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2807849686) (.leaf 2724453351)) (.branch 25 (.leaf 2644251781) (.leaf 2567092639))) (.branch 28 (.branch 27 (.leaf 2492832072) (.leaf 2421334180)) (.branch 29 (.leaf 2352470517) (.leaf 2286119631)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2222166633) (.branch 32 (.leaf 2160502799) (.leaf 2101025196))) (.branch 35 (.branch 34 (.leaf 2043636335) (.leaf 1988243849)) (.branch 36 (.leaf 1934760188) (.leaf 1883102337)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1833191555) (.leaf 1784953123)) (.branch 40 (.leaf 1738316117) (.leaf 1693213187))) (.branch 43 (.branch 42 (.leaf 1649580360) (.leaf 1607356845)) (.branch 44 (.leaf 1566484857) (.leaf 1526909447))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1488578348) (.branch 47 (.leaf 1451441828) (.leaf 1415452546))) (.branch 50 (.branch 49 (.leaf 1380565427) (.leaf 1346737539)) (.branch 51 (.leaf 1313927973) (.leaf 1282097741)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1251209669) (.leaf 1221228303)) (.branch 55 (.leaf 1192119818) (.leaf 1163851933))) (.branch 58 (.branch 57 (.leaf 1136393829) (.leaf 1109716076)) (.branch 59 (.leaf 1083790558) (.leaf 1058590407))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1034089942) (.branch 62 (.leaf 1010264603) (.leaf 987090899))) (.branch 65 (.branch 64 (.leaf 964546354) (.leaf 942609452)) (.branch 66 (.leaf 921259595) (.leaf 900477053)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 880242924) (.leaf 860539092)) (.branch 70 (.leaf 841348190) (.leaf 822653562))) (.branch 73 (.branch 72 (.leaf 804439230) (.leaf 786689862)) (.branch 74 (.leaf 769390738) (.leaf 752527726))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 736087249) (.branch 77 (.leaf 720056265) (.leaf 704422235))) (.branch 80 (.branch 79 (.leaf 689173106) (.leaf 674297283)) (.branch 81 (.leaf 659783613) (.leaf 645621364)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 631800200) (.leaf 618310173)) (.branch 85 (.leaf 605141696) (.leaf 592285536))) (.branch 88 (.branch 87 (.leaf 579732788) (.leaf 567474872)) (.branch 89 (.leaf 555503508) (.leaf 543810713)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 532388778) (.branch 92 (.leaf 521230266) (.leaf 510327994))) (.branch 95 (.branch 94 (.leaf 499675023) (.leaf 489264650)) (.branch 96 (.leaf 479090398) (.leaf 469146005)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 459425414) (.leaf 449922769)) (.branch 100 (.leaf 440632403) (.leaf 431548832))) (.branch 103 (.branch 102 (.leaf 422666747) (.leaf 413981007)) (.branch 104 (.leaf 405486633) (.leaf 397178802))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 389052839) (.leaf 381104215)) (.branch 108 (.leaf 373328535) (.leaf 365721540))) (.branch 111 (.branch 110 (.leaf 358279099) (.leaf 350997200)) (.branch 112 (.leaf 343871955) (.leaf 336899586)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 330076425) (.leaf 323398912)) (.branch 116 (.leaf 316863587) (.leaf 310467091))) (.branch 119 (.branch 118 (.leaf 304206155) (.leaf 298077608)) (.branch 120 (.leaf 292078361) (.leaf 286205415)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 52).prefactor = (5943751464129509/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 52).cutoff/(generalMeanRows 52).c)).2 =
    (97552431256329/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 52).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 52).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 52).q*(generalMeanRows 52).c/2-2 = (311/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable032.value]
    have hcontinuation : (generalMeanRows 52).q*(generalMeanRows 52).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable030.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 52).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 52

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 52).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 52).criticalRate j.val*(generalMeanRows 52).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 52).c*(generalMeanRows 52).criticalPoint j.val)).2-
      (generalMeanRows 52).J/2-(generalMeanRows 52).error (generalMeanGrid j.val)+
      (generalMeanRows 52).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 52).c)).2-
      (generalMeanRows 52).J/2-(generalMeanRows 52).error 4 := by
  have he : (generalMeanRows 52).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 52) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 52)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0052

/-! Kernel-checked entropy margins for general spectral rectangle 53. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0053
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5199097063) (.branch 2 (.leaf 4979900200) (.leaf 4771682057))) (.branch 5 (.branch 4 (.leaf 4573789780) (.leaf 4385617087)) (.branch 6 (.leaf 4206600200) (.leaf 4036214219)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3873969870) (.leaf 3719410595)) (.branch 10 (.leaf 3572109928) (.leaf 3431669125))) (.branch 13 (.branch 12 (.leaf 3297715023) (.leaf 3169898100)) (.branch 14 (.leaf 3047890711) (.leaf 2931385478))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2820093826) (.branch 17 (.leaf 2713744642) (.leaf 2612083052))) (.branch 20 (.branch 19 (.leaf 2514869289) (.leaf 2421877667)) (.branch 21 (.leaf 2332895624) (.leaf 2247722850)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2166170478) (.leaf 2088060337)) (.branch 25 (.leaf 2013224263) (.leaf 1941503461))) (.branch 28 (.branch 27 (.leaf 1872747912) (.leaf 1806815823)) (.branch 29 (.leaf 1743573119) (.leaf 1682892969)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1624655344) (.branch 32 (.leaf 1568746606) (.leaf 1515059127))) (.branch 35 (.branch 34 (.leaf 1463490933) (.leaf 1413945367)) (.branch 36 (.leaf 1366330785) (.leaf 1320560257)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1276551304) (.leaf 1234225634)) (.branch 40 (.leaf 1193508915) (.leaf 1154330543))) (.branch 43 (.branch 42 (.leaf 1116623437) (.leaf 1080323843)) (.branch 44 (.leaf 1045371148) (.leaf 1011707710))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 979278692) (.branch 47 (.leaf 948031915) (.leaf 917917710))) (.branch 50 (.branch 49 (.leaf 888888785) (.leaf 860900097)) (.branch 51 (.leaf 833908735) (.leaf 807873806)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 782756329) (.leaf 758519136)) (.branch 55 (.leaf 735126776) (.leaf 712545430))) (.branch 58 (.branch 57 (.leaf 690742823) (.leaf 669688148)) (.branch 59 (.leaf 649351991) (.leaf 629706259))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 610724115) (.branch 62 (.leaf 592379916) (.leaf 574649151))) (.branch 65 (.branch 64 (.leaf 557508386) (.leaf 540935212)) (.branch 66 (.leaf 524908195) (.leaf 509406825)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 494411475) (.leaf 479903357)) (.branch 70 (.leaf 465864480) (.leaf 452277616))) (.branch 73 (.branch 72 (.leaf 439126258) (.leaf 426394591)) (.branch 74 (.leaf 414067458) (.leaf 402130326))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 390569262) (.branch 77 (.leaf 379370900) (.leaf 368522419))) (.branch 80 (.branch 79 (.leaf 358011516) (.leaf 347826382)) (.branch 81 (.leaf 337955681) (.leaf 328388527)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 319114464) (.leaf 310123449)) (.branch 85 (.leaf 301405830) (.leaf 292952331))) (.branch 88 (.branch 87 (.leaf 284754034) (.leaf 276802364)) (.branch 89 (.leaf 269089077) (.leaf 261606238)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 254346215) (.branch 92 (.leaf 247301664) (.leaf 240465514))) (.branch 95 (.branch 94 (.leaf 233830958) (.leaf 227391441)) (.branch 96 (.leaf 221140649) (.leaf 215072501)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 209181136) (.leaf 203460906)) (.branch 100 (.leaf 197906366) (.leaf 192512269))) (.branch 103 (.branch 102 (.leaf 187273551) (.leaf 182185332)) (.branch 104 (.leaf 177242902) (.leaf 172441717))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 167777391) (.leaf 163245693)) (.branch 108 (.leaf 158842537) (.leaf 154563977))) (.branch 111 (.branch 110 (.leaf 150406204) (.leaf 146365538)) (.branch 112 (.leaf 142438423) (.leaf 138621425)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 134911225) (.leaf 131304614)) (.branch 116 (.leaf 127798491) (.leaf 124389857))) (.branch 119 (.branch 118 (.leaf 121075812) (.leaf 117853553)) (.branch 120 (.leaf 114720367) (.leaf 111673629)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 53).prefactor = (6157052416247571/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 53).cutoff/(generalMeanRows 53).c)).2 =
    (304849876074161/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 53).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 53).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 53).q*(generalMeanRows 53).c/2-2 = (41/40:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable033.value]
    have hcontinuation : (generalMeanRows 53).q*(generalMeanRows 53).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable030.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 53).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 53

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 53).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 53).criticalRate j.val*(generalMeanRows 53).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 53).c*(generalMeanRows 53).criticalPoint j.val)).2-
      (generalMeanRows 53).J/2-(generalMeanRows 53).error (generalMeanGrid j.val)+
      (generalMeanRows 53).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 53).c)).2-
      (generalMeanRows 53).J/2-(generalMeanRows 53).error 4 := by
  have he : (generalMeanRows 53).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 53) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 53)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0053

/-! Kernel-checked entropy margins for general spectral rectangle 54. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0054
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5518609194) (.branch 2 (.leaf 5345605764) (.leaf 5180912384))) (.branch 5 (.branch 4 (.leaf 5024009723) (.leaf 4874416952)) (.branch 6 (.leaf 4731688374) (.leaf 4595410405)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4465198867) (.leaf 4340696552)) (.branch 10 (.leaf 4221571030) (.leaf 4107512661))) (.branch 13 (.branch 12 (.leaf 3998232802) (.leaf 3893462169)) (.branch 14 (.leaf 3792949359) (.leaf 3696459498))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3603773001) (.branch 17 (.leaf 3514684450) (.leaf 3429001562))) (.branch 20 (.branch 19 (.leaf 3346544235) (.leaf 3267143688)) (.branch 21 (.leaf 3190641653) (.leaf 3116889647)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3045748291) (.leaf 2977086684)) (.branch 25 (.leaf 2910781828) (.leaf 2846718094))) (.branch 28 (.branch 27 (.leaf 2784786728) (.leaf 2724885397)) (.branch 29 (.leaf 2666917761) (.leaf 2610793084)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2556425872) (.branch 32 (.leaf 2503735527) (.leaf 2452646043))) (.branch 35 (.branch 34 (.leaf 2403085704) (.leaf 2354986820)) (.branch 36 (.leaf 2308285469) (.leaf 2262921263)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2218837128) (.leaf 2175979101)) (.branch 40 (.leaf 2134296135) (.leaf 2093739924))) (.branch 43 (.branch 42 (.leaf 2054264736) (.leaf 2015827255)) (.branch 44 (.leaf 1978386439) (.leaf 1941903381))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1906341184) (.branch 47 (.leaf 1871664842) (.leaf 1837841128))) (.branch 50 (.branch 49 (.leaf 1804838488) (.leaf 1772626948)) (.branch 51 (.leaf 1741178017) (.leaf 1710464607)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1680460946) (.leaf 1651142509)) (.branch 55 (.leaf 1622485944) (.leaf 1594469007))) (.branch 58 (.branch 57 (.leaf 1567070497) (.leaf 1540270202)) (.branch 59 (.leaf 1514048839) (.leaf 1488388009))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1463270140) (.branch 62 (.leaf 1438678449) (.leaf 1414596898))) (.branch 65 (.branch 64 (.leaf 1391010147) (.leaf 1367903527)) (.branch 66 (.leaf 1345262994) (.leaf 1323075103)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1301326973) (.leaf 1280006258)) (.branch 70 (.leaf 1259101118) (.leaf 1238600194))) (.branch 73 (.branch 72 (.leaf 1218492583) (.leaf 1198767816)) (.branch 74 (.leaf 1179415833) (.leaf 1160426963))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1141791905) (.branch 77 (.leaf 1123501713) (.leaf 1105547770))) (.branch 80 (.branch 79 (.leaf 1087921781) (.leaf 1070615751)) (.branch 81 (.leaf 1053621973) (.leaf 1036933015)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1020541704) (.leaf 1004441116)) (.branch 85 (.leaf 988624563) (.leaf 973085583))) (.branch 88 (.branch 87 (.leaf 957817931) (.leaf 942815565)) (.branch 89 (.leaf 928072640) (.leaf 913583497)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 899342658) (.branch 92 (.leaf 885344814) (.leaf 871584821))) (.branch 95 (.branch 94 (.leaf 858057690) (.leaf 844758583)) (.branch 96 (.leaf 831682804) (.leaf 818825794)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 806183128) (.leaf 793750505)) (.branch 100 (.leaf 781523744) (.leaf 769498783))) (.branch 103 (.branch 102 (.leaf 757671669) (.leaf 746038557)) (.branch 104 (.leaf 734595705) (.leaf 723339470))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 712266302) (.leaf 701372745)) (.branch 108 (.leaf 690655431) (.leaf 680111074))) (.branch 111 (.branch 110 (.leaf 669736473) (.leaf 659528504)) (.branch 112 (.leaf 649484119) (.leaf 639600343)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 629874274) (.leaf 620303075)) (.branch 116 (.leaf 610883977) (.leaf 601614274))) (.branch 119 (.branch 118 (.leaf 592491322) (.leaf 583512536)) (.branch 120 (.leaf 574675390) (.leaf 565977412)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 54).prefactor = (2512336626194057/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 54).cutoff/(generalMeanRows 54).c)).2 =
    (51990930898841/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 54).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 54).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 54).q*(generalMeanRows 54).c/2-2 = (47/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable034.value]
    have hcontinuation : (generalMeanRows 54).q*(generalMeanRows 54).cutoff/2-2 = (127/54:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable035.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 54).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 54

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 54).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 54).criticalRate j.val*(generalMeanRows 54).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 54).c*(generalMeanRows 54).criticalPoint j.val)).2-
      (generalMeanRows 54).J/2-(generalMeanRows 54).error (generalMeanGrid j.val)+
      (generalMeanRows 54).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 54).c)).2-
      (generalMeanRows 54).J/2-(generalMeanRows 54).error 4 := by
  have he : (generalMeanRows 54).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 54) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 54)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0054

/-! Kernel-checked entropy margins for general spectral rectangle 55. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0055
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5557769931) (.branch 2 (.leaf 5380101208) (.leaf 5210980313))) (.branch 5 (.branch 4 (.leaf 5049874088) (.leaf 4896288875)) (.branch 6 (.leaf 4749767056) (.leaf 4609883960)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4476245083) (.leaf 4348483588)) (.branch 10 (.leaf 4226258057) (.leaf 4109250453))) (.branch 13 (.branch 12 (.leaf 3997164275) (.leaf 3889722887)) (.branch 14 (.leaf 3786667993) (.leaf 3687758253))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3592768015) (.branch 17 (.leaf 3501486161) (.leaf 3413715044))) (.branch 20 (.branch 19 (.leaf 3329269520) (.leaf 3247976054)) (.branch 21 (.leaf 3169671903) (.leaf 3094204360)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3021430062) (.leaf 2951214343)) (.branch 25 (.leaf 2883430649) (.leaf 2817959987))) (.branch 28 (.branch 27 (.leaf 2754690421) (.leaf 2693516603)) (.branch 29 (.leaf 2634339339) (.leaf 2577065186)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2521606079) (.branch 32 (.leaf 2467878988) (.leaf 2415805587))) (.branch 35 (.branch 34 (.leaf 2365311963) (.leaf 2316328334)) (.branch 36 (.leaf 2268788789) (.leaf 2222631047)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2177796229) (.leaf 2134228654)) (.branch 40 (.leaf 2091875637) (.leaf 2050687309))) (.branch 43 (.branch 42 (.leaf 2010616447) (.leaf 1971618312)) (.branch 44 (.leaf 1933650500) (.leaf 1896672807))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1860647090) (.branch 47 (.leaf 1825537156) (.leaf 1791308638))) (.branch 50 (.branch 49 (.leaf 1757928895) (.leaf 1725366906)) (.branch 51 (.leaf 1693593182) (.leaf 1662579673)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1632299691) (.leaf 1602727825)) (.branch 55 (.leaf 1573839876) (.leaf 1545612786))) (.branch 58 (.branch 57 (.leaf 1518024573) (.leaf 1491054271)) (.branch 59 (.leaf 1464681877) (.leaf 1438888294))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1413655283) (.branch 62 (.leaf 1388965417) (.leaf 1364802036))) (.branch 65 (.branch 64 (.leaf 1341149206) (.leaf 1317991679)) (.branch 66 (.leaf 1295314859) (.leaf 1273104766)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1251348002) (.leaf 1230031723)) (.branch 70 (.leaf 1209143610) (.leaf 1188671840))) (.branch 73 (.branch 72 (.leaf 1168605064) (.leaf 1148932379)) (.branch 74 (.leaf 1129643307) (.leaf 1110727774))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1092176090) (.branch 77 (.leaf 1073978930) (.leaf 1056127314))) (.branch 80 (.branch 79 (.leaf 1038612593) (.leaf 1021426432)) (.branch 81 (.leaf 1004560794) (.leaf 988007926)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 971760347) (.leaf 955810833)) (.branch 85 (.leaf 940152406) (.leaf 924778325))) (.branch 88 (.branch 87 (.leaf 909682071) (.leaf 894857338)) (.branch 89 (.leaf 880298028) (.leaf 865998233)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 851952236) (.branch 92 (.leaf 838154496) (.leaf 824599643))) (.branch 95 (.branch 94 (.leaf 811282470) (.leaf 798197927)) (.branch 96 (.leaf 785341113) (.leaf 772707272)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 760291782) (.leaf 748090157)) (.branch 100 (.leaf 736098036) (.leaf 724311178))) (.branch 103 (.branch 102 (.leaf 712725462) (.leaf 701336875)) (.branch 104 (.leaf 690141515) (.leaf 679135583))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 668315379) (.leaf 657677299)) (.branch 108 (.leaf 647217833) (.leaf 636933557))) (.branch 111 (.branch 110 (.leaf 626821137) (.leaf 616877317)) (.branch 112 (.leaf 607098924) (.leaf 597482862)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 588026109) (.leaf 578725713)) (.branch 116 (.leaf 569578793) (.leaf 560582537))) (.branch 119 (.branch 118 (.leaf 551734193) (.leaf 543031077)) (.branch 120 (.leaf 534470563) (.leaf 526050083)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 55).prefactor = (2582030757746247/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 55).cutoff/(generalMeanRows 55).c)).2 =
    (63786731286121/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 55).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 55).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 55).q*(generalMeanRows 55).c/2-2 = (49/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable011.value]
    have hcontinuation : (generalMeanRows 55).q*(generalMeanRows 55).cutoff/2-2 = (127/54:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable035.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 55).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 55

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 55).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 55).criticalRate j.val*(generalMeanRows 55).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 55).c*(generalMeanRows 55).criticalPoint j.val)).2-
      (generalMeanRows 55).J/2-(generalMeanRows 55).error (generalMeanGrid j.val)+
      (generalMeanRows 55).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 55).c)).2-
      (generalMeanRows 55).J/2-(generalMeanRows 55).error 4 := by
  have he : (generalMeanRows 55).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 55) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 55)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0055

/-! Kernel-checked entropy margins for general spectral rectangle 56. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0056
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5597911110) (.branch 2 (.leaf 5415517033) (.leaf 5241915172))) (.branch 5 (.branch 4 (.leaf 5076558116) (.leaf 4918938984)) (.branch 6 (.leaf 4768587873) (.leaf 4625068680)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4487976251) (.leaf 4356933823)) (.branch 10 (.leaf 4231590707) (.leaf 4111620202))) (.branch 13 (.branch 12 (.leaf 3996717705) (.leaf 3886598990)) (.branch 14 (.leaf 3780998650) (.leaf 3679668674))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3582377147) (.branch 17 (.leaf 3488907065) (.leaf 3399055246))) (.branch 20 (.branch 19 (.leaf 3312631337) (.leaf 3229456900)) (.branch 21 (.leaf 3149364567) (.leaf 3072197272)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2997807533) (.leaf 2926056800)) (.branch 25 (.leaf 2856814843) (.leaf 2789959197))) (.branch 28 (.branch 27 (.leaf 2725374637) (.leaf 2662952702)) (.branch 29 (.leaf 2602591248) (.leaf 2544194036)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2487670351) (.branch 32 (.leaf 2432934641) (.leaf 2379906193))) (.branch 35 (.branch 34 (.leaf 2328508822) (.leaf 2278670584)) (.branch 36 (.leaf 2230323516) (.leaf 2183403379)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2137849435) (.leaf 2093604228)) (.branch 40 (.leaf 2050613383) (.leaf 2008825419))) (.branch 43 (.branch 42 (.leaf 1968191572) (.leaf 1928665636)) (.branch 44 (.leaf 1890203805) (.leaf 1852764534))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1816308400) (.branch 47 (.leaf 1780797983) (.leaf 1746197746))) (.branch 50 (.branch 49 (.leaf 1712473924) (.leaf 1679594422)) (.branch 51 (.leaf 1647528722) (.leaf 1616247789)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1585723985) (.leaf 1555930995)) (.branch 55 (.leaf 1526843748) (.leaf 1498438351))) (.branch 58 (.branch 57 (.leaf 1470692018) (.leaf 1443583014)) (.branch 59 (.leaf 1417090594) (.leaf 1391194948))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1365877154) (.branch 62 (.leaf 1341119125) (.leaf 1316903567))) (.branch 65 (.branch 64 (.leaf 1293213935) (.leaf 1270034395)) (.branch 66 (.leaf 1247349784) (.leaf 1225145575)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1203407847) (.leaf 1182123249)) (.branch 70 (.leaf 1161278972) (.leaf 1140862724))) (.branch 73 (.branch 72 (.leaf 1120862699) (.leaf 1101267555)) (.branch 74 (.leaf 1082066393) (.leaf 1063248729))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1044804478) (.branch 77 (.leaf 1026723934) (.leaf 1008997749))) (.branch 80 (.branch 79 (.leaf 991616917) (.leaf 974572760)) (.branch 81 (.leaf 957856908) (.leaf 941461286)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 925378103) (.leaf 909599834)) (.branch 85 (.leaf 894119211) (.leaf 878929210))) (.branch 88 (.branch 87 (.leaf 864023042) (.leaf 849394137)) (.branch 89 (.leaf 835036141) (.leaf 820942902)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 807108462) (.branch 92 (.leaf 793527049) (.leaf 780193071))) (.branch 95 (.branch 94 (.leaf 767101103) (.leaf 754245886)) (.branch 96 (.leaf 741622316) (.leaf 729225438)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 717050444) (.leaf 705092661)) (.branch 100 (.leaf 693347549) (.leaf 681810695))) (.branch 103 (.branch 102 (.leaf 670477810) (.leaf 659344719)) (.branch 104 (.leaf 648407364) (.leaf 637661791))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 627104155) (.leaf 616730708)) (.branch 108 (.leaf 606537802) (.leaf 596521880))) (.branch 111 (.branch 110 (.leaf 586679476) (.leaf 577007211)) (.branch 112 (.leaf 567501789) (.leaf 558159997)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 548978697) (.leaf 539954828)) (.branch 116 (.leaf 531085404) (.leaf 522367506))) (.branch 119 (.branch 118 (.leaf 513798284) (.leaf 505374957)) (.branch 120 (.leaf 497094803) (.leaf 488955167)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 56).prefactor = (331707282198849/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 56).cutoff/(generalMeanRows 56).c)).2 =
    (31298123048607/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 56).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 56).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 56).q*(generalMeanRows 56).c/2-2 = (51/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable036.value]
    have hcontinuation : (generalMeanRows 56).q*(generalMeanRows 56).cutoff/2-2 = (127/54:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable035.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 56).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 56

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 56).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 56).criticalRate j.val*(generalMeanRows 56).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 56).c*(generalMeanRows 56).criticalPoint j.val)).2-
      (generalMeanRows 56).J/2-(generalMeanRows 56).error (generalMeanGrid j.val)+
      (generalMeanRows 56).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 56).c)).2-
      (generalMeanRows 56).J/2-(generalMeanRows 56).error 4 := by
  have he : (generalMeanRows 56).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 56) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 56)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0056

/-! Kernel-checked entropy margins for general spectral rectangle 57. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0057
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5753201428) (.branch 2 (.leaf 5565747600) (.leaf 5387329891))) (.branch 5 (.branch 4 (.leaf 5217385705) (.leaf 5055394098)) (.branch 6 (.leaf 4900872133) (.leaf 4753371607)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4612476131) (.leaf 4477798486)) (.branch 10 (.leaf 4348978256) (.leaf 4225679678))) (.branch 13 (.branch 12 (.leaf 4107589698) (.leaf 3994416206)) (.branch 14 (.leaf 3885886432) (.leaf 3781745486))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3681755018) (.branch 17 (.leaf 3585692004) (.leaf 3493347627))) (.branch 20 (.branch 19 (.leaf 3404526254) (.leaf 3319044494)) (.branch 21 (.leaf 3236730339) (.leaf 3157422364)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3080968997) (.leaf 3007227844)) (.branch 25 (.leaf 2936065063) (.leaf 2867354790))) (.branch 28 (.branch 27 (.leaf 2800978605) (.leaf 2736825038)) (.branch 29 (.leaf 2674789111) (.leaf 2614771917)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2556680221) (.branch 32 (.leaf 2500426101) (.leaf 2445926603))) (.branch 35 (.branch 34 (.leaf 2393103430) (.leaf 2341882642)) (.branch 36 (.leaf 2292194389) (.leaf 2243972652)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2197155007) (.leaf 2151682404)) (.branch 40 (.leaf 2107498960) (.leaf 2064551766))) (.branch 43 (.branch 42 (.leaf 2022790705) (.leaf 1982168290)) (.branch 44 (.leaf 1942639499) (.leaf 1904161633))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1866694178) (.branch 47 (.leaf 1830198676) (.leaf 1794638601))) (.branch 50 (.branch 49 (.leaf 1759979255) (.leaf 1726187651)) (.branch 51 (.leaf 1693232424) (.leaf 1661083733)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1629713176) (.leaf 1599093706)) (.branch 55 (.leaf 1569199557) (.leaf 1540006172))) (.branch 58 (.branch 57 (.leaf 1511490135) (.leaf 1483629107)) (.branch 59 (.leaf 1456401766) (.leaf 1429787756))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1403767627) (.branch 62 (.leaf 1378322791) (.leaf 1353435475))) (.branch 65 (.branch 64 (.leaf 1329088675) (.leaf 1305266116)) (.branch 66 (.leaf 1281952217) (.leaf 1259132047)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1236791297) (.leaf 1214916248)) (.branch 70 (.leaf 1193493735) (.leaf 1172511125))) (.branch 73 (.branch 72 (.leaf 1151956284) (.leaf 1131817556)) (.branch 74 (.leaf 1112083739) (.leaf 1092744059))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1073788150) (.branch 77 (.leaf 1055206038) (.leaf 1036988115))) (.branch 80 (.branch 79 (.leaf 1019125126) (.leaf 1001608151)) (.branch 81 (.leaf 984428588) (.leaf 967578139)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 951048796) (.leaf 934832826)) (.branch 85 (.leaf 918922759) (.leaf 903311376))) (.branch 88 (.branch 87 (.leaf 887991699) (.leaf 872956978)) (.branch 89 (.leaf 858200680) (.leaf 843716483)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 829498265) (.branch 92 (.leaf 815540094) (.leaf 801836221))) (.branch 95 (.branch 94 (.leaf 788381072) (.leaf 775169241)) (.branch 96 (.leaf 762195483) (.leaf 749454707)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 736941970) (.leaf 724652469)) (.branch 100 (.leaf 712581538) (.leaf 700724643))) (.branch 103 (.branch 102 (.leaf 689077375) (.leaf 677635444)) (.branch 104 (.leaf 666394678) (.leaf 655351015))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 644500502) (.leaf 633839288)) (.branch 108 (.leaf 623363623) (.leaf 613069851))) (.branch 111 (.branch 110 (.leaf 602954412) (.leaf 593013830)) (.branch 112 (.leaf 583244721) (.leaf 573643780)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 564207784) (.leaf 554933587)) (.branch 116 (.leaf 545818117) (.leaf 536858378))) (.branch 119 (.branch 118 (.leaf 528051440) (.leaf 519394443)) (.branch 120 (.leaf 510884592) (.leaf 502519155)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 57).prefactor = (2727272758836693/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 57).cutoff/(generalMeanRows 57).c)).2 =
    (31298123048607/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 57).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 57).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 57).q*(generalMeanRows 57).c/2-2 = (51/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable036.value]
    have hcontinuation : (generalMeanRows 57).q*(generalMeanRows 57).cutoff/2-2 = (127/54:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable035.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 57).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 57

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 57).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 57).criticalRate j.val*(generalMeanRows 57).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 57).c*(generalMeanRows 57).criticalPoint j.val)).2-
      (generalMeanRows 57).J/2-(generalMeanRows 57).error (generalMeanGrid j.val)+
      (generalMeanRows 57).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 57).c)).2-
      (generalMeanRows 57).J/2-(generalMeanRows 57).error 4 := by
  have he : (generalMeanRows 57).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 57) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 57)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0057

/-! Kernel-checked entropy margins for general spectral rectangle 58. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0058
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5912799617) (.branch 2 (.leaf 5720145678) (.leaf 5536778526))) (.branch 5 (.branch 4 (.leaf 5362119958) (.leaf 5195634581)) (.branch 6 (.leaf 5036826058) (.leaf 4885233756)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4740429732) (.leaf 4602016026)) (.branch 10 (.leaf 4469622225) (.leaf 4342903251))) (.branch 13 (.branch 12 (.leaf 4221537365) (.leaf 4105224354)) (.branch 14 (.leaf 3993683882) (.leaf 3886653986))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3783889706) (.branch 17 (.leaf 3685161831) (.leaf 3590255751))) (.branch 20 (.branch 19 (.leaf 3498970405) (.leaf 3411117317)) (.branch 21 (.leaf 3326519704) (.leaf 3245011665)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3166437424) (.leaf 3090650635)) (.branch 25 (.leaf 3017513744) (.leaf 2946897396))) (.branch 28 (.branch 27 (.leaf 2878679885) (.leaf 2812746649)) (.branch 29 (.leaf 2748989798) (.leaf 2687307681)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2627604478) (.branch 32 (.leaf 2569789825) (.leaf 2513778470))) (.branch 35 (.branch 34 (.leaf 2459489942) (.leaf 2406848250)) (.branch 36 (.leaf 2355781607) (.leaf 2306222162)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2258105760) (.leaf 2211371713)) (.branch 40 (.leaf 2165962587) (.leaf 2121824004))) (.branch 43 (.branch 42 (.leaf 2078904460) (.leaf 2037155148)) (.branch 44 (.leaf 1996529798) (.leaf 1956984527))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1918477697) (.branch 47 (.leaf 1880969781) (.leaf 1844423243))) (.branch 50 (.branch 49 (.leaf 1808802420) (.leaf 1774073411)) (.branch 51 (.leaf 1740203981) (.leaf 1707163461)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1674922661) (.leaf 1643453783)) (.branch 55 (.leaf 1612730348) (.leaf 1582727116))) (.branch 58 (.branch 57 (.leaf 1553420023) (.leaf 1524786108)) (.branch 59 (.leaf 1496803461) (.leaf 1469451157))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1442709210) (.branch 62 (.leaf 1416558515) (.leaf 1390980806))) (.branch 65 (.branch 64 (.leaf 1365958607) (.leaf 1341475193)) (.branch 66 (.leaf 1317514548) (.leaf 1294061329)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1271100830) (.leaf 1248618950)) (.branch 70 (.leaf 1226602161) (.leaf 1205037476))) (.branch 73 (.branch 72 (.leaf 1183912428) (.leaf 1163215037)) (.branch 74 (.leaf 1142933789) (.leaf 1123057611))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1103575851) (.branch 77 (.leaf 1084478257) (.leaf 1065754955))) (.branch 80 (.branch 79 (.leaf 1047396433) (.leaf 1029393524)) (.branch 81 (.leaf 1011737386) (.leaf 994419494)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 977431614) (.leaf 960765800)) (.branch 85 (.leaf 944414376) (.leaf 928369922))) (.branch 88 (.branch 87 (.leaf 912625265) (.leaf 897173469)) (.branch 89 (.leaf 882007820) (.leaf 867121821)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 852509179) (.branch 92 (.leaf 838163797) (.leaf 824079768))) (.branch 95 (.branch 94 (.leaf 810251363) (.leaf 796673026)) (.branch 96 (.leaf 783339367) (.leaf 770245152)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 757385301) (.leaf 744754880)) (.branch 100 (.leaf 732349093) (.leaf 720163279))) (.branch 103 (.branch 102 (.leaf 708192906) (.leaf 696433567)) (.branch 104 (.leaf 684880974) (.leaf 673530951))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 662379437) (.leaf 651422473)) (.branch 108 (.leaf 640656204) (.leaf 630076876))) (.branch 111 (.branch 110 (.leaf 619680826) (.leaf 609464486)) (.branch 112 (.leaf 599424374) (.leaf 589557095)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 579859338) (.leaf 570327867)) (.branch 116 (.leaf 560959528) (.leaf 551751238))) (.branch 119 (.branch 118 (.leaf 542699989) (.leaf 533802840)) (.branch 120 (.leaf 525056919) (.leaf 516459420)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 58).prefactor = (1401464691208119/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 58).cutoff/(generalMeanRows 58).c)).2 =
    (31298123048607/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 58).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 58).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 58).q*(generalMeanRows 58).c/2-2 = (51/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable036.value]
    have hcontinuation : (generalMeanRows 58).q*(generalMeanRows 58).cutoff/2-2 = (127/54:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable035.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 58).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 58

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 58).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 58).criticalRate j.val*(generalMeanRows 58).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 58).c*(generalMeanRows 58).criticalPoint j.val)).2-
      (generalMeanRows 58).J/2-(generalMeanRows 58).error (generalMeanGrid j.val)+
      (generalMeanRows 58).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 58).c)).2-
      (generalMeanRows 58).J/2-(generalMeanRows 58).error 4 := by
  have he : (generalMeanRows 58).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 58) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 58)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0058

/-! Kernel-checked entropy margins for general spectral rectangle 59. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0059
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6076825182) (.branch 2 (.leaf 5878826876) (.leaf 5690372979))) (.branch 5 (.branch 4 (.leaf 5510869250) (.leaf 5339765441)) (.branch 6 (.leaf 5176551450) (.leaf 5020753862)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4871932863) (.leaf 4729679456)) (.branch 10 (.leaf 4593612950) (.leaf 4463378695))) (.branch 13 (.branch 12 (.leaf 4338646026) (.leaf 4219106404)) (.branch 14 (.leaf 4104471714) (.leaf 3994472728))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3888857689) (.branch 17 (.leaf 3787391027) (.leaf 3689852180))) (.branch 20 (.branch 19 (.leaf 3596034509) (.leaf 3505744309)) (.branch 21 (.leaf 3418799894) (.leaf 3335030761)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3254276810) (.leaf 3176387637)) (.branch 25 (.leaf 3101221874) (.leaf 3028646574))) (.branch 28 (.branch 27 (.leaf 2958536658) (.leaf 2890774383)) (.branch 29 (.leaf 2825248869) (.leaf 2761855643)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2700496227) (.branch 32 (.leaf 2641077752) (.leaf 2583512600))) (.branch 35 (.branch 34 (.leaf 2527718066) (.leaf 2473616054)) (.branch 36 (.leaf 2421132783) (.leaf 2370198521)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2320747334) (.leaf 2272716849)) (.branch 40 (.leaf 2226048038) (.leaf 2180685018))) (.branch 43 (.branch 42 (.leaf 2136574853) (.leaf 2093667383)) (.branch 44 (.leaf 2051915055) (.leaf 2011272768))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1971697729) (.branch 47 (.leaf 1933149315) (.leaf 1895588949))) (.branch 50 (.branch 49 (.leaf 1858979976) (.leaf 1823287559)) (.branch 51 (.leaf 1788478565) (.leaf 1754521476)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1721386291) (.leaf 1689044443)) (.branch 55 (.leaf 1657468716) (.leaf 1626633172))) (.branch 58 (.branch 57 (.leaf 1596513077) (.leaf 1567084836)) (.branch 59 (.leaf 1538325929) (.leaf 1510214852))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1482731062) (.branch 62 (.leaf 1455854927) (.leaf 1429567673))) (.branch 65 (.branch 64 (.leaf 1403851339) (.leaf 1378688736)) (.branch 66 (.leaf 1354063405) (.leaf 1329959576)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1306362135) (.leaf 1283256591)) (.branch 70 (.leaf 1260629039) (.leaf 1238466134))) (.branch 73 (.branch 72 (.leaf 1216755061) (.leaf 1195483508)) (.branch 74 (.leaf 1174639643) (.leaf 1154212085))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1134189886) (.branch 77 (.leaf 1114562510) (.leaf 1095319809))) (.branch 80 (.branch 79 (.leaf 1076452008) (.leaf 1057949684)) (.branch 81 (.leaf 1039803752) (.leaf 1022005448)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1004546311) (.leaf 987418175)) (.branch 85 (.leaf 970613150) (.leaf 954123610))) (.branch 88 (.branch 87 (.leaf 937942185) (.leaf 922061744)) (.branch 89 (.leaf 906475389) (.leaf 891176441)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 876158433) (.branch 92 (.leaf 861415099) (.leaf 846940369))) (.branch 95 (.branch 94 (.leaf 832728353) (.leaf 818773343)) (.branch 96 (.leaf 805069797) (.leaf 791612339)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 778395746) (.leaf 765414948)) (.branch 100 (.leaf 752665014) (.leaf 740141157))) (.branch 103 (.branch 102 (.leaf 727838717) (.leaf 715753165)) (.branch 104 (.leaf 703880094) (.leaf 692215213))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 680754347) (.leaf 669493428)) (.branch 108 (.leaf 658428495) (.leaf 647555688))) (.branch 111 (.branch 110 (.leaf 636871244) (.leaf 626371495)) (.branch 112 (.leaf 616052863) (.leaf 605911858)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 595945077) (.leaf 586149196)) (.branch 116 (.leaf 576520972) (.leaf 567057238))) (.branch 119 (.branch 118 (.leaf 557754900) (.leaf 548610938)) (.branch 120 (.leaf 539622398) (.leaf 530786397)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 59).prefactor = (1440342389179181/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 59).cutoff/(generalMeanRows 59).c)).2 =
    (31298123048607/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 59).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 59).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 59).q*(generalMeanRows 59).c/2-2 = (51/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable036.value]
    have hcontinuation : (generalMeanRows 59).q*(generalMeanRows 59).cutoff/2-2 = (127/54:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable035.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 59).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 59

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 59).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 59).criticalRate j.val*(generalMeanRows 59).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 59).c*(generalMeanRows 59).criticalPoint j.val)).2-
      (generalMeanRows 59).J/2-(generalMeanRows 59).error (generalMeanGrid j.val)+
      (generalMeanRows 59).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 59).c)).2-
      (generalMeanRows 59).J/2-(generalMeanRows 59).error 4 := by
  have he : (generalMeanRows 59).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 59) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 59)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0059

/-! Kernel-checked entropy margins for general spectral rectangle 60. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0060
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7810652818) (.branch 2 (.leaf 7572364891) (.leaf 7344833644))) (.branch 5 (.branch 4 (.leaf 7127445772) (.leaf 6919630936)) (.branch 6 (.leaf 6720857977) (.leaf 6530631546)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6348489106) (.leaf 6173998239)) (.branch 10 (.leaf 6006754238) (.leaf 5846377935))) (.branch 13 (.branch 12 (.leaf 5692513740) (.leaf 5544827868)) (.branch 14 (.leaf 5403006730) (.leaf 5266755471))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5135796634) (.branch 17 (.leaf 5009868945) (.leaf 4888726199))) (.branch 20 (.branch 19 (.leaf 4772136237) (.leaf 4659880012)) (.branch 21 (.leaf 4551750721) (.leaf 4447553015)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4347102262) (.leaf 4250223875)) (.branch 25 (.leaf 4156752677) (.leaf 4066532327))) (.branch 28 (.branch 27 (.leaf 3979414779) (.leaf 3895259779)) (.branch 29 (.leaf 3813934404) (.leaf 3735312624)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3659274902) (.branch 32 (.leaf 3585707818) (.leaf 3514503714))) (.branch 35 (.branch 34 (.leaf 3445560369) (.leaf 3378780690)) (.branch 36 (.leaf 3314072427) (.leaf 3251347900)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3190523753) (.leaf 3131520709)) (.branch 40 (.leaf 3074263357) (.leaf 3018679936))) (.branch 43 (.branch 42 (.leaf 2964702144) (.leaf 2912264953)) (.branch 44 (.leaf 2861306431) (.leaf 2811767586))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2763592207) (.branch 47 (.leaf 2716726722) (.leaf 2671120061))) (.branch 50 (.branch 49 (.leaf 2626723526) (.leaf 2583490669)) (.branch 51 (.leaf 2541377181) (.leaf 2500340781)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2460341113) (.leaf 2421339651)) (.branch 55 (.leaf 2383299608) (.leaf 2346185846))) (.branch 58 (.branch 57 (.leaf 2309964800) (.leaf 2274604395)) (.branch 59 (.leaf 2240073976) (.leaf 2206344238))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2173387159) (.branch 62 (.leaf 2141175940) (.leaf 2109684944))) (.branch 65 (.branch 64 (.leaf 2078889641) (.leaf 2048766554)) (.branch 66 (.leaf 2019293211) (.leaf 1990448095)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1962210598) (.leaf 1934560981)) (.branch 70 (.leaf 1907480331) (.leaf 1880950523))) (.branch 73 (.branch 72 (.leaf 1854954183) (.leaf 1829474652)) (.branch 74 (.leaf 1804495955) (.leaf 1780002768))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1755980388) (.branch 77 (.leaf 1732414705) (.leaf 1709292173))) (.branch 80 (.branch 79 (.leaf 1686599787) (.leaf 1664325059)) (.branch 81 (.leaf 1642455989) (.leaf 1620981049)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1599889159) (.leaf 1579169668)) (.branch 85 (.leaf 1558812333) (.leaf 1538807303))) (.branch 88 (.branch 87 (.leaf 1519145101) (.leaf 1499816606)) (.branch 89 (.leaf 1480813039) (.leaf 1462125947)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1443747189) (.branch 92 (.leaf 1425668923) (.leaf 1407883592))) (.branch 95 (.branch 94 (.leaf 1390383913) (.leaf 1373162864)) (.branch 96 (.leaf 1356213672) (.leaf 1339529805)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1323104959) (.leaf 1306933050)) (.branch 100 (.leaf 1291008203) (.leaf 1275324746))) (.branch 103 (.branch 102 (.leaf 1259877200) (.leaf 1244660269)) (.branch 104 (.leaf 1229668834) (.leaf 1214897948))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1200342824) (.leaf 1185998833)) (.branch 108 (.leaf 1171861494) (.leaf 1157926471))) (.branch 111 (.branch 110 (.leaf 1144189564) (.leaf 1130646707)) (.branch 112 (.leaf 1117293960) (.leaf 1104127503)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1091143635) (.leaf 1078338766)) (.branch 116 (.leaf 1065709415) (.leaf 1053252204))) (.branch 119 (.branch 118 (.leaf 1040963853) (.leaf 1028841180)) (.branch 120 (.leaf 1016881093) (.leaf 1005080589)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 60).prefactor = (2809046487230661/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 60).cutoff/(generalMeanRows 60).c)).2 =
    (224975360190751/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 60).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 60).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 60).q*(generalMeanRows 60).c/2-2 = (43/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable022.value]
    have hcontinuation : (generalMeanRows 60).q*(generalMeanRows 60).cutoff/2-2 = (67/37:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable037.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 60).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 60

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 60).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 60).criticalRate j.val*(generalMeanRows 60).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 60).c*(generalMeanRows 60).criticalPoint j.val)).2-
      (generalMeanRows 60).J/2-(generalMeanRows 60).error (generalMeanGrid j.val)+
      (generalMeanRows 60).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 60).c)).2-
      (generalMeanRows 60).J/2-(generalMeanRows 60).error 4 := by
  have he : (generalMeanRows 60).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 60) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 60)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0060

/-! Kernel-checked entropy margins for general spectral rectangle 61. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0061
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8034135346) (.branch 2 (.leaf 7783994821) (.leaf 7545142549))) (.branch 5 (.branch 4 (.leaf 7316935881) (.leaf 7098777192)) (.branch 6 (.leaf 6890109912) (.leaf 6690414991)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6499207758) (.leaf 6316035099)) (.branch 10 (.leaf 6140472929) (.leaf 5972123920))) (.branch 13 (.branch 12 (.leaf 5810615440) (.leaf 5655597701)) (.branch 14 (.leaf 5506742067) (.leaf 5363739526))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5226299288) (.branch 17 (.leaf 5094147512) (.leaf 4967026140))) (.branch 20 (.branch 19 (.leaf 4844691823) (.leaf 4726914941)) (.branch 21 (.leaf 4613478702) (.leaf 4504178303)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4398820168) (.leaf 4297221235)) (.branch 25 (.leaf 4199208300) (.leaf 4104617410))) (.branch 28 (.branch 27 (.leaf 4013293294) (.leaf 3925088845)) (.branch 29 (.leaf 3839864630) (.leaf 3757488434)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3677834840) (.branch 32 (.leaf 3600784837) (.leaf 3526225447))) (.branch 35 (.branch 34 (.leaf 3454049383) (.leaf 3384154733)) (.branch 36 (.leaf 3316444649) (.leaf 3250827075)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3187214478) (.leaf 3125523600)) (.branch 40 (.leaf 3065675230) (.leaf 3007593979))) (.branch 43 (.branch 42 (.leaf 2951208082) (.leaf 2896449200)) (.branch 44 (.leaf 2843252241) (.leaf 2791555189))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2741298943) (.branch 47 (.leaf 2692427163) (.leaf 2644886134))) (.branch 50 (.branch 49 (.leaf 2598624624) (.leaf 2553593759)) (.branch 51 (.leaf 2509746906) (.leaf 2467039555)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2425429217) (.leaf 2384875318)) (.branch 55 (.leaf 2345339106) (.leaf 2306783562))) (.branch 58 (.branch 57 (.leaf 2269173309) (.leaf 2232474538)) (.branch 59 (.leaf 2196654925) (.leaf 2161683564))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2127530893) (.branch 62 (.leaf 2094168634) (.leaf 2061569726))) (.branch 65 (.branch 64 (.leaf 2029708270) (.leaf 1998559473)) (.branch 66 (.leaf 1968099594) (.leaf 1938305896)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1909156597) (.leaf 1880630825)) (.branch 70 (.leaf 1852708577) (.leaf 1825370675))) (.branch 73 (.branch 72 (.leaf 1798598733) (.leaf 1772375113)) (.branch 74 (.leaf 1746682898) (.leaf 1721505854))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1696828398) (.branch 77 (.leaf 1672635573) (.leaf 1648913014))) (.branch 80 (.branch 79 (.leaf 1625646925) (.leaf 1602824053)) (.branch 81 (.leaf 1580431659) (.leaf 1558457501)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1536889807) (.leaf 1515717259)) (.branch 85 (.leaf 1494928967) (.leaf 1474514454))) (.branch 88 (.branch 87 (.leaf 1454463636) (.leaf 1434766807)) (.branch 89 (.leaf 1415414618) (.leaf 1396398066)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1377708478) (.branch 92 (.leaf 1359337494) (.leaf 1341277055))) (.branch 95 (.branch 94 (.leaf 1323519392) (.leaf 1306057012)) (.branch 96 (.leaf 1288882683) (.leaf 1271989431)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1255370519) (.leaf 1239019445)) (.branch 100 (.leaf 1222929930) (.leaf 1207095905))) (.branch 103 (.branch 102 (.leaf 1191511508) (.leaf 1176171070)) (.branch 104 (.leaf 1161069111) (.leaf 1146200330))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1131559601) (.leaf 1117141959)) (.branch 108 (.leaf 1102942601) (.leaf 1088956875))) (.branch 111 (.branch 110 (.leaf 1075180275) (.leaf 1061608437)) (.branch 112 (.leaf 1048237129) (.leaf 1035062251)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 1022079825) (.leaf 1009285993)) (.branch 116 (.leaf 996677013) (.leaf 984249252))) (.branch 119 (.branch 118 (.leaf 971999183) (.leaf 959923381)) (.branch 120 (.leaf 948018520) (.leaf 936281367)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 61).prefactor = (5897929619421179/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 61).cutoff/(generalMeanRows 61).c)).2 =
    (218840313894843/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 61).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 61).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 61).q*(generalMeanRows 61).c/2-2 = (23/50:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable014.value]
    have hcontinuation : (generalMeanRows 61).q*(generalMeanRows 61).cutoff/2-2 = (67/37:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable037.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 61).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 61

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 61).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 61).criticalRate j.val*(generalMeanRows 61).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 61).c*(generalMeanRows 61).criticalPoint j.val)).2-
      (generalMeanRows 61).J/2-(generalMeanRows 61).error (generalMeanGrid j.val)+
      (generalMeanRows 61).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 61).c)).2-
      (generalMeanRows 61).J/2-(generalMeanRows 61).error 4 := by
  have he : (generalMeanRows 61).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 61) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 61)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0061

/-! Kernel-checked entropy margins for general spectral rectangle 62. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0062
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7355388482) (.branch 2 (.leaf 7095914162) (.leaf 6848269914))) (.branch 5 (.branch 4 (.leaf 6611787453) (.leaf 6385845261)) (.branch 6 (.leaf 6169864457) (.leaf 5963305114)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5765662992) (.leaf 5576466597)) (.branch 10 (.leaf 5395274559) (.leaf 5221673259))) (.branch 13 (.branch 12 (.leaf 5055274694) (.leaf 4895714547)) (.branch 14 (.leaf 4742650436) (.leaf 4595760314))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4454741026) (.branch 17 (.leaf 4319306982) (.leaf 4189188945))) (.branch 20 (.branch 19 (.leaf 4064132919) (.leaf 3943899135)) (.branch 21 (.leaf 3828261109) (.leaf 3717004783)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3609927727) (.leaf 3506838404)) (.branch 25 (.leaf 3407555488) (.leaf 3311907240))) (.branch 28 (.branch 27 (.leaf 3219730916) (.leaf 3130872231)) (.branch 29 (.leaf 3045184852) (.leaf 2962529928)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2882775655) (.branch 32 (.leaf 2805796869) (.leaf 2731474662))) (.branch 35 (.branch 34 (.leaf 2659696032) (.leaf 2590353546)) (.branch 36 (.leaf 2523345034) (.leaf 2458573295)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2395945823) (.leaf 2335374556)) (.branch 40 (.leaf 2276775632) (.leaf 2220069167))) (.branch 43 (.branch 42 (.leaf 2165179041) (.leaf 2112032697)) (.branch 44 (.leaf 2060560959) (.leaf 2010697854))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1962380441) (.branch 47 (.leaf 1915548663) (.leaf 1870145194))) (.branch 50 (.branch 49 (.leaf 1826115300) (.leaf 1783406710)) (.branch 51 (.leaf 1741969492) (.leaf 1701755935)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1662720438) (.leaf 1624819408)) (.branch 55 (.leaf 1588011158) (.leaf 1552255815))) (.branch 58 (.branch 57 (.leaf 1517515235) (.leaf 1483752912)) (.branch 59 (.leaf 1450933905) (.leaf 1419024762))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1387993447) (.branch 62 (.leaf 1357809272) (.leaf 1328442836))) (.branch 65 (.branch 64 (.leaf 1299865964) (.leaf 1272051647)) (.branch 66 (.leaf 1244973990) (.leaf 1218608159)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1192930333) (.leaf 1167917655)) (.branch 70 (.leaf 1143548191) (.leaf 1119800885))) (.branch 73 (.branch 72 (.leaf 1096655522) (.leaf 1074092687)) (.branch 74 (.leaf 1052093729) (.leaf 1030640732))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1009716472) (.branch 77 (.leaf 989304398) (.leaf 969388594))) (.branch 80 (.branch 79 (.leaf 949953751) (.leaf 930985147)) (.branch 81 (.leaf 912468615) (.leaf 894390520)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 876737737) (.leaf 859497631)) (.branch 85 (.leaf 842658031) (.leaf 826207214))) (.branch 88 (.branch 87 (.leaf 810133883) (.leaf 794427154)) (.branch 89 (.leaf 779076531) (.leaf 764071897)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 749403493) (.branch 92 (.leaf 735061905) (.leaf 721038051))) (.branch 95 (.branch 94 (.leaf 707323166) (.leaf 693908786)) (.branch 96 (.leaf 680786741) (.leaf 667949139)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 655388359) (.leaf 643097035)) (.branch 100 (.leaf 631068046) (.leaf 619294514))) (.branch 103 (.branch 102 (.leaf 607769782) (.leaf 596487417)) (.branch 104 (.leaf 585441192) (.leaf 574625086))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 564033267) (.leaf 553660093)) (.branch 108 (.leaf 543500100) (.leaf 533547995))) (.branch 111 (.branch 110 (.leaf 523798654) (.leaf 514247108)) (.branch 112 (.leaf 504888546) (.leaf 495718299)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 486731845) (.leaf 477924797)) (.branch 116 (.leaf 469292898) (.leaf 460832021))) (.branch 119 (.branch 118 (.leaf 452538158) (.leaf 444407420)) (.branch 120 (.leaf 436436032) (.leaf 428620328)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 62).prefactor = (1238340979893839/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 62).cutoff/(generalMeanRows 62).c)).2 =
    (355763505321799/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 62).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 62).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 62).q*(generalMeanRows 62).c/2-2 = (67/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable016.value]
    have hcontinuation : (generalMeanRows 62).q*(generalMeanRows 62).cutoff/2-2 = (67/37:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable037.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 62).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 62

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 62).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 62).criticalRate j.val*(generalMeanRows 62).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 62).c*(generalMeanRows 62).criticalPoint j.val)).2-
      (generalMeanRows 62).J/2-(generalMeanRows 62).error (generalMeanGrid j.val)+
      (generalMeanRows 62).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 62).c)).2-
      (generalMeanRows 62).J/2-(generalMeanRows 62).error 4 := by
  have he : (generalMeanRows 62).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 62) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 62)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0062

/-! Kernel-checked entropy margins for general spectral rectangle 63. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0063
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6630363848) (.branch 2 (.leaf 6424516478) (.leaf 6228174876))) (.branch 5 (.branch 4 (.leaf 6040780755) (.leaf 5861815485)) (.branch 6 (.leaf 5690796630) (.leaf 5527274860)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5370831194) (.leaf 5221074522)) (.branch 10 (.leaf 5077639375) (.leaf 4940183919))) (.branch 13 (.branch 12 (.leaf 4808388134) (.leaf 4681952169)) (.branch 14 (.leaf 4560594844) (.leaf 4444052286))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4332076684) (.branch 17 (.leaf 4224435155) (.leaf 4120908701))) (.branch 20 (.branch 19 (.leaf 4021291251) (.leaf 3925388790)) (.branch 21 (.leaf 3833018541) (.leaf 3744008232)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3658195399) (.leaf 3575426756)) (.branch 25 (.leaf 3495557608) (.leaf 3418451305))) (.branch 28 (.branch 27 (.leaf 3343978736) (.leaf 3272017866)) (.branch 29 (.leaf 3202453295) (.leaf 3135175856)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3070082236) (.branch 32 (.leaf 3007074629) (.leaf 2946060405))) (.branch 35 (.branch 34 (.leaf 2886951804) (.leaf 2829665653)) (.branch 36 (.leaf 2774123097) (.leaf 2720249352)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2667973468) (.leaf 2617228115)) (.branch 40 (.leaf 2567949371) (.leaf 2520076540))) (.branch 43 (.branch 42 (.leaf 2473551961) (.leaf 2428320846)) (.branch 44 (.leaf 2384331121) (.leaf 2341533271))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2299880208) (.branch 47 (.leaf 2259327130) (.leaf 2219831407))) (.branch 50 (.branch 49 (.leaf 2181352456) (.leaf 2143851633)) (.branch 51 (.leaf 2107292135) (.leaf 2071638894)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2036858492) (.leaf 2002919069)) (.branch 55 (.leaf 1969790247) (.leaf 1937443047))) (.branch 58 (.branch 57 (.leaf 1905849821) (.leaf 1874984180)) (.branch 59 (.leaf 1844820931) (.leaf 1815336016))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1786506452) (.branch 62 (.leaf 1758310277) (.leaf 1730726503))) (.branch 65 (.branch 64 (.leaf 1703735058) (.leaf 1677316749)) (.branch 66 (.leaf 1651453211) (.leaf 1626126871)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1601320906) (.leaf 1577019206)) (.branch 70 (.leaf 1553206341) (.leaf 1529867524))) (.branch 73 (.branch 72 (.leaf 1506988584) (.leaf 1484555933)) (.branch 74 (.leaf 1462556538) (.leaf 1440977898))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1419808011) (.branch 77 (.leaf 1399035360) (.leaf 1378648879))) (.branch 80 (.branch 79 (.leaf 1358637943) (.leaf 1338992338)) (.branch 81 (.leaf 1319702245) (.leaf 1300758223)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1282151191) (.leaf 1263872409)) (.branch 85 (.leaf 1245913464) (.leaf 1228266255))) (.branch 88 (.branch 87 (.leaf 1210922980) (.leaf 1193876118)) (.branch 89 (.leaf 1177118422) (.leaf 1160642902)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1144442817) (.branch 92 (.leaf 1128511661) (.leaf 1112843154))) (.branch 95 (.branch 94 (.leaf 1097431234) (.leaf 1082270042)) (.branch 96 (.leaf 1067353920) (.leaf 1052677395)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1038235178) (.leaf 1024022153)) (.branch 100 (.leaf 1010033366) (.leaf 996264025))) (.branch 103 (.branch 102 (.leaf 982709489) (.leaf 969365263)) (.branch 104 (.leaf 956226990) (.leaf 943290447))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 930551541) (.leaf 918006299)) (.branch 108 (.leaf 905650869) (.leaf 893481511))) (.branch 111 (.branch 110 (.leaf 881494592) (.leaf 869686586)) (.branch 112 (.leaf 858054067) (.leaf 846593702)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 835302255) (.leaf 824176576)) (.branch 116 (.leaf 813213602) (.leaf 802410351))) (.branch 119 (.branch 118 (.leaf 791763923) (.leaf 781271490)) (.branch 120 (.leaf 770930302) (.leaf 760737676)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 63).prefactor = (1312181102727523/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 63).cutoff/(generalMeanRows 63).c)).2 =
    (233535880580807/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 63).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 63).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 63).q*(generalMeanRows 63).c/2-2 = (201/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable029.value]
    have hcontinuation : (generalMeanRows 63).q*(generalMeanRows 63).cutoff/2-2 = (516/259:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable038.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 63).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 63

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 63).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 63).criticalRate j.val*(generalMeanRows 63).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 63).c*(generalMeanRows 63).criticalPoint j.val)).2-
      (generalMeanRows 63).J/2-(generalMeanRows 63).error (generalMeanGrid j.val)+
      (generalMeanRows 63).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 63).c)).2-
      (generalMeanRows 63).J/2-(generalMeanRows 63).error 4 := by
  have he : (generalMeanRows 63).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 63) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 63)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0063

/-! Kernel-checked entropy margins for general spectral rectangle 64. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0064
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6748627765) (.branch 2 (.leaf 6534942249) (.leaf 6331130491))) (.branch 5 (.branch 4 (.leaf 6136613564) (.leaf 5950853656)) (.branch 6 (.leaf 5773350471) (.leaf 5603638035)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5441281830) (.leaf 5285876229)) (.branch 10 (.leaf 5137042182) (.leaf 4994425135))) (.branch 13 (.branch 12 (.leaf 4857693146) (.leaf 4726535173)) (.branch 14 (.leaf 4600659527) (.leaf 4479792456))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4363676852) (.branch 17 (.leaf 4252071082) (.leaf 4144747896))) (.branch 20 (.branch 19 (.leaf 4041493447) (.leaf 3942106378)) (.branch 21 (.leaf 3846396981) (.leaf 3754186431)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3665306070) (.leaf 3579596752)) (.branch 25 (.leaf 3496908231) (.leaf 3417098602))) (.branch 28 (.branch 27 (.leaf 3340033770) (.leaf 3265586976)) (.branch 29 (.leaf 3193638335) (.leaf 3124074425)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3056787891) (.branch 32 (.leaf 2991677082) (.leaf 2928645717))) (.branch 35 (.branch 34 (.leaf 2867602561) (.leaf 2808461134)) (.branch 36 (.leaf 2751139432) (.leaf 2695559672)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2641648047) (.leaf 2589334500)) (.branch 40 (.leaf 2538552513) (.leaf 2489238907))) (.branch 43 (.branch 42 (.leaf 2441333656) (.leaf 2394779711)) (.branch 44 (.leaf 2349522835) (.leaf 2305511453))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2262696500) (.branch 47 (.leaf 2221031288) (.leaf 2180471379))) (.branch 50 (.branch 49 (.leaf 2140974460) (.leaf 2102500234)) (.branch 51 (.leaf 2065010307) (.leaf 2028468095)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1992838718) (.leaf 1958088922)) (.branch 55 (.leaf 1924186985) (.leaf 1891102642))) (.branch 58 (.branch 57 (.leaf 1858807010) (.leaf 1827272511)) (.branch 59 (.leaf 1796472814) (.leaf 1766382763))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1736978323) (.branch 62 (.leaf 1708236519) (.leaf 1680135387))) (.branch 65 (.branch 64 (.leaf 1652653918) (.leaf 1625772016)) (.branch 66 (.leaf 1599470445) (.leaf 1573730797)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1548535439) (.leaf 1523867485)) (.branch 70 (.leaf 1499710753) (.leaf 1476049735))) (.branch 73 (.branch 72 (.leaf 1452869560) (.leaf 1430155967)) (.branch 74 (.leaf 1407895274) (.leaf 1386074350))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1364680589) (.branch 77 (.leaf 1343701886) (.leaf 1323126611))) (.branch 80 (.branch 79 (.leaf 1302943590) (.leaf 1283142079)) (.branch 81 (.leaf 1263711750) (.leaf 1244642666)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1225925265) (.leaf 1207550345)) (.branch 85 (.leaf 1189509043) (.leaf 1171792825))) (.branch 88 (.branch 87 (.leaf 1154393465) (.leaf 1137303037)) (.branch 89 (.leaf 1120513897) (.leaf 1104018672)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1087810250) (.branch 92 (.leaf 1071881764) (.leaf 1056226587))) (.branch 95 (.branch 94 (.leaf 1040838314) (.leaf 1025710761)) (.branch 96 (.leaf 1010837949) (.leaf 996214096)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 981833612) (.leaf 967691088)) (.branch 100 (.leaf 953781289) (.leaf 940099147))) (.branch 103 (.branch 102 (.leaf 926639753) (.leaf 913398350)) (.branch 104 (.leaf 900370332) (.leaf 887551229))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 874936709) (.leaf 862522568)) (.branch 108 (.leaf 850304729) (.leaf 838279230))) (.branch 111 (.branch 110 (.leaf 826442228) (.leaf 814789988)) (.branch 112 (.leaf 803318881) (.leaf 792025381)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 780906059) (.leaf 769957578)) (.branch 116 (.leaf 759176697) (.leaf 748560256))) (.branch 119 (.branch 118 (.leaf 738105183) (.leaf 727808486)) (.branch 120 (.leaf 717667250) (.leaf 707678635)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 64).prefactor = (1090172128875227/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 64).cutoff/(generalMeanRows 64).c)).2 =
    (456142690629423/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 64).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 64).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 64).q*(generalMeanRows 64).c/2-2 = (53/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable031.value]
    have hcontinuation : (generalMeanRows 64).q*(generalMeanRows 64).cutoff/2-2 = (516/259:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable038.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 64).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 64

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 64).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 64).criticalRate j.val*(generalMeanRows 64).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 64).c*(generalMeanRows 64).criticalPoint j.val)).2-
      (generalMeanRows 64).J/2-(generalMeanRows 64).error (generalMeanGrid j.val)+
      (generalMeanRows 64).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 64).c)).2-
      (generalMeanRows 64).J/2-(generalMeanRows 64).error 4 := by
  have he : (generalMeanRows 64).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 64) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 64)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0064

/-! Kernel-checked entropy margins for general spectral rectangle 65. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0065
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6870176117) (.branch 2 (.leaf 6648443524) (.leaf 6436967118))) (.branch 5 (.branch 4 (.leaf 6235146499) (.leaf 6042423891)) (.branch 6 (.leaf 5858280415) (.leaf 5682232773)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5513830274) (.leaf 5352652177)) (.branch 10 (.leaf 5198305292) (.leaf 5050421820))) (.branch 13 (.branch 12 (.leaf 4908657399) (.leaf 4772689336)) (.branch 14 (.leaf 4642214992) (.leaf 4516950320))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4396628531) (.branch 17 (.leaf 4280998864) (.leaf 4169825478))) (.branch 20 (.branch 19 (.leaf 4062886414) (.leaf 3959972663)) (.branch 21 (.leaf 3860887289) (.leaf 3765444636)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3673469586) (.leaf 3584796878)) (.branch 25 (.leaf 3499270479) (.leaf 3416742998))) (.branch 28 (.branch 27 (.leaf 3337075145) (.leaf 3260135227)) (.branch 29 (.leaf 3185798682) (.leaf 3113947644)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3044470540) (.branch 32 (.leaf 2977261708) (.leaf 2912221053))) (.branch 35 (.branch 34 (.leaf 2849253712) (.leaf 2788269754)) (.branch 36 (.leaf 2729183887) (.leaf 2671915196)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2616386889) (.leaf 2562526065)) (.branch 40 (.leaf 2510263491) (.leaf 2459533399))) (.branch 43 (.branch 42 (.leaf 2410273290) (.leaf 2362423755)) (.branch 44 (.leaf 2315928302) (.leaf 2270733198))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2226787319) (.branch 47 (.leaf 2184042006) (.leaf 2142450934))) (.branch 50 (.branch 49 (.leaf 2101969984) (.leaf 2062557131)) (.branch 51 (.leaf 2024172326) (.leaf 1986777395)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1950335941) (.leaf 1914813248)) (.branch 55 (.leaf 1880176198) (.leaf 1846393182))) (.branch 58 (.branch 57 (.leaf 1813434027) (.leaf 1781269920)) (.branch 59 (.leaf 1749873341) (.leaf 1719217991))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1689278739) (.branch 62 (.leaf 1660031554) (.leaf 1631453457))) (.branch 65 (.branch 64 (.leaf 1603522463) (.leaf 1576217535)) (.branch 66 (.leaf 1549518536) (.leaf 1523406183)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1497862007) (.leaf 1472868312)) (.branch 70 (.leaf 1448408139) (.leaf 1424465227))) (.branch 73 (.branch 72 (.leaf 1401023982) (.leaf 1378069444)) (.branch 74 (.leaf 1355587258) (.leaf 1333563642))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1311985362) (.branch 77 (.leaf 1290839707) (.leaf 1270114461))) (.branch 80 (.branch 79 (.leaf 1249797885) (.leaf 1229878689)) (.branch 81 (.leaf 1210346015) (.leaf 1191189417)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1172398838) (.leaf 1153964599)) (.branch 85 (.leaf 1135877375) (.leaf 1118128183))) (.branch 88 (.branch 87 (.leaf 1100708367) (.leaf 1083609580)) (.branch 89 (.leaf 1066823773) (.leaf 1050343181)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1034160310) (.branch 92 (.leaf 1018267925) (.leaf 1002659041))) (.branch 95 (.branch 94 (.leaf 987326909) (.leaf 972265007)) (.branch 96 (.leaf 957467031) (.leaf 942926886)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 928638673) (.leaf 914596688)) (.branch 100 (.leaf 900795407) (.leaf 887229483))) (.branch 103 (.branch 102 (.leaf 873893736) (.leaf 860783148)) (.branch 104 (.leaf 847892853) (.leaf 835218138))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 822754427) (.leaf 810497284)) (.branch 108 (.leaf 798442403) (.leaf 786585605))) (.branch 111 (.branch 110 (.leaf 774922830) (.leaf 763450136)) (.branch 112 (.leaf 752163692) (.leaf 741059776)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 730134766) (.leaf 719385144)) (.branch 116 (.leaf 708807484) (.leaf 698398454))) (.branch 119 (.branch 118 (.leaf 688154811) (.leaf 678073398)) (.branch 120 (.leaf 668151138) (.leaf 658385036)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 65).prefactor = (1132156289350949/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 65).cutoff/(generalMeanRows 65).c)).2 =
    (445331774525207/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 65).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 65).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 65).q*(generalMeanRows 65).c/2-2 = (223/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable017.value]
    have hcontinuation : (generalMeanRows 65).q*(generalMeanRows 65).cutoff/2-2 = (516/259:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable038.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 65).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 65

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 65).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 65).criticalRate j.val*(generalMeanRows 65).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 65).c*(generalMeanRows 65).criticalPoint j.val)).2-
      (generalMeanRows 65).J/2-(generalMeanRows 65).error (generalMeanGrid j.val)+
      (generalMeanRows 65).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 65).c)).2-
      (generalMeanRows 65).J/2-(generalMeanRows 65).error 4 := by
  have he : (generalMeanRows 65).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 65) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 65)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0065

/-! Kernel-checked entropy margins for general spectral rectangle 66. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0066
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5900215532) (.branch 2 (.leaf 5675895776) (.leaf 5462236325))) (.branch 5 (.branch 4 (.leaf 5258618670) (.leaf 5064468005)) (.branch 6 (.leaf 4879249407) (.leaf 4702464429)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4533648050) (.leaf 4372365944)) (.branch 10 (.leaf 4218212023) (.leaf 4070806221))) (.branch 13 (.branch 12 (.leaf 3929792492) (.leaf 3794836991)) (.branch 14 (.leaf 3665626432) (.leaf 3541866579))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3423280886) (.branch 17 (.leaf 3309609240) (.leaf 3200606818))) (.branch 20 (.branch 19 (.leaf 3096043038) (.leaf 2995700594)) (.branch 21 (.leaf 2899374567) (.leaf 2806871612)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2718009198) (.leaf 2632614916)) (.branch 25 (.leaf 2550525832) (.leaf 2471587893))) (.branch 28 (.branch 27 (.leaf 2395655371) (.leaf 2322590349)) (.branch 29 (.leaf 2252262247) (.leaf 2184547378)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2119328532) (.branch 32 (.leaf 2056494594) (.leaf 1995940185))) (.branch 35 (.branch 34 (.leaf 1937565324) (.leaf 1881275123)) (.branch 36 (.leaf 1826979484) (.leaf 1774592837)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1724033874) (.leaf 1675225316)) (.branch 40 (.leaf 1628093688) (.leaf 1582569104))) (.branch 43 (.branch 42 (.leaf 1538585076) (.leaf 1496078322)) (.branch 44 (.leaf 1454988596) (.leaf 1415258525))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1376833450) (.branch 47 (.leaf 1339661289) (.leaf 1303692393))) (.branch 50 (.branch 49 (.leaf 1268879422) (.leaf 1235177225)) (.branch 51 (.leaf 1202542724) (.leaf 1170934807)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1140314227) (.leaf 1110643508)) (.branch 55 (.leaf 1081886853) (.leaf 1054010059))) (.branch 58 (.branch 57 (.leaf 1026980440) (.leaf 1000766745)) (.branch 59 (.leaf 975339094) (.leaf 950668903))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 926728825) (.branch 62 (.leaf 903492686) (.leaf 880935431))) (.branch 65 (.branch 64 (.leaf 859033066) (.leaf 837762611)) (.branch 66 (.leaf 817102046) (.leaf 797030271)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 777527058) (.leaf 758573010)) (.branch 70 (.leaf 740149523) (.leaf 722238750))) (.branch 73 (.branch 72 (.leaf 704823563) (.leaf 687887521)) (.branch 74 (.leaf 671414839) (.leaf 655390355))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 639799505) (.branch 77 (.leaf 624628296) (.leaf 609863274))) (.branch 80 (.branch 79 (.leaf 595491509) (.leaf 581500562)) (.branch 81 (.leaf 567878473) (.leaf 554613729)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 541695255) (.leaf 529112386)) (.branch 85 (.leaf 516854854) (.leaf 504912770))) (.branch 88 (.branch 87 (.leaf 493276606) (.leaf 481937181)) (.branch 89 (.leaf 470885647) (.leaf 460113472)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 449612428) (.branch 92 (.leaf 439374580) (.leaf 429392271))) (.branch 95 (.branch 94 (.leaf 419658113) (.leaf 410164972)) (.branch 96 (.leaf 400905963) (.leaf 391874434)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 383063963) (.leaf 374468341)) (.branch 100 (.leaf 366081571) (.leaf 357897854))) (.branch 103 (.branch 102 (.leaf 349911584) (.leaf 342117339)) (.branch 104 (.leaf 334509875) (.leaf 327084119))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 319835160) (.leaf 312758245)) (.branch 108 (.leaf 305848774) (.leaf 299102291))) (.branch 111 (.branch 110 (.leaf 292514481) (.leaf 286081163)) (.branch 112 (.leaf 279798287) (.leaf 273661927)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 267668278) (.leaf 261813650)) (.branch 116 (.leaf 256094467) (.leaf 250507258))) (.branch 119 (.branch 118 (.leaf 245048657) (.leaf 239715397)) (.branch 120 (.leaf 234504311) (.leaf 229412320)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 66).prefactor = (5878786613446863/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 66).cutoff/(generalMeanRows 66).c)).2 =
    (171601139724413/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 66).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 66).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 66).q*(generalMeanRows 66).c/2-2 = (333/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable039.value]
    have hcontinuation : (generalMeanRows 66).q*(generalMeanRows 66).cutoff/2-2 = (516/259:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable038.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 66).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 66

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 66).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 66).criticalRate j.val*(generalMeanRows 66).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 66).c*(generalMeanRows 66).criticalPoint j.val)).2-
      (generalMeanRows 66).J/2-(generalMeanRows 66).error (generalMeanGrid j.val)+
      (generalMeanRows 66).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 66).c)).2-
      (generalMeanRows 66).J/2-(generalMeanRows 66).error 4 := by
  have he : (generalMeanRows 66).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 66) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 66)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0066

/-! Kernel-checked entropy margins for general spectral rectangle 67. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0067
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5613876334) (.branch 2 (.leaf 5440433830) (.leaf 5275160015))) (.branch 5 (.branch 4 (.leaf 5117556073) (.leaf 4967159571)) (.branch 6 (.leaf 4823541285) (.leaf 4686302364)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4555071785) (.leaf 4429504063)) (.branch 10 (.leaf 4309277194) (.leaf 4194090789))) (.branch 13 (.branch 12 (.leaf 4083664391) (.leaf 3977735940)) (.branch 14 (.leaf 3876060384) (.leaf 3778408411))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3684565288) (.branch 17 (.leaf 3594329804) (.leaf 3507513303))) (.branch 20 (.branch 19 (.leaf 3423938788) (.leaf 3343440111)) (.branch 21 (.leaf 3265861217) (.leaf 3191055455)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3118884936) (.leaf 3049219948)) (.branch 25 (.leaf 2981938409) (.leaf 2916925364))) (.branch 28 (.branch 27 (.leaf 2854072520) (.leaf 2793277811)) (.branch 29 (.leaf 2734445002) (.leaf 2677483309)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2622307061) (.branch 32 (.leaf 2568835374) (.leaf 2516991854))) (.branch 35 (.branch 34 (.leaf 2466704316) (.leaf 2417904527)) (.branch 36 (.leaf 2370527962) (.leaf 2324513580)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2279803611) (.leaf 2236343362)) (.branch 40 (.leaf 2194081030) (.leaf 2152967532))) (.branch 43 (.branch 42 (.leaf 2112956346) (.leaf 2074003357)) (.branch 44 (.leaf 2036066717) (.leaf 1999106715))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1963085652) (.branch 47 (.leaf 1927967725) (.leaf 1893718919))) (.branch 50 (.branch 49 (.leaf 1860306906) (.leaf 1827700946)) (.branch 51 (.leaf 1795871803) (.leaf 1764791654)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1734434015) (.leaf 1704773666)) (.branch 55 (.leaf 1675786579) (.leaf 1647449853))) (.branch 58 (.branch 57 (.leaf 1619741654) (.leaf 1592641155)) (.branch 59 (.leaf 1566128483) (.leaf 1540184664))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1514791580) (.branch 62 (.leaf 1489931920) (.leaf 1465589136))) (.branch 65 (.branch 64 (.leaf 1441747406) (.leaf 1418391594)) (.branch 66 (.leaf 1395507214) (.leaf 1373080395)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1351097852) (.leaf 1329546854)) (.branch 70 (.leaf 1308415195) (.leaf 1287691170))) (.branch 73 (.branch 72 (.leaf 1267363546) (.leaf 1247421540)) (.branch 74 (.leaf 1227854797) (.leaf 1208653368))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1189807689) (.branch 77 (.leaf 1171308565) (.leaf 1153147148))) (.branch 80 (.branch 79 (.leaf 1135314923) (.leaf 1117803691)) (.branch 81 (.leaf 1100605552) (.leaf 1083712895)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1067118380) (.leaf 1050814929)) (.branch 85 (.leaf 1034795711) (.leaf 1019054129))) (.branch 88 (.branch 87 (.leaf 1003583814) (.leaf 988378613)) (.branch 89 (.leaf 973432576) (.leaf 958739950)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 944295170) (.branch 92 (.leaf 930092850) (.leaf 916127774))) (.branch 95 (.branch 94 (.leaf 902394890) (.leaf 888889303)) (.branch 96 (.leaf 875606269) (.leaf 862541186)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 849689589) (.leaf 837047146)) (.branch 100 (.leaf 824609650) (.leaf 812373017))) (.branch 103 (.branch 102 (.leaf 800333276) (.leaf 788486571)) (.branch 104 (.leaf 776829150) (.leaf 765357366))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 754067669) (.leaf 742956604)) (.branch 108 (.leaf 732020809) (.leaf 721257007))) (.branch 111 (.branch 110 (.leaf 710662008) (.leaf 700232703)) (.branch 112 (.leaf 689966059) (.leaf 679859121)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 669909006) (.leaf 660112901)) (.branch 116 (.leaf 650468060) (.leaf 640971804))) (.branch 119 (.branch 118 (.leaf 631621516) (.leaf 622414640)) (.branch 120 (.leaf 613348678) (.leaf 604421190)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 67).prefactor = (4847530771447951/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 67).cutoff/(generalMeanRows 67).c)).2 =
    (502219148927257/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 67).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 67).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 67).q*(generalMeanRows 67).c/2-2 = (9/16:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable040.value]
    have hcontinuation : (generalMeanRows 67).q*(generalMeanRows 67).cutoff/2-2 = (248/111:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable041.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 67).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 67

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 67).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 67).criticalRate j.val*(generalMeanRows 67).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 67).c*(generalMeanRows 67).criticalPoint j.val)).2-
      (generalMeanRows 67).J/2-(generalMeanRows 67).error (generalMeanGrid j.val)+
      (generalMeanRows 67).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 67).c)).2-
      (generalMeanRows 67).J/2-(generalMeanRows 67).error 4 := by
  have he : (generalMeanRows 67).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 67) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 67)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0067

/-! Kernel-checked entropy margins for general spectral rectangle 68. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0068
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5665741066) (.branch 2 (.leaf 5487268490) (.leaf 5317212617))) (.branch 5 (.branch 4 (.leaf 5155060461) (.leaf 5000336430)) (.branch 6 (.leaf 4852599068) (.leaf 4711438130)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4576471971) (.leaf 4447345195)) (.branch 10 (.leaf 4323726534) (.leaf 4205306937))) (.branch 13 (.branch 12 (.leaf 4091797833) (.leaf 3982929561)) (.branch 14 (.leaf 3878449937) (.leaf 3778122953))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3681727585) (.branch 17 (.leaf 3589056703) (.leaf 3499916081))) (.branch 20 (.branch 19 (.leaf 3414123478) (.leaf 3331507799)) (.branch 21 (.leaf 3251908325) (.leaf 3175174000)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3101162776) (.leaf 3029741008)) (.branch 25 (.leaf 2960782897) (.leaf 2894169967))) (.branch 28 (.branch 27 (.leaf 2829790591) (.leaf 2767539545)) (.branch 29 (.leaf 2707317596) (.leaf 2649031122)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2592591752) (.branch 32 (.leaf 2537916042) (.leaf 2484925161))) (.branch 35 (.branch 34 (.leaf 2433544610) (.leaf 2383703954)) (.branch 36 (.leaf 2335336570) (.leaf 2288379421)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2242772835) (.leaf 2198460305)) (.branch 40 (.leaf 2155388299) (.leaf 2113506083))) (.branch 43 (.branch 42 (.leaf 2072765559) (.leaf 2033121107)) (.branch 44 (.leaf 1994529441) (.leaf 1956949474))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1920342193) (.branch 47 (.leaf 1884670535) (.leaf 1849899281))) (.branch 50 (.branch 49 (.leaf 1815994949) (.leaf 1782925693)) (.branch 51 (.leaf 1750661217) (.leaf 1719172682)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1688432629) (.leaf 1658414901)) (.branch 55 (.leaf 1629094572) (.leaf 1600447879))) (.branch 58 (.branch 57 (.leaf 1572452157) (.leaf 1545085782)) (.branch 59 (.leaf 1518328115) (.leaf 1492159444))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1466560942) (.branch 62 (.leaf 1441514614) (.leaf 1417003255))) (.branch 65 (.branch 64 (.leaf 1393010409) (.leaf 1369520328)) (.branch 66 (.leaf 1346517939) (.leaf 1323988802)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1301919085) (.leaf 1280295529)) (.branch 70 (.leaf 1259105418) (.leaf 1238336554))) (.branch 73 (.branch 72 (.leaf 1217977229) (.leaf 1198016201)) (.branch 74 (.leaf 1178442671) (.leaf 1159246261))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1140416993) (.branch 77 (.leaf 1121945270) (.leaf 1103821857))) (.branch 80 (.branch 79 (.leaf 1086037864) (.leaf 1068584728)) (.branch 81 (.leaf 1051454199) (.leaf 1034638325)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1018129437) (.leaf 1001920138)) (.branch 85 (.leaf 986003286) (.leaf 970371988))) (.branch 88 (.branch 87 (.leaf 955019584) (.leaf 939939638)) (.branch 89 (.leaf 925125929) (.leaf 910572439)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 896273348) (.branch 92 (.leaf 882223020) (.leaf 868415998))) (.branch 95 (.branch 94 (.leaf 854846998) (.leaf 841510898)) (.branch 96 (.leaf 828402732) (.leaf 815517685)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 802851085) (.leaf 790398400)) (.branch 100 (.leaf 778155226) (.leaf 766117290))) (.branch 103 (.branch 102 (.leaf 754280438) (.leaf 742640634)) (.branch 104 (.leaf 731193953) (.leaf 719936578))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 708864797) (.leaf 697974996)) (.branch 108 (.leaf 687263658) (.leaf 676727358))) (.branch 111 (.branch 110 (.leaf 666362758) (.leaf 656166607)) (.branch 112 (.leaf 646135737) (.leaf 636267059)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 626557560) (.leaf 617004300)) (.branch 116 (.leaf 607604413) (.leaf 598355099))) (.branch 119 (.branch 118 (.leaf 589253626) (.leaf 580297326)) (.branch 120 (.leaf 571483593) (.leaf 562809881)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 68).prefactor = (998150374603673/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 68).cutoff/(generalMeanRows 68).c)).2 =
    (246255167400149/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 68).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 68).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 68).q*(generalMeanRows 68).c/2-2 = (47/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable034.value]
    have hcontinuation : (generalMeanRows 68).q*(generalMeanRows 68).cutoff/2-2 = (248/111:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable041.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 68).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 68

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 68).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 68).criticalRate j.val*(generalMeanRows 68).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 68).c*(generalMeanRows 68).criticalPoint j.val)).2-
      (generalMeanRows 68).J/2-(generalMeanRows 68).error (generalMeanGrid j.val)+
      (generalMeanRows 68).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 68).c)).2-
      (generalMeanRows 68).J/2-(generalMeanRows 68).error 4 := by
  have he : (generalMeanRows 68).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 68) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 68)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0068

/-! Kernel-checked entropy margins for general spectral rectangle 69. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0069
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5718823777) (.branch 2 (.leaf 5535242063) (.leaf 5360332490))) (.branch 5 (.branch 4 (.leaf 5193567446) (.leaf 5034457758)) (.branch 6 (.leaf 4882549334) (.leaf 4737420166)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4598677641) (.leaf 4465956122)) (.branch 10 (.leaf 4338914773) (.leaf 4217235592))) (.branch 13 (.branch 12 (.leaf 4100621626) (.leaf 3988795357)) (.branch 14 (.leaf 3881497230) (.leaf 3778484315))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3679529081) (.branch 17 (.leaf 3584418284) (.leaf 3492951935))) (.branch 20 (.branch 19 (.leaf 3404942368) (.leaf 3320213374)) (.branch 21 (.leaf 3238599407) (.leaf 3159944857)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3084103371) (.leaf 3010937238)) (.branch 25 (.leaf 2940316808) (.leaf 2872119963))) (.branch 28 (.branch 27 (.leaf 2806231628) (.leaf 2742543307)) (.branch 29 (.leaf 2680952670) (.leaf 2621363152)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2563683591) (.branch 32 (.leaf 2507827890) (.leaf 2453714699))) (.branch 35 (.branch 34 (.leaf 2401267123) (.leaf 2350412445)) (.branch 36 (.leaf 2301081877) (.leaf 2253210312)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2206736111) (.leaf 2161600889)) (.branch 40 (.leaf 2117749327) (.leaf 2075128983))) (.branch 43 (.branch 42 (.leaf 2033690127) (.leaf 1993385584)) (.branch 44 (.leaf 1954170581) (.leaf 1916002609))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1878841295) (.branch 47 (.leaf 1842648276) (.leaf 1807387089))) (.branch 50 (.branch 49 (.leaf 1773023057) (.leaf 1739523196)) (.branch 51 (.leaf 1706856113) (.leaf 1674991922)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1643902157) (.leaf 1613559696)) (.branch 55 (.leaf 1583938687) (.leaf 1555014476))) (.branch 58 (.branch 57 (.leaf 1526763545) (.leaf 1499163450)) (.branch 59 (.leaf 1472192761) (.leaf 1445831009))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1420058636) (.branch 62 (.leaf 1394856945) (.leaf 1370208057))) (.branch 65 (.branch 64 (.leaf 1346094863) (.leaf 1322500990)) (.branch 66 (.leaf 1299410759) (.leaf 1276809152)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1254681774) (.leaf 1233014825)) (.branch 70 (.leaf 1211795069) (.leaf 1191009803))) (.branch 73 (.branch 72 (.leaf 1170646834) (.leaf 1150694452)) (.branch 74 (.leaf 1131141406) (.leaf 1111976879))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1093190473) (.branch 77 (.leaf 1074772182) (.leaf 1056712377))) (.branch 80 (.branch 79 (.leaf 1039001787) (.leaf 1021631480)) (.branch 81 (.leaf 1004592852) (.leaf 987877604)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 971477735) (.leaf 955385524)) (.branch 85 (.leaf 939593520) (.leaf 924094525))) (.branch 88 (.branch 87 (.leaf 908881588) (.leaf 893947990)) (.branch 89 (.leaf 879287236) (.leaf 864893042)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 850759330) (.branch 92 (.leaf 836880217) (.leaf 823250004))) (.branch 95 (.branch 94 (.leaf 809863172) (.leaf 796714372)) (.branch 96 (.leaf 783798421) (.leaf 771110290)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 758645100) (.leaf 746398119)) (.branch 100 (.leaf 734364751) (.leaf 722540533))) (.branch 103 (.branch 102 (.leaf 710921130) (.leaf 699502328)) (.branch 104 (.leaf 688280031) (.leaf 677250258))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 666409133) (.leaf 655752887)) (.branch 108 (.leaf 645277851) (.leaf 634980453))) (.branch 111 (.branch 110 (.leaf 624857213) (.leaf 614904742)) (.branch 112 (.leaf 605119737) (.leaf 595498979)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 586039329) (.leaf 576737726)) (.branch 116 (.leaf 567591184) (.leaf 558596788))) (.branch 119 (.branch 118 (.leaf 549751695) (.leaf 541053129)) (.branch 120 (.leaf 532498379) (.leaf 524084797)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 69).prefactor = (1027640893163281/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 69).cutoff/(generalMeanRows 69).c)).2 =
    (482894876100857/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 69).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 69).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 69).q*(generalMeanRows 69).c/2-2 = (49/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable011.value]
    have hcontinuation : (generalMeanRows 69).q*(generalMeanRows 69).cutoff/2-2 = (248/111:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable041.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 69).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 69

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 69).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 69).criticalRate j.val*(generalMeanRows 69).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 69).c*(generalMeanRows 69).criticalPoint j.val)).2-
      (generalMeanRows 69).J/2-(generalMeanRows 69).error (generalMeanGrid j.val)+
      (generalMeanRows 69).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 69).c)).2-
      (generalMeanRows 69).J/2-(generalMeanRows 69).error 4 := by
  have he : (generalMeanRows 69).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 69) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 69)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0069

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock00 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 0 i) := by
  fin_cases i
  · exact EntropyRow0000.numerical
  · exact EntropyRow0001.numerical
  · exact EntropyRow0002.numerical
  · exact EntropyRow0003.numerical
  · exact EntropyRow0004.numerical
  · exact EntropyRow0005.numerical
  · exact EntropyRow0006.numerical
  · exact EntropyRow0007.numerical
  · exact EntropyRow0008.numerical
  · exact EntropyRow0009.numerical
  · exact EntropyRow0010.numerical
  · exact EntropyRow0011.numerical
  · exact EntropyRow0012.numerical
  · exact EntropyRow0013.numerical
  · exact EntropyRow0014.numerical
  · exact EntropyRow0015.numerical
  · exact EntropyRow0016.numerical
  · exact EntropyRow0017.numerical
  · exact EntropyRow0018.numerical
  · exact EntropyRow0019.numerical
  · exact EntropyRow0020.numerical
  · exact EntropyRow0021.numerical
  · exact EntropyRow0022.numerical
  · exact EntropyRow0023.numerical
  · exact EntropyRow0024.numerical
  · exact EntropyRow0025.numerical
  · exact EntropyRow0026.numerical
  · exact EntropyRow0027.numerical
  · exact EntropyRow0028.numerical
  · exact EntropyRow0029.numerical
  · exact EntropyRow0030.numerical
  · exact EntropyRow0031.numerical
  · exact EntropyRow0032.numerical
  · exact EntropyRow0033.numerical
  · exact EntropyRow0034.numerical
  · exact EntropyRow0035.numerical
  · exact EntropyRow0036.numerical
  · exact EntropyRow0037.numerical
  · exact EntropyRow0038.numerical
  · exact EntropyRow0039.numerical
  · exact EntropyRow0040.numerical
  · exact EntropyRow0041.numerical
  · exact EntropyRow0042.numerical
  · exact EntropyRow0043.numerical
  · exact EntropyRow0044.numerical
  · exact EntropyRow0045.numerical
  · exact EntropyRow0046.numerical
  · exact EntropyRow0047.numerical
  · exact EntropyRow0048.numerical
  · exact EntropyRow0049.numerical
  · exact EntropyRow0050.numerical
  · exact EntropyRow0051.numerical
  · exact EntropyRow0052.numerical
  · exact EntropyRow0053.numerical
  · exact EntropyRow0054.numerical
  · exact EntropyRow0055.numerical
  · exact EntropyRow0056.numerical
  · exact EntropyRow0057.numerical
  · exact EntropyRow0058.numerical
  · exact EntropyRow0059.numerical
  · exact EntropyRow0060.numerical
  · exact EntropyRow0061.numerical
  · exact EntropyRow0062.numerical
  · exact EntropyRow0063.numerical
  · exact EntropyRow0064.numerical
  · exact EntropyRow0065.numerical
  · exact EntropyRow0066.numerical
  · exact EntropyRow0067.numerical
  · exact EntropyRow0068.numerical
  · exact EntropyRow0069.numerical
end SingularValueBounds.KL.Certificates
