import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block04
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block05
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block10
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block11
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block12
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block13
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block14
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block15
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 700. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0700
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4967463919) (.branch 2 (.leaf 4796930542) (.leaf 4633937862))) (.branch 5 (.branch 4 (.leaf 4478062559) (.leaf 4328910951)) (.branch 6 (.leaf 4186116410) (.leaf 4049337056)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3918253689) (.leaf 3792567945)) (.branch 10 (.leaf 3672000623) (.leaf 3556290187))) (.branch 13 (.branch 12 (.leaf 3445191408) (.leaf 3338474132)) (.branch 14 (.leaf 3235922162) (.leaf 3137332242))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3042513126) (.branch 17 (.leaf 2951284734) (.leaf 2863477372))) (.branch 20 (.branch 19 (.leaf 2778931023) (.leaf 2697494692)) (.branch 21 (.leaf 2619025805) (.leaf 2543389657)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2470458898) (.leaf 2400113063)) (.branch 25 (.leaf 2332238138) (.leaf 2266726151))) (.branch 28 (.branch 27 (.leaf 2203474803) (.leaf 2142387115)) (.branch 29 (.leaf 2083371112) (.leaf 2026339516)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1971209473) (.branch 32 (.leaf 1917902287) (.leaf 1866343182))) (.branch 35 (.branch 34 (.leaf 1816461073) (.leaf 1768188359)) (.branch 36 (.leaf 1721460717) (.leaf 1676216926)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1632398691) (.leaf 1589950478)) (.branch 40 (.leaf 1548819366) (.leaf 1508954906))) (.branch 43 (.branch 42 (.leaf 1470308982) (.leaf 1432835691)) (.branch 44 (.leaf 1396491221) (.leaf 1361233745))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1327023312) (.branch 47 (.leaf 1293821754) (.leaf 1261592590))) (.branch 50 (.branch 49 (.leaf 1230300940) (.leaf 1199913444)) (.branch 51 (.leaf 1170398187) (.leaf 1141724621)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1113863502) (.leaf 1086786822)) (.branch 55 (.leaf 1060467747) (.leaf 1034880565))) (.branch 58 (.branch 57 (.leaf 1010000624) (.leaf 985804286)) (.branch 59 (.leaf 962268876) (.leaf 939372635))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 917094680) (.branch 62 (.leaf 895414959) (.leaf 874314213))) (.branch 65 (.branch 64 (.leaf 853773941) (.leaf 833776361)) (.branch 66 (.leaf 814304381) (.leaf 795341564)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 776872102) (.leaf 758880782)) (.branch 70 (.leaf 741352966) (.leaf 724274560))) (.branch 73 (.branch 72 (.leaf 707631993) (.leaf 691412190)) (.branch 74 (.leaf 675602556) (.leaf 660190950))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 645165670) (.branch 77 (.leaf 630515429) (.leaf 616229341))) (.branch 80 (.branch 79 (.leaf 602296903) (.leaf 588707978)) (.branch 81 (.leaf 575452781) (.leaf 562521863)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 549906099) (.leaf 537596673)) (.branch 85 (.leaf 525585065) (.leaf 513863040))) (.branch 88 (.branch 87 (.leaf 502422637) (.leaf 491256159)) (.branch 89 (.leaf 480356158) (.leaf 469715429)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 459327000) (.branch 92 (.leaf 449184124) (.leaf 439280265))) (.branch 95 (.branch 94 (.leaf 429609097) (.leaf 420164491)) (.branch 96 (.leaf 410940510) (.leaf 401931400)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 393131584) (.leaf 384535658)) (.branch 100 (.leaf 376138378) (.leaf 367934661))) (.branch 103 (.branch 102 (.leaf 359919577) (.leaf 352088339)) (.branch 104 (.leaf 344436306) (.leaf 336958972))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 329651961) (.leaf 322511026)) (.branch 108 (.leaf 315532042) (.leaf 308711003))) (.branch 111 (.branch 110 (.leaf 302044016) (.leaf 295527300)) (.branch 112 (.leaf 289157179) (.leaf 282930081)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 276842533) (.leaf 270891159)) (.branch 116 (.leaf 265072674) (.leaf 259383887))) (.branch 119 (.branch 118 (.leaf 253821690) (.leaf 248383061)) (.branch 120 (.leaf 243065059) (.leaf 237864823)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 700).prefactor = (2325016812613957/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 700).cutoff/(generalMeanRows 700).c)).2 =
    (7063144045663/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 700).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 700).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 700).q*(generalMeanRows 700).c/2-2 = (6659/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable215.value]
    have hcontinuation : (generalMeanRows 700).q*(generalMeanRows 700).cutoff/2-2 = (3932/1935:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable229.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 700).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 700

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 700).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 700).criticalRate j.val*(generalMeanRows 700).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 700).c*(generalMeanRows 700).criticalPoint j.val)).2-
      (generalMeanRows 700).J/2-(generalMeanRows 700).error (generalMeanGrid j.val)+
      (generalMeanRows 700).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 700).c)).2-
      (generalMeanRows 700).J/2-(generalMeanRows 700).error 4 := by
  have he : (generalMeanRows 700).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 700) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 700)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0700

/-! Kernel-checked entropy margins for general spectral rectangle 701. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0701
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5321682996) (.branch 2 (.leaf 5154893043) (.leaf 4995339930))) (.branch 5 (.branch 4 (.leaf 4842612426) (.leaf 4696328394)) (.branch 6 (.leaf 4556132253) (.leaf 4421692705)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4292700708) (.leaf 4168867650)) (.branch 10 (.leaf 4049923710) (.leaf 3935616381))) (.branch 13 (.branch 12 (.leaf 3825709132) (.leaf 3719980192)) (.branch 14 (.leaf 3618221452) (.leaf 3520237459))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3425844506) (.branch 17 (.leaf 3334869789) (.leaf 3247150649))) (.branch 20 (.branch 19 (.leaf 3162533867) (.leaf 3080875020)) (.branch 21 (.leaf 3002037888) (.leaf 2925893911)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2852321683) (.leaf 2781206489)) (.branch 25 (.leaf 2712439876) (.leaf 2645919252))) (.branch 28 (.branch 27 (.leaf 2581547521) (.leaf 2519232741)) (.branch 29 (.leaf 2458887805) (.leaf 2400430146)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2343781466) (.branch 32 (.leaf 2288867477) (.leaf 2235617664))) (.branch 35 (.branch 34 (.leaf 2183965063) (.leaf 2133846055)) (.branch 36 (.leaf 2085200172) (.leaf 2037969915)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1992100586) (.leaf 1947540130)) (.branch 40 (.leaf 1904238986) (.leaf 1862149949))) (.branch 43 (.branch 42 (.leaf 1821228038) (.leaf 1781430379)) (.branch 44 (.leaf 1742716081) (.leaf 1705046140))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1668383329) (.branch 47 (.leaf 1632692106) (.leaf 1597938525))) (.branch 50 (.branch 49 (.leaf 1564090152) (.leaf 1531115987)) (.branch 51 (.leaf 1498986386) (.leaf 1467672993)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1437148676) (.leaf 1407387460)) (.branch 55 (.leaf 1378364473) (.leaf 1350055887))) (.branch 58 (.branch 57 (.leaf 1322438868) (.leaf 1295491524)) (.branch 59 (.leaf 1269192863) (.leaf 1243522744))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1218461837) (.branch 62 (.leaf 1193991585) (.leaf 1170094166))) (.branch 65 (.branch 64 (.leaf 1146752457) (.leaf 1123950003)) (.branch 66 (.leaf 1101670980) (.leaf 1079900174)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1058622945) (.leaf 1037825202)) (.branch 70 (.leaf 1017493381) (.leaf 997614419))) (.branch 73 (.branch 72 (.leaf 978175727) (.leaf 959165178)) (.branch 74 (.leaf 940571076) (.leaf 922382143))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 904587500) (.branch 77 (.leaf 887176648) (.leaf 870139451))) (.branch 80 (.branch 79 (.leaf 853466121) (.leaf 837147204)) (.branch 81 (.leaf 821173565) (.leaf 805536373)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 790227090) (.leaf 775237459)) (.branch 85 (.leaf 760559489) (.leaf 746185450))) (.branch 88 (.branch 87 (.leaf 732107856) (.leaf 718319459)) (.branch 89 (.leaf 704813238) (.leaf 691582390)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 678620323) (.branch 92 (.leaf 665920645) (.leaf 653477156))) (.branch 95 (.branch 94 (.leaf 641283844) (.leaf 629334876)) (.branch 96 (.leaf 617624589) (.leaf 606147487)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 594898232) (.leaf 583871639)) (.branch 100 (.leaf 573062672) (.leaf 562466436))) (.branch 103 (.branch 102 (.leaf 552078174) (.leaf 541893259)) (.branch 104 (.leaf 531907194) (.leaf 522115602))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 512514227) (.leaf 503098926)) (.branch 108 (.leaf 493865665) (.leaf 484810520))) (.branch 111 (.branch 110 (.leaf 475929666) (.leaf 467219381)) (.branch 112 (.leaf 458676037) (.leaf 450296099)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 442076124) (.leaf 434012752)) (.branch 116 (.leaf 426102712) (.leaf 418342810))) (.branch 119 (.branch 118 (.leaf 410729934) (.leaf 403261047)) (.branch 120 (.leaf 395933186) (.leaf 388743460)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 701).prefactor = (4541776302932597/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 701).cutoff/(generalMeanRows 701).c)).2 =
    (205105195865993/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 701).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 701).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 701).q*(generalMeanRows 701).c/2-2 = (353/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable084.value]
    have hcontinuation : (generalMeanRows 701).q*(generalMeanRows 701).cutoff/2-2 = (1964/945:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable237.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 701).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 701

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 701).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 701).criticalRate j.val*(generalMeanRows 701).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 701).c*(generalMeanRows 701).criticalPoint j.val)).2-
      (generalMeanRows 701).J/2-(generalMeanRows 701).error (generalMeanGrid j.val)+
      (generalMeanRows 701).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 701).c)).2-
      (generalMeanRows 701).J/2-(generalMeanRows 701).error 4 := by
  have he : (generalMeanRows 701).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 701) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 701)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0701

/-! Kernel-checked entropy margins for general spectral rectangle 702. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0702
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4883398541) (.branch 2 (.leaf 4713380662) (.leaf 4550939055))) (.branch 5 (.branch 4 (.leaf 4395646753) (.leaf 4247106727)) (.branch 6 (.leaf 4104949277) (.leaf 3968829700)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3838426209) (.leaf 3713438062)) (.branch 10 (.leaf 3593583876) (.leaf 3478600115))) (.branch 13 (.branch 12 (.leaf 3368239715) (.leaf 3262270837)) (.branch 14 (.leaf 3160475741) (.leaf 3062649756))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2968600341) (.branch 17 (.leaf 2878146229) (.leaf 2791116641))) (.branch 20 (.branch 19 (.leaf 2707350565) (.leaf 2626696100)) (.branch 21 (.leaf 2549009843) (.leaf 2474156330)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2402007521) (.leaf 2332442325)) (.branch 25 (.leaf 2265346152) (.leaf 2200610512))) (.branch 28 (.branch 27 (.leaf 2138132631) (.leaf 2077815105)) (.branch 29 (.leaf 2019565567) (.leaf 1963296392)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1908924407) (.branch 32 (.leaf 1856370631) (.leaf 1805560034))) (.branch 35 (.branch 34 (.leaf 1756421302) (.leaf 1708886626)) (.branch 36 (.leaf 1662891503) (.leaf 1618374549)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1575277327) (.leaf 1533544177)) (.branch 40 (.leaf 1493122069) (.leaf 1453960458))) (.branch 43 (.branch 42 (.leaf 1416011147) (.leaf 1379228162)) (.branch 44 (.leaf 1343567635) (.leaf 1308987689))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1275448336) (.branch 47 (.leaf 1242911376) (.leaf 1211340305))) (.branch 50 (.branch 49 (.leaf 1180700229) (.leaf 1150957779)) (.branch 51 (.leaf 1122081036) (.leaf 1094039455)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1066803799) (.leaf 1040346070)) (.branch 55 (.leaf 1014639451) (.leaf 989658249))) (.branch 58 (.branch 57 (.leaf 965377833) (.leaf 941774591)) (.branch 59 (.leaf 918825876) (.leaf 896509960))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 874805991) (.branch 62 (.leaf 853693952) (.leaf 833154620))) (.branch 65 (.branch 64 (.leaf 813169530) (.leaf 793720942)) (.branch 66 (.leaf 774791801) (.leaf 756365714)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 738426913) (.leaf 720960229)) (.branch 70 (.leaf 703951067) (.leaf 687385378))) (.branch 73 (.branch 72 (.leaf 671249634) (.leaf 655530808)) (.branch 74 (.leaf 640216348) (.leaf 625294162))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 610752591) (.branch 77 (.leaf 596580397) (.leaf 582766739))) (.branch 80 (.branch 79 (.leaf 569301160) (.leaf 556173572)) (.branch 81 (.leaf 543374236) (.leaf 530893749)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 518723034) (.leaf 506853320)) (.branch 85 (.leaf 495276135) (.leaf 483983292))) (.branch 88 (.branch 87 (.leaf 472966875) (.leaf 462219233)) (.branch 89 (.leaf 451732965) (.leaf 441500913)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 431516151) (.branch 92 (.leaf 421771975) (.leaf 412261898))) (.branch 95 (.branch 94 (.leaf 402979639) (.leaf 393919113)) (.branch 96 (.leaf 385074430) (.leaf 376439879)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 368009930) (.leaf 359779222)) (.branch 100 (.leaf 351742556) (.leaf 343894894))) (.branch 103 (.branch 102 (.leaf 336231348) (.leaf 328747178)) (.branch 104 (.leaf 321437783) (.leaf 314298702))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 307325603) (.leaf 300514282)) (.branch 108 (.leaf 293860655) (.leaf 287360760))) (.branch 111 (.branch 110 (.leaf 281010747) (.leaf 274806874)) (.branch 112 (.leaf 268745510) (.leaf 262823123)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 257036282) (.leaf 251381653)) (.branch 116 (.leaf 245855991) (.leaf 240456146))) (.branch 119 (.branch 118 (.leaf 235179050) (.leaf 230021723)) (.branch 120 (.leaf 224981263) (.leaf 220054848)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 702).prefactor = (467701507936771/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 702).cutoff/(generalMeanRows 702).c)).2 =
    (175714472425497/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 702).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 702).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 702).q*(generalMeanRows 702).c/2-2 = (273/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable221.value]
    have hcontinuation : (generalMeanRows 702).q*(generalMeanRows 702).cutoff/2-2 = (15814/7697:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable236.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 702).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 702

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 702).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 702).criticalRate j.val*(generalMeanRows 702).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 702).c*(generalMeanRows 702).criticalPoint j.val)).2-
      (generalMeanRows 702).J/2-(generalMeanRows 702).error (generalMeanGrid j.val)+
      (generalMeanRows 702).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 702).c)).2-
      (generalMeanRows 702).J/2-(generalMeanRows 702).error 4 := by
  have he : (generalMeanRows 702).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 702) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 702)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0702

/-! Kernel-checked entropy margins for general spectral rectangle 703. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0703
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5024679330) (.branch 2 (.leaf 4854294101) (.leaf 4691454743))) (.branch 5 (.branch 4 (.leaf 4535734665) (.leaf 4386737284)) (.branch 6 (.leaf 4244093399) (.leaf 4107458866)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3976512497) (.leaf 3850954188)) (.branch 10 (.leaf 3730503234) (.leaf 3614896803))) (.branch 13 (.branch 12 (.leaf 3503888560) (.leaf 3397247418)) (.branch 14 (.leaf 3294756405) (.leaf 3196211632))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3101421352) (.branch 17 (.leaf 3010205098) (.leaf 2922392895))) (.branch 20 (.branch 19 (.leaf 2837824543) (.leaf 2756348947)) (.branch 21 (.leaf 2677823512) (.leaf 2602113578)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2529091905) (.leaf 2458638192)) (.branch 25 (.leaf 2390638636) (.leaf 2324985521))) (.branch 28 (.branch 27 (.leaf 2261576839) (.leaf 2200315939)) (.branch 29 (.leaf 2141111200) (.leaf 2083875722)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2028527052) (.branch 32 (.leaf 1974986912) (.leaf 1923180958))) (.branch 35 (.branch 34 (.leaf 1873038550) (.leaf 1824492539)) (.branch 36 (.leaf 1777479065) (.leaf 1731937372)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1687809633) (.leaf 1645040787)) (.branch 40 (.leaf 1603578383) (.leaf 1563372440))) (.branch 43 (.branch 42 (.leaf 1524375310) (.leaf 1486541551)) (.branch 44 (.leaf 1449827813) (.leaf 1414192719))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1379596766) (.branch 47 (.leaf 1346002224) (.leaf 1313373045))) (.branch 50 (.branch 49 (.leaf 1281674772) (.leaf 1250874464)) (.branch 51 (.leaf 1220940608) (.leaf 1191843057)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1163552952) (.leaf 1136042666)) (.branch 55 (.leaf 1109285733) (.leaf 1083256798))) (.branch 58 (.branch 57 (.leaf 1057931559) (.leaf 1033286718)) (.branch 59 (.leaf 1009299925) (.leaf 985949744))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 963215597) (.branch 62 (.leaf 941077731) (.leaf 919517176))) (.branch 65 (.branch 64 (.leaf 898515710) (.leaf 878055821)) (.branch 66 (.leaf 858120674) (.leaf 838694085)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 819760485) (.leaf 801304894)) (.branch 70 (.leaf 783312895) (.leaf 765770608))) (.branch 73 (.branch 72 (.leaf 748664668) (.leaf 731982198)) (.branch 74 (.leaf 715710790) (.leaf 699838486))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 684353753) (.branch 77 (.leaf 669245472) (.leaf 654502913))) (.branch 80 (.branch 79 (.leaf 640115725) (.leaf 626073912)) (.branch 81 (.leaf 612367827) (.leaf 598988151)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 585925881) (.leaf 573172317)) (.branch 85 (.leaf 560719051) (.leaf 548557954))) (.branch 88 (.branch 87 (.leaf 536681163) (.leaf 525081073)) (.branch 89 (.leaf 513750326) (.leaf 502681799)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 491868599) (.branch 92 (.leaf 481304049) (.leaf 470981684))) (.branch 95 (.branch 94 (.leaf 460895241) (.leaf 451038650)) (.branch 96 (.leaf 441406029) (.leaf 431991676)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 422790060) (.leaf 413795819)) (.branch 100 (.leaf 405003752) (.leaf 396408809))) (.branch 103 (.branch 102 (.leaf 388006094) (.leaf 379790850)) (.branch 104 (.leaf 371758461) (.leaf 363904445))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 356224447) (.leaf 348714237)) (.branch 108 (.leaf 341369706) (.leaf 334186860))) (.branch 111 (.branch 110 (.leaf 327161815) (.leaf 320290799)) (.branch 112 (.leaf 313570141) (.leaf 306996273)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 300565724) (.leaf 294275115)) (.branch 116 (.leaf 288121162) (.leaf 282100666))) (.branch 119 (.branch 118 (.leaf 276210515) (.leaf 270447680)) (.branch 120 (.leaf 264809211) (.leaf 259292236)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 703).prefactor = (1168412503616547/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 703).cutoff/(generalMeanRows 703).c)).2 =
    (368878426258927/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 703).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 703).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 703).q*(generalMeanRows 703).c/2-2 = (6493/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable213.value]
    have hcontinuation : (generalMeanRows 703).q*(generalMeanRows 703).cutoff/2-2 = (31714/15351:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable238.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 703).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 703

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 703).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 703).criticalRate j.val*(generalMeanRows 703).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 703).c*(generalMeanRows 703).criticalPoint j.val)).2-
      (generalMeanRows 703).J/2-(generalMeanRows 703).error (generalMeanGrid j.val)+
      (generalMeanRows 703).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 703).c)).2-
      (generalMeanRows 703).J/2-(generalMeanRows 703).error 4 := by
  have he : (generalMeanRows 703).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 703) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 703)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0703

/-! Kernel-checked entropy margins for general spectral rectangle 704. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0704
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4960713887) (.branch 2 (.leaf 4790207428) (.leaf 4627282071))) (.branch 5 (.branch 4 (.leaf 4471509472) (.leaf 4322491386)) (.branch 6 (.leaf 4179857044) (.leaf 4043260808)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3912380076) (.leaf 3786913398)) (.branch 10 (.leaf 3666578789) (.leaf 3551112194))) (.branch 13 (.branch 12 (.leaf 3440266116) (.leaf 3333808357)) (.branch 14 (.leaf 3231520885) (.leaf 3133198795))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3038649372) (.branch 17 (.leaf 2947691218) (.leaf 2860153472))) (.branch 20 (.branch 19 (.leaf 2775875079) (.leaf 2694704130)) (.branch 21 (.leaf 2616497245) (.leaf 2541119013)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2468441475) (.leaf 2398343635)) (.branch 25 (.leaf 2330711027) (.leaf 2265435295))) (.branch 28 (.branch 27 (.leaf 2202413820) (.leaf 2141549360)) (.branch 29 (.leaf 2082749726) (.leaf 2025927477)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1970999633) (.branch 32 (.leaf 1917887415) (.leaf 1866515995))) (.branch 35 (.branch 34 (.leaf 1816814267) (.leaf 1768714634)) (.branch 36 (.leaf 1722152807) (.leaf 1677067616)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1633400838) (.leaf 1591097026)) (.branch 40 (.leaf 1550103365) (.leaf 1510369518))) (.branch 43 (.branch 42 (.leaf 1471847499) (.leaf 1434491541)) (.branch 44 (.leaf 1398257977) (.leaf 1363105130))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1328993209) (.branch 47 (.leaf 1295884206) (.leaf 1263741804))) (.branch 50 (.branch 49 (.leaf 1232531293) (.leaf 1202219482)) (.branch 51 (.leaf 1172774626) (.leaf 1144166350)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1116365580) (.leaf 1089344478)) (.branch 55 (.leaf 1063076382) (.leaf 1037535744))) (.branch 58 (.branch 57 (.leaf 1012698081) (.leaf 988539918)) (.branch 59 (.leaf 965038741) (.leaf 942172951))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 919921819) (.branch 62 (.leaf 898265447) (.leaf 877184724))) (.branch 65 (.branch 64 (.leaf 856661296) (.leaf 836677523)) (.branch 66 (.leaf 817216452) (.leaf 798261782)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 779797835) (.leaf 761809528)) (.branch 70 (.leaf 744282345) (.leaf 727202313))) (.branch 73 (.branch 72 (.leaf 710555977) (.leaf 694330377)) (.branch 74 (.leaf 678513026) (.leaf 663091889))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 648055365) (.branch 77 (.leaf 633392266) (.leaf 619091802))) (.branch 80 (.branch 79 (.leaf 605143559) (.leaf 591537491)) (.branch 81 (.leaf 578263896) (.leaf 565313407)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 552676977) (.leaf 540345865)) (.branch 85 (.leaf 528311624) (.leaf 516566088))) (.branch 88 (.branch 87 (.leaf 505101364) (.leaf 493909815)) (.branch 89 (.leaf 482984057) (.leaf 472316942)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 461901554) (.branch 92 (.leaf 451731198) (.leaf 441799391))) (.branch 95 (.branch 94 (.leaf 432099854) (.leaf 422626504)) (.branch 96 (.leaf 413373449) (.leaf 404334976)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 395505548) (.leaf 386879799)) (.branch 100 (.leaf 378452521) (.leaf 370218666))) (.branch 103 (.branch 102 (.leaf 362173334) (.leaf 354311771)) (.branch 104 (.leaf 346629365) (.leaf 339121636))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 331784235) (.leaf 324612939)) (.branch 108 (.leaf 317603647) (.leaf 310752374))) (.branch 111 (.branch 110 (.leaf 304055248) (.leaf 297508507)) (.branch 112 (.leaf 291108493) (.leaf 284851650)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 278734523) (.leaf 272753749)) (.branch 116 (.leaf 266906058) (.leaf 261188271))) (.branch 119 (.branch 118 (.leaf 255597293) (.leaf 250130112)) (.branch 120 (.leaf 244783798) (.leaf 239555499)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 704).prefactor = (1172541045588821/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 704).cutoff/(generalMeanRows 704).c)).2 =
    (90381362988417/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 704).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 704).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 704).q*(generalMeanRows 704).c/2-2 = (6659/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable215.value]
    have hcontinuation : (generalMeanRows 704).q*(generalMeanRows 704).cutoff/2-2 = (31714/15351:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable238.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 704).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 704

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 704).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 704).criticalRate j.val*(generalMeanRows 704).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 704).c*(generalMeanRows 704).criticalPoint j.val)).2-
      (generalMeanRows 704).J/2-(generalMeanRows 704).error (generalMeanGrid j.val)+
      (generalMeanRows 704).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 704).c)).2-
      (generalMeanRows 704).J/2-(generalMeanRows 704).error 4 := by
  have he : (generalMeanRows 704).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 704) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 704)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0704

/-! Kernel-checked entropy margins for general spectral rectangle 705. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0705
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4980910815) (.branch 2 (.leaf 4809774529) (.leaf 4646233482))) (.branch 5 (.branch 4 (.leaf 4489859456) (.leaf 4340254288)) (.branch 6 (.leaf 4197047249) (.leaf 4059892704)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3928468014) (.leaf 3802471667)) (.branch 10 (.leaf 3681621581) (.leaf 3565653584))) (.branch 13 (.branch 12 (.leaf 3454320035) (.leaf 3347388573)) (.branch 14 (.leaf 3244640983) (.leaf 3145872165))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3050889191) (.branch 17 (.leaf 2959510440) (.leaf 2871564818))) (.branch 20 (.branch 19 (.leaf 2786891027) (.leaf 2705336907)) (.branch 21 (.leaf 2626758824) (.leaf 2551021107)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2477995529) (.leaf 2407560830)) (.branch 25 (.leaf 2339602275) (.leaf 2274011240))) (.branch 28 (.branch 27 (.leaf 2210684833) (.leaf 2149525546)) (.branch 29 (.leaf 2090440922) (.leaf 2033343254)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1978149297) (.branch 32 (.leaf 1924780012) (.leaf 1873160313))) (.branch 35 (.branch 34 (.leaf 1823218840) (.leaf 1774887746)) (.branch 36 (.leaf 1728102494) (.leaf 1682801672)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1638926818) (.leaf 1596422254)) (.branch 40 (.leaf 1555234934) (.leaf 1515314299))) (.branch 43 (.branch 42 (.leaf 1476612143) (.leaf 1439082484)) (.branch 44 (.leaf 1402681449) (.leaf 1367367155))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1333099613) (.branch 47 (.leaf 1299840620) (.leaf 1267553672))) (.branch 50 (.branch 49 (.leaf 1236203875) (.leaf 1205757860)) (.branch 51 (.leaf 1176183708) (.leaf 1147450874)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1119530121) (.leaf 1092393453)) (.branch 55 (.leaf 1066014051) (.leaf 1040366221))) (.branch 58 (.branch 57 (.leaf 1015425333) (.leaf 991167770)) (.branch 59 (.leaf 967570884) (.leaf 944612942))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 922273088) (.branch 62 (.leaf 900531300) (.leaf 879368349))) (.branch 65 (.branch 64 (.leaf 858765763) (.leaf 838705791)) (.branch 66 (.leaf 819171371) (.leaf 800146099)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 781614194) (.leaf 763560477)) (.branch 70 (.leaf 745970337) (.leaf 728829709))) (.branch 73 (.branch 72 (.leaf 712125052) (.leaf 695843320)) (.branch 74 (.leaf 679971944) (.leaf 664498810))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 649412242) (.branch 77 (.leaf 634700978) (.leaf 620354156))) (.branch 80 (.branch 79 (.leaf 606361296) (.leaf 592712283)) (.branch 81 (.leaf 579397354) (.leaf 566407081)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 553732357) (.leaf 541364385)) (.branch 85 (.leaf 529294663) (.leaf 517514973))) (.branch 88 (.branch 87 (.leaf 506017371) (.leaf 494794170)) (.branch 89 (.leaf 483837941) (.leaf 473141490)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 462697857) (.branch 92 (.leaf 452500306) (.leaf 442542313))) (.branch 95 (.branch 94 (.leaf 432817560) (.leaf 423319929)) (.branch 96 (.leaf 414043489) (.leaf 404982494)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 396131375) (.leaf 387484732)) (.branch 100 (.leaf 379037328) (.leaf 370784083))) (.branch 103 (.branch 102 (.leaf 362720072) (.leaf 354840512)) (.branch 104 (.leaf 347140764) (.leaf 339616324))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 332262819) (.leaf 325076002)) (.branch 108 (.leaf 318051749) (.leaf 311186055))) (.branch 111 (.branch 110 (.leaf 304475026) (.leaf 297914880)) (.branch 112 (.leaf 291501941) (.leaf 285232635)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 279103488) (.leaf 273111120)) (.branch 116 (.leaf 267252247) (.leaf 261523671))) (.branch 119 (.branch 118 (.leaf 255922284) (.leaf 250445060)) (.branch 120 (.leaf 245089054) (.leaf 239851401)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 705).prefactor = (938736304825981/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 705).cutoff/(generalMeanRows 705).c)).2 =
    (358728247332607/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 705).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 705).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 705).q*(generalMeanRows 705).c/2-2 = (6659/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable215.value]
    have hcontinuation : (generalMeanRows 705).q*(generalMeanRows 705).cutoff/2-2 = (15814/7697:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable236.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 705).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 705

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 705).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 705).criticalRate j.val*(generalMeanRows 705).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 705).c*(generalMeanRows 705).criticalPoint j.val)).2-
      (generalMeanRows 705).J/2-(generalMeanRows 705).error (generalMeanGrid j.val)+
      (generalMeanRows 705).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 705).c)).2-
      (generalMeanRows 705).J/2-(generalMeanRows 705).error 4 := by
  have he : (generalMeanRows 705).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 705) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 705)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0705

/-! Kernel-checked entropy margins for general spectral rectangle 706. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0706
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4918264328) (.branch 2 (.leaf 4747032579) (.leaf 4583431196))) (.branch 5 (.branch 4 (.leaf 4427030160) (.leaf 4277429610)) (.branch 6 (.leaf 4134257204) (.leaf 3997165780)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3865831253) (.leaf 3739950733)) (.branch 10 (.leaf 3619240829) (.leaf 3503436124))) (.branch 13 (.branch 12 (.leaf 3392287789) (.leaf 3285562329)) (.branch 14 (.leaf 3183040451) (.leaf 3084516022))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2989795127) (.branch 17 (.leaf 2898695204) (.leaf 2811044254))) (.branch 20 (.branch 19 (.leaf 2726680118) (.leaf 2645449808)) (.branch 21 (.leaf 2567208897) (.leaf 2491820955)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2419157029) (.leaf 2349095161)) (.branch 25 (.leaf 2281519945) (.leaf 2216322114))) (.branch 28 (.branch 27 (.leaf 2153398163) (.leaf 2092649990)) (.branch 29 (.leaf 2033984571) (.leaf 1977313653)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1922553471) (.branch 32 (.leaf 1869624480) (.leaf 1818451112))) (.branch 35 (.branch 34 (.leaf 1768961546) (.leaf 1721087489)) (.branch 36 (.leaf 1674763976) (.leaf 1629929187)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1586524266) (.leaf 1544493155)) (.branch 40 (.leaf 1503782448) (.leaf 1464341236))) (.branch 43 (.branch 42 (.leaf 1426120980) (.leaf 1389075377)) (.branch 44 (.leaf 1353160246) (.leaf 1318333411))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1284554599) (.branch 47 (.leaf 1251785336) (.leaf 1219988858))) (.branch 50 (.branch 49 (.leaf 1189130023) (.leaf 1159175222)) (.branch 51 (.leaf 1130092309) (.leaf 1101850521)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1074420411) (.leaf 1047773783)) (.branch 55 (.leaf 1021883628) (.leaf 996724068))) (.branch 58 (.branch 57 (.leaf 972270299) (.leaf 948498538)) (.branch 59 (.leaf 925385977) (.leaf 902910733))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 881051805) (.branch 62 (.leaf 859789033) (.leaf 839103057))) (.branch 65 (.branch 64 (.leaf 818975281) (.leaf 799387836)) (.branch 66 (.leaf 780323548) (.leaf 761765905)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 743699027) (.leaf 726107637)) (.branch 70 (.leaf 708977036) (.leaf 692293073))) (.branch 73 (.branch 72 (.leaf 676042126) (.leaf 660211072)) (.branch 74 (.leaf 644787273) (.leaf 629758547))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 615113155) (.branch 77 (.leaf 600839776) (.leaf 586927493))) (.branch 80 (.branch 79 (.leaf 573365775) (.leaf 560144460)) (.branch 81 (.leaf 547253741) (.leaf 534684148)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 522426538) (.leaf 510472078)) (.branch 85 (.leaf 498812237) (.leaf 487438766))) (.branch 88 (.branch 87 (.leaf 476343696) (.leaf 465519320)) (.branch 89 (.leaf 454958183) (.leaf 444653078)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 434597028) (.branch 92 (.leaf 424783282) (.leaf 415205307))) (.branch 95 (.branch 94 (.leaf 405856775) (.leaf 396731560)) (.branch 96 (.leaf 387823729) (.leaf 379127531)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 370637395) (.leaf 362347922)) (.branch 100 (.leaf 354253877) (.leaf 346350186))) (.branch 103 (.branch 102 (.leaf 338631924) (.leaf 331094319)) (.branch 104 (.leaf 323732739) (.leaf 316542687))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 309519803) (.leaf 302659850)) (.branch 108 (.leaf 295958720) (.leaf 289412417))) (.branch 111 (.branch 110 (.leaf 283017067) (.leaf 276768901)) (.branch 112 (.leaf 270664260) (.leaf 264699590)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 258871433) (.leaf 253176431)) (.branch 116 (.leaf 247611319) (.leaf 242172920))) (.branch 119 (.branch 118 (.leaf 236858148) (.leaf 231663999)) (.branch 120 (.leaf 226587552) (.leaf 221625964)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 706).prefactor = (471040735941711/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 706).cutoff/(generalMeanRows 706).c)).2 =
    (175714472425497/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 706).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 706).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 706).q*(generalMeanRows 706).c/2-2 = (273/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable221.value]
    have hcontinuation : (generalMeanRows 706).q*(generalMeanRows 706).cutoff/2-2 = (15814/7697:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable236.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 706).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 706

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 706).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 706).criticalRate j.val*(generalMeanRows 706).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 706).c*(generalMeanRows 706).criticalPoint j.val)).2-
      (generalMeanRows 706).J/2-(generalMeanRows 706).error (generalMeanGrid j.val)+
      (generalMeanRows 706).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 706).c)).2-
      (generalMeanRows 706).J/2-(generalMeanRows 706).error 4 := by
  have he : (generalMeanRows 706).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 706) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 706)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0706

/-! Kernel-checked entropy margins for general spectral rectangle 707. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0707
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5183298886) (.branch 2 (.leaf 5015955615) (.leaf 4855921477))) (.branch 5 (.branch 4 (.leaf 4702782084) (.leaf 4556152307)) (.branch 6 (.leaf 4415673728) (.leaf 4281012351)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4151856562) (.leaf 4027915304)) (.branch 10 (.leaf 3908916419) (.leaf 3794605169))) (.branch 13 (.branch 12 (.leaf 3684742886) (.leaf 3579105756)) (.branch 14 (.leaf 3477483711) (.leaf 3379679420))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3285507371) (.branch 17 (.leaf 3194793028) (.leaf 3107372067))) (.branch 20 (.branch 19 (.leaf 3023089665) (.leaf 2941799857)) (.branch 21 (.leaf 2863364940) (.leaf 2787654922)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2714547017) (.leaf 2643925181)) (.branch 25 (.leaf 2575679676) (.leaf 2509706672))) (.branch 28 (.branch 27 (.leaf 2445907878) (.leaf 2384190196)) (.branch 29 (.leaf 2324465405) (.leaf 2266649860)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2210664222) (.branch 32 (.leaf 2156433196) (.leaf 2103885294))) (.branch 35 (.branch 34 (.leaf 2052952611) (.leaf 2003570620)) (.branch 36 (.leaf 1955677972) (.leaf 1909216317)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1864130134) (.leaf 1820366573)) (.branch 40 (.leaf 1777875303) (.leaf 1736608373))) (.branch 43 (.branch 42 (.leaf 1696520084) (.leaf 1657566861)) (.branch 44 (.leaf 1619707144) (.leaf 1582901274))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1547111393) (.branch 47 (.leaf 1512301350) (.leaf 1478436610))) (.branch 50 (.branch 49 (.leaf 1445484168) (.leaf 1413412471)) (.branch 51 (.leaf 1382191343) (.leaf 1351791913)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1322186550) (.leaf 1293348798)) (.branch 55 (.leaf 1265253320) (.leaf 1237875837))) (.branch 58 (.branch 57 (.leaf 1211193082) (.leaf 1185182745)) (.branch 59 (.leaf 1159823426) (.leaf 1135094594))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1110976543) (.branch 62 (.leaf 1087450352) (.leaf 1064497846))) (.branch 65 (.branch 64 (.leaf 1042101564) (.leaf 1020244724)) (.branch 66 (.leaf 998911190) (.leaf 978085440)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 957752544) (.leaf 937898130)) (.branch 70 (.leaf 918508363) (.leaf 899569917))) (.branch 73 (.branch 72 (.leaf 881069955) (.leaf 862996106)) (.branch 74 (.leaf 845336444) (.leaf 828079468))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 811214085) (.branch 77 (.leaf 794729589) (.leaf 778615648))) (.branch 80 (.branch 79 (.leaf 762862286) (.leaf 747459866)) (.branch 81 (.leaf 732399080) (.leaf 717670931)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 703266723) (.leaf 689178045)) (.branch 85 (.leaf 675396763) (.leaf 661915007))) (.branch 88 (.branch 87 (.leaf 648725160) (.leaf 635819847)) (.branch 89 (.leaf 623191927) (.leaf 610834485)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 598740817) (.branch 92 (.leaf 586904430) (.leaf 575319027))) (.branch 95 (.branch 94 (.leaf 563978504) (.leaf 552876939)) (.branch 96 (.leaf 542008586) (.leaf 531367873)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 520949388) (.leaf 510747878)) (.branch 100 (.leaf 500758242) (.leaf 490975525))) (.branch 103 (.branch 102 (.leaf 481394913) (.leaf 472011727)) (.branch 104 (.leaf 462821421) (.leaf 453819575))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 445001890) (.leaf 436364185)) (.branch 108 (.leaf 427902392) (.leaf 419612556))) (.branch 111 (.branch 110 (.leaf 411490823) (.leaf 403533447)) (.branch 112 (.leaf 395736776) (.leaf 388097257)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 380611430) (.leaf 373275921)) (.branch 116 (.leaf 366087445) (.leaf 359042803))) (.branch 119 (.branch 118 (.leaf 352138874) (.leaf 345372616)) (.branch 120 (.leaf 338741065) (.leaf 332241329)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 707).prefactor = (182942774121029/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 707).cutoff/(generalMeanRows 707).c)).2 =
    (197586257183723/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 707).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 707).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 707).q*(generalMeanRows 707).c/2-2 = (747/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable220.value]
    have hcontinuation : (generalMeanRows 707).q*(generalMeanRows 707).cutoff/2-2 = (1964/945:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable237.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 707).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 707

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 707).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 707).criticalRate j.val*(generalMeanRows 707).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 707).c*(generalMeanRows 707).criticalPoint j.val)).2-
      (generalMeanRows 707).J/2-(generalMeanRows 707).error (generalMeanGrid j.val)+
      (generalMeanRows 707).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 707).c)).2-
      (generalMeanRows 707).J/2-(generalMeanRows 707).error 4 := by
  have he : (generalMeanRows 707).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 707) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 707)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0707

/-! Kernel-checked entropy margins for general spectral rectangle 708. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0708
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5133958328) (.branch 2 (.leaf 4965806371) (.leaf 4805024988))) (.branch 5 (.branch 4 (.leaf 4651196707) (.leaf 4503933509)) (.branch 6 (.leaf 4362874253) (.leaf 4227682382)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4098043868) (.leaf 3973665370)) (.branch 10 (.leaf 3854272577) (.leaf 3739608708))) (.branch 13 (.branch 12 (.leaf 3629433162) (.leaf 3523520292)) (.branch 14 (.leaf 3421658288) (.leaf 3323648164))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3229302833) (.branch 17 (.leaf 3138446264) (.leaf 3050912703))) (.branch 20 (.branch 19 (.leaf 2966545969) (.leaf 2885198798)) (.branch 21 (.leaf 2806732248) (.leaf 2731015142)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2657923566) (.leaf 2587340391)) (.branch 25 (.leaf 2519154847) (.leaf 2453262112))) (.branch 28 (.branch 27 (.leaf 2389562947) (.leaf 2327963346)) (.branch 29 (.leaf 2268374214) (.leaf 2210711075)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2154893785) (.branch 32 (.leaf 2100846282) (.leaf 2048496340))) (.branch 35 (.branch 34 (.leaf 1997775348) (.leaf 1948618096)) (.branch 36 (.leaf 1900962583) (.leaf 1854749831)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1809923717) (.leaf 1766430810)) (.branch 40 (.leaf 1724220222) (.leaf 1683243468))) (.branch 43 (.branch 42 (.leaf 1643454332) (.leaf 1604808745)) (.branch 44 (.leaf 1567264668) (.leaf 1530781986))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1495322399) (.branch 47 (.leaf 1460849332) (.leaf 1427327842))) (.branch 50 (.branch 49 (.leaf 1394724531) (.leaf 1363007468)) (.branch 51 (.leaf 1332146114) (.leaf 1302111248)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1272874901) (.leaf 1244410295)) (.branch 55 (.leaf 1216691780) (.leaf 1189694778))) (.branch 58 (.branch 57 (.leaf 1163395732) (.leaf 1137772056)) (.branch 59 (.leaf 1112802082) (.leaf 1088465024))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1064740927) (.branch 62 (.leaf 1041610633) (.leaf 1019055740))) (.branch 65 (.branch 64 (.leaf 997058566) (.leaf 975602119)) (.branch 66 (.leaf 954670058) (.leaf 934246670)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 914316835) (.leaf 894866002)) (.branch 70 (.leaf 875880163) (.leaf 857345827))) (.branch 73 (.branch 72 (.leaf 839249999) (.leaf 821580153)) (.branch 74 (.leaf 804324218) (.leaf 787470553))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 771007930) (.branch 77 (.leaf 754925514) (.leaf 739212850))) (.branch 80 (.branch 79 (.leaf 723859843) (.leaf 708856745)) (.branch 81 (.leaf 694194138) (.leaf 679862922)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 665854301) (.leaf 652159772)) (.branch 85 (.leaf 638771109) (.leaf 625680357))) (.branch 88 (.branch 87 (.leaf 612879815) (.leaf 600362033)) (.branch 89 (.leaf 588119795) (.leaf 576146112)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 564434218) (.branch 92 (.leaf 552977552) (.leaf 541769758))) (.branch 95 (.branch 94 (.leaf 530804674) (.leaf 520076323)) (.branch 96 (.leaf 509578911) (.leaf 499306814)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 489254574) (.leaf 479416898)) (.branch 100 (.leaf 469788641) (.leaf 460364811))) (.branch 103 (.branch 102 (.leaf 451140559) (.leaf 442111174)) (.branch 104 (.leaf 433272076) (.leaf 424618817))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 416147071) (.leaf 407852632)) (.branch 108 (.leaf 399731411) (.leaf 391779429))) (.branch 111 (.branch 110 (.leaf 383992815) (.leaf 376367803)) (.branch 112 (.leaf 368900729) (.leaf 361588022)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 354426211) (.leaf 347411911)) (.branch 116 (.leaf 340541828) (.leaf 333812752))) (.branch 119 (.branch 118 (.leaf 327221557) (.leaf 320765196)) (.branch 120 (.leaf 314440700) (.leaf 308245173)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 708).prefactor = (4605584958781397/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 708).cutoff/(generalMeanRows 708).c)).2 =
    (387737535879929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 708).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 708).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 708).q*(generalMeanRows 708).c/2-2 = (307/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable081.value]
    have hcontinuation : (generalMeanRows 708).q*(generalMeanRows 708).cutoff/2-2 = (1964/945:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable237.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 708).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 708

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 708).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 708).criticalRate j.val*(generalMeanRows 708).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 708).c*(generalMeanRows 708).criticalPoint j.val)).2-
      (generalMeanRows 708).J/2-(generalMeanRows 708).error (generalMeanGrid j.val)+
      (generalMeanRows 708).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 708).c)).2-
      (generalMeanRows 708).J/2-(generalMeanRows 708).error 4 := by
  have he : (generalMeanRows 708).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 708) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 708)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0708

/-! Kernel-checked entropy margins for general spectral rectangle 709. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0709
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5163636034) (.branch 2 (.leaf 4995686439) (.leaf 4835146067))) (.branch 5 (.branch 4 (.leaf 4681591275) (.leaf 4534628461)) (.branch 6 (.leaf 4393891437) (.leaf 4259039090)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4129753285) (.leaf 4005736986)) (.branch 10 (.leaf 3886712558) (.leaf 3772420242))) (.branch 13 (.branch 12 (.leaf 3662616773) (.leaf 3557074124)) (.branch 14 (.leaf 3455578370) (.leaf 3357928652))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3263936226) (.branch 17 (.leaf 3173423606) (.leaf 3086223766))) (.branch 20 (.branch 19 (.leaf 3002179421) (.leaf 2921142354)) (.branch 21 (.leaf 2842972811) (.leaf 2767538930)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2694716224) (.leaf 2624387101)) (.branch 25 (.leaf 2556440417) (.leaf 2490771069))) (.branch 28 (.branch 27 (.leaf 2427279610) (.leaf 2365871898)) (.branch 29 (.leaf 2306458770) (.leaf 2248955731)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2193282678) (.branch 32 (.leaf 2139363632) (.leaf 2087126491))) (.branch 35 (.branch 34 (.leaf 2036502807) (.leaf 1987427563)) (.branch 36 (.leaf 1939838982) (.leaf 1893678335)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1848889770) (.leaf 1805420146)) (.branch 40 (.leaf 1763218880) (.leaf 1722237808))) (.branch 43 (.branch 42 (.leaf 1682431047) (.leaf 1643754869)) (.branch 44 (.leaf 1606167587) (.leaf 1569629440))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1534102491) (.branch 47 (.leaf 1499550528) (.leaf 1465938974))) (.branch 50 (.branch 49 (.leaf 1433234798) (.leaf 1401406438)) (.branch 51 (.leaf 1370423717) (.leaf 1340257781)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1310881022) (.leaf 1282267018)) (.branch 55 (.leaf 1254390473) (.leaf 1227227161))) (.branch 58 (.branch 57 (.leaf 1200753868) (.leaf 1174948345)) (.branch 59 (.leaf 1149789261) (.leaf 1125256156))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1101329395) (.branch 62 (.leaf 1077990136) (.leaf 1055220285))) (.branch 65 (.branch 64 (.leaf 1033002461) (.leaf 1011319966)) (.branch 66 (.leaf 990156747) (.leaf 969497370)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 949326989) (.leaf 929631319)) (.branch 70 (.leaf 910396610) (.leaf 891609623))) (.branch 73 (.branch 72 (.leaf 873257607) (.leaf 855328275)) (.branch 74 (.leaf 837809785) (.leaf 820690720))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 803960068) (.branch 77 (.leaf 787607205) (.leaf 771621879))) (.branch 80 (.branch 79 (.leaf 755994191) (.leaf 740714582)) (.branch 81 (.leaf 725773820) (.leaf 711162982)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 696873443) (.leaf 682896865)) (.branch 85 (.leaf 669225183) (.leaf 655850594))) (.branch 88 (.branch 87 (.leaf 642765547) (.leaf 629962732)) (.branch 89 (.leaf 617435073) (.leaf 605175712)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 593178010) (.branch 92 (.leaf 581435527) (.leaf 569942027))) (.branch 95 (.branch 94 (.leaf 558691457) (.leaf 547677951)) (.branch 96 (.leaf 536895815) (.leaf 526339526)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 516003722) (.leaf 505883197)) (.branch 100 (.leaf 495972897) (.leaf 486267911))) (.branch 103 (.branch 102 (.leaf 476763468) (.leaf 467454933)) (.branch 104 (.leaf 458337799) (.leaf 449407686))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 440660332) (.leaf 432091596)) (.branch 108 (.leaf 423697445) (.leaf 415473956))) (.branch 111 (.branch 110 (.leaf 407417313) (.leaf 399523800)) (.branch 112 (.leaf 391789798) (.leaf 384211783)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 376786325) (.leaf 369510080)) (.branch 116 (.leaf 362379791) (.leaf 355392284))) (.branch 119 (.branch 118 (.leaf 348544464) (.leaf 341833317)) (.branch 120 (.leaf 335255900) (.leaf 328809347)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 709).prefactor = (2314333647607963/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 709).cutoff/(generalMeanRows 709).c)).2 =
    (201267572999373/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 709).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 709).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 709).q*(generalMeanRows 709).c/2-2 = (1199/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable178.value]
    have hcontinuation : (generalMeanRows 709).q*(generalMeanRows 709).cutoff/2-2 = (32058/15179:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable233.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 709).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 709

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 709).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 709).criticalRate j.val*(generalMeanRows 709).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 709).c*(generalMeanRows 709).criticalPoint j.val)).2-
      (generalMeanRows 709).J/2-(generalMeanRows 709).error (generalMeanGrid j.val)+
      (generalMeanRows 709).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 709).c)).2-
      (generalMeanRows 709).J/2-(generalMeanRows 709).error 4 := by
  have he : (generalMeanRows 709).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 709) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 709)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0709

/-! Kernel-checked entropy margins for general spectral rectangle 710. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0710
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5181283813) (.branch 2 (.leaf 5012760216) (.leaf 4851671165))) (.branch 5 (.branch 4 (.leaf 4697591568) (.leaf 4550126478)) (.branch 6 (.leaf 4408908457) (.leaf 4273595224)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4143867559) (.leaf 4019427409)) (.branch 10 (.leaf 3899996191) (.leaf 3785313258))) (.branch 13 (.branch 12 (.leaf 3675134512) (.leaf 3569231150)) (.branch 14 (.leaf 3467388514) (.leaf 3369405058))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3275091394) (.branch 17 (.leaf 3184269428) (.leaf 3096771566))) (.branch 20 (.branch 19 (.leaf 3012439981) (.leaf 2931125954)) (.branch 21 (.leaf 2852689251) (.leaf 2776997559)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2703925966) (.leaf 2633356479)) (.branch 25 (.leaf 2565177574) (.leaf 2499283787))) (.branch 28 (.branch 27 (.leaf 2435575333) (.leaf 2373957748)) (.branch 29 (.leaf 2314341563) (.leaf 2256641996)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2200778669) (.branch 32 (.leaf 2146675343) (.leaf 2094259672))) (.branch 35 (.branch 34 (.leaf 2043462970) (.leaf 1994220002)) (.branch 36 (.leaf 1946468777) (.leaf 1900150367)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1855208728) (.leaf 1811590537)) (.branch 40 (.leaf 1769245040) (.leaf 1728123907))) (.branch 43 (.branch 42 (.leaf 1688181098) (.leaf 1649372737)) (.branch 44 (.leaf 1611656993) (.leaf 1574993969))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1539345599) (.branch 47 (.leaf 1504675548) (.leaf 1470949119))) (.branch 50 (.branch 49 (.leaf 1438133171) (.leaf 1406196030)) (.branch 51 (.leaf 1375107420) (.leaf 1344838385)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1315361225) (.leaf 1286649427)) (.branch 55 (.leaf 1258677609) (.leaf 1231421460))) (.branch 58 (.branch 57 (.leaf 1204857689) (.leaf 1178963971)) (.branch 59 (.leaf 1153718901) (.leaf 1129101948))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1105093413) (.branch 62 (.leaf 1081674387) (.leaf 1058826715))) (.branch 65 (.branch 64 (.leaf 1036532958) (.leaf 1014776358)) (.branch 66 (.leaf 993540809) (.leaf 972810825)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 952571507) (.leaf 932808523)) (.branch 70 (.leaf 913508076) (.leaf 894656881))) (.branch 73 (.branch 72 (.leaf 876242143) (.leaf 858251534)) (.branch 74 (.leaf 840673171) (.leaf 823495598))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 806707766) (.branch 77 (.leaf 790299014) (.leaf 774259054))) (.branch 80 (.branch 79 (.leaf 758577955) (.leaf 743246126)) (.branch 81 (.leaf 728254300) (.leaf 713593526)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 699255150) (.leaf 685230804)) (.branch 85 (.leaf 671512396) (.leaf 658092097))) (.branch 88 (.branch 87 (.leaf 644962329) (.leaf 632115758)) (.branch 89 (.leaf 619545283) (.leaf 607244024)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 595205316) (.branch 92 (.leaf 583422702) (.leaf 571889920))) (.branch 95 (.branch 94 (.leaf 560600899) (.leaf 549549752)) (.branch 96 (.leaf 538730766) (.leaf 528138399)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 517767270) (.leaf 507612156)) (.branch 100 (.leaf 497667986) (.leaf 487929831))) (.branch 103 (.branch 102 (.leaf 478392904) (.leaf 469052555)) (.branch 104 (.leaf 459904262) (.leaf 450943628))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 442166379) (.leaf 433568357)) (.branch 108 (.leaf 425145517) (.leaf 416893923))) (.branch 111 (.branch 110 (.leaf 408809745) (.leaf 400889254)) (.branch 112 (.leaf 393128819) (.leaf 385524905)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 378074069) (.leaf 370772956)) (.branch 116 (.leaf 363618298) (.leaf 356606909))) (.branch 119 (.branch 118 (.leaf 349735686) (.leaf 343001602)) (.branch 120 (.leaf 336401706) (.leaf 329933120)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 710).prefactor = (232224335482449/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 710).cutoff/(generalMeanRows 710).c)).2 =
    (201267572999373/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 710).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 710).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 710).q*(generalMeanRows 710).c/2-2 = (1199/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable178.value]
    have hcontinuation : (generalMeanRows 710).q*(generalMeanRows 710).cutoff/2-2 = (32058/15179:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable233.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 710).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 710

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 710).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 710).criticalRate j.val*(generalMeanRows 710).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 710).c*(generalMeanRows 710).criticalPoint j.val)).2-
      (generalMeanRows 710).J/2-(generalMeanRows 710).error (generalMeanGrid j.val)+
      (generalMeanRows 710).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 710).c)).2-
      (generalMeanRows 710).J/2-(generalMeanRows 710).error 4 := by
  have he : (generalMeanRows 710).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 710) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 710)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0710

/-! Kernel-checked entropy margins for general spectral rectangle 711. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0711
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5114901208) (.branch 2 (.leaf 4946124565) (.leaf 4784806801))) (.branch 5 (.branch 4 (.leaf 4630522801) (.leaf 4482877525)) (.branch 6 (.leaf 4341503381) (.leaf 4206057884)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4076221553) (.leaf 3951696036)) (.branch 10 (.leaf 3832202409) (.leaf 3717479650))) (.branch 13 (.branch 12 (.leaf 3607283257) (.leaf 3501383992)) (.branch 14 (.leaf 3399566744) (.leaf 3301629490))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3207382353) (.branch 17 (.leaf 3116646730) (.leaf 3029254510))) (.branch 20 (.branch 19 (.leaf 2945047341) (.leaf 2863875968)) (.branch 21 (.leaf 2785599618) (.leaf 2710085436)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2637207966) (.leaf 2566848668)) (.branch 25 (.leaf 2498895476) (.leaf 2433242385))) (.branch 28 (.branch 27 (.leaf 2369789069) (.leaf 2308440532)) (.branch 29 (.leaf 2249106774) (.leaf 2191702491)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2136146788) (.branch 32 (.leaf 2082362916) (.leaf 2030278027))) (.branch 35 (.branch 34 (.leaf 1979822942) (.leaf 1930931940)) (.branch 36 (.leaf 1883542554) (.leaf 1837595389)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1793033943) (.leaf 1749804446)) (.branch 40 (.leaf 1707855705) (.leaf 1667138962))) (.branch 43 (.branch 42 (.leaf 1627607761) (.leaf 1589217816)) (.branch 44 (.leaf 1551926899) (.leaf 1515694727))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1480482856) (.branch 47 (.leaf 1446254582) (.leaf 1412974854))) (.branch 50 (.branch 49 (.leaf 1380610182) (.leaf 1349128557)) (.branch 51 (.leaf 1318499375) (.leaf 1288693363)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1259682512) (.leaf 1231440012)) (.branch 55 (.leaf 1203940192) (.leaf 1177158462))) (.branch 58 (.branch 57 (.leaf 1151071259) (.leaf 1125655998)) (.branch 59 (.leaf 1100891020) (.leaf 1076755550))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1053229653) (.branch 62 (.leaf 1030294192) (.leaf 1007930793))) (.branch 65 (.branch 64 (.leaf 986121805) (.leaf 964850266)) (.branch 66 (.leaf 944099873) (.leaf 923854951)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 904100420) (.leaf 884821772)) (.branch 70 (.leaf 866005041) (.leaf 847636783))) (.branch 73 (.branch 72 (.leaf 829704046) (.leaf 812194354)) (.branch 74 (.leaf 795095681) (.leaf 778396434))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 762085434) (.branch 77 (.leaf 746151895) (.leaf 730585410))) (.branch 80 (.branch 79 (.leaf 715375932) (.leaf 700513761)) (.branch 81 (.leaf 685989527) (.leaf 671794180)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 657918970) (.leaf 644355440)) (.branch 85 (.leaf 631095413) (.leaf 618130977))) (.branch 88 (.branch 87 (.leaf 605454480) (.leaf 593058513)) (.branch 89 (.leaf 580935906) (.leaf 569079715)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 557483214) (.branch 92 (.leaf 546139885) (.leaf 535043415))) (.branch 95 (.branch 94 (.leaf 524187680) (.leaf 513566745)) (.branch 96 (.leaf 503174854) (.leaf 493006421)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 483056027) (.leaf 473318413)) (.branch 100 (.leaf 463788474) (.leaf 454461251))) (.branch 103 (.branch 102 (.leaf 445331929) (.leaf 436395831)) (.branch 104 (.leaf 427648412) (.leaf 419085254))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 410702063) (.leaf 402494666)) (.branch 108 (.leaf 394459002) (.leaf 386591121))) (.branch 111 (.branch 110 (.leaf 378887184) (.leaf 371343450)) (.branch 112 (.leaf 363956283) (.leaf 356722141)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 349637577) (.leaf 342699232)) (.branch 116 (.leaf 335903838) (.leaf 329248210))) (.branch 119 (.branch 118 (.leaf 322729244) (.leaf 316343918)) (.branch 120 (.leaf 310089284) (.leaf 303962470)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 711).prefactor = (2323821941964439/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 711).cutoff/(generalMeanRows 711).c)).2 =
    (392187457384243/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 711).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 711).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 711).q*(generalMeanRows 711).c/2-2 = (6161/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable180.value]
    have hcontinuation : (generalMeanRows 711).q*(generalMeanRows 711).cutoff/2-2 = (15986/7611:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable232.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 711).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 711

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 711).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 711).criticalRate j.val*(generalMeanRows 711).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 711).c*(generalMeanRows 711).criticalPoint j.val)).2-
      (generalMeanRows 711).J/2-(generalMeanRows 711).error (generalMeanGrid j.val)+
      (generalMeanRows 711).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 711).c)).2-
      (generalMeanRows 711).J/2-(generalMeanRows 711).error 4 := by
  have he : (generalMeanRows 711).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 711) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 711)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0711

/-! Kernel-checked entropy margins for general spectral rectangle 712. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0712
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5047895349) (.branch 2 (.leaf 4878946292) (.leaf 4717491364))) (.branch 5 (.branch 4 (.leaf 4563103799) (.leaf 4415386994)) (.branch 6 (.leaf 4273971872) (.leaf 4138514539)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4008694176) (.leaf 3884211152)) (.branch 10 (.leaf 3764785328) (.leaf 3650154523))) (.branch 13 (.branch 12 (.leaf 3540073124) (.leaf 3434310834)) (.branch 14 (.leaf 3332651527) (.leaf 3234892209))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3140842070) (.branch 17 (.leaf 3050321616) (.leaf 2963161877))) (.branch 20 (.branch 19 (.leaf 2879203679) (.leaf 2798296976)) (.branch 21 (.leaf 2720300236) (.leaf 2645079872)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2572509726) (.leaf 2502470582)) (.branch 25 (.leaf 2434849722) (.leaf 2369540513))) (.branch 28 (.branch 27 (.leaf 2306442029) (.leaf 2245458688)) (.branch 29 (.leaf 2186499933) (.leaf 2129479918)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2074317227) (.branch 32 (.leaf 2020934611) (.leaf 1969258736))) (.branch 35 (.branch 34 (.leaf 1919219958) (.leaf 1870752105)) (.branch 36 (.leaf 1823792279) (.leaf 1778280663)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1734160355) (.leaf 1691377193)) (.branch 40 (.leaf 1649879612) (.leaf 1609618492))) (.branch 43 (.branch 42 (.leaf 1570547026) (.leaf 1532620594)) (.branch 44 (.leaf 1495796644) (.leaf 1460034580))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1425295657) (.branch 47 (.leaf 1391542882) (.leaf 1358740924))) (.branch 50 (.branch 49 (.leaf 1326856023) (.leaf 1295855911)) (.branch 51 (.leaf 1265709736) (.leaf 1236387983)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1207862412) (.leaf 1180105990)) (.branch 55 (.leaf 1153092833) (.leaf 1126798145))) (.branch 58 (.branch 57 (.leaf 1101198164) (.leaf 1076270114)) (.branch 59 (.leaf 1051992154) (.leaf 1028343334))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1005303549) (.branch 62 (.leaf 982853502) (.leaf 960974661))) (.branch 65 (.branch 64 (.leaf 939649226) (.leaf 918860094)) (.branch 66 (.leaf 898590825) (.leaf 878825611)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 859549249) (.leaf 840747108)) (.branch 70 (.leaf 822405110) (.leaf 804509699))) (.branch 73 (.branch 72 (.leaf 787047820) (.leaf 770006896)) (.branch 74 (.leaf 753374806) (.leaf 737139866))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 721290811) (.branch 77 (.leaf 705816772) (.leaf 690707263))) (.branch 80 (.branch 79 (.leaf 675952165) (.leaf 661541706)) (.branch 81 (.leaf 647466451) (.leaf 633717284)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 620285397) (.leaf 607162277)) (.branch 85 (.leaf 594339694) (.leaf 581809686))) (.branch 88 (.branch 87 (.leaf 569564553) (.leaf 557596844)) (.branch 89 (.leaf 545899346) (.leaf 534465078)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 523287277) (.branch 92 (.leaf 512359395) (.leaf 501675085))) (.branch 95 (.branch 94 (.leaf 491228196) (.leaf 481012768)) (.branch 96 (.leaf 471023020) (.leaf 461253346)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 451698306) (.leaf 442352625)) (.branch 100 (.leaf 433211182) (.leaf 424269004))) (.branch 103 (.branch 102 (.leaf 415521265) (.leaf 406963278)) (.branch 104 (.leaf 398590489) (.leaf 390398473))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 382382934) (.leaf 374539691)) (.branch 108 (.leaf 366864682) (.leaf 359353959))) (.branch 111 (.branch 110 (.leaf 352003680) (.leaf 344810108)) (.branch 112 (.leaf 337769610) (.leaf 330878647)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 324133777) (.leaf 317531650)) (.branch 116 (.leaf 311069003) (.leaf 304742661))) (.branch 119 (.branch 118 (.leaf 298549529) (.leaf 292486595)) (.branch 120 (.leaf 286550923) (.leaf 280739653)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 712).prefactor = (4663659754216893/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 712).cutoff/(generalMeanRows 712).c)).2 =
    (76944947236531/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 712).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 712).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 712).q*(generalMeanRows 712).c/2-2 = (6327/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable234.value]
    have hcontinuation : (generalMeanRows 712).q*(generalMeanRows 712).cutoff/2-2 = (15986/7611:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable232.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 712).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 712

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 712).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 712).criticalRate j.val*(generalMeanRows 712).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 712).c*(generalMeanRows 712).criticalPoint j.val)).2-
      (generalMeanRows 712).J/2-(generalMeanRows 712).error (generalMeanGrid j.val)+
      (generalMeanRows 712).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 712).c)).2-
      (generalMeanRows 712).J/2-(generalMeanRows 712).error 4 := by
  have he : (generalMeanRows 712).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 712) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 712)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0712

/-! Kernel-checked entropy margins for general spectral rectangle 713. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0713
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5112636118) (.branch 2 (.leaf 4943909505) (.leaf 4782652860))) (.branch 5 (.branch 4 (.leaf 4628439483) (.leaf 4480872901)) (.branch 6 (.leaf 4339584228) (.leaf 4204229810)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4074489116) (.leaf 3950062846)) (.branch 10 (.leaf 3830671227) (.leaf 3716052477))) (.branch 13 (.branch 12 (.leaf 3605961413) (.leaf 3500168189)) (.branch 14 (.leaf 3398457153) (.leaf 3300625806))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3206483843) (.branch 17 (.leaf 3115852291) (.leaf 3028562713))) (.branch 20 (.branch 19 (.leaf 2944456471) (.leaf 2863384064)) (.branch 21 (.leaf 2785204508) (.leaf 2709784768)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2636999236) (.leaf 2566729248)) (.branch 25 (.leaf 2498862634) (.leaf 2433293309))) (.branch 28 (.branch 27 (.leaf 2369920885) (.leaf 2308650320)) (.branch 29 (.leaf 2249391587) (.leaf 2192059363)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2136572752) (.branch 32 (.leaf 2082855012) (.leaf 2030833311))) (.branch 35 (.branch 34 (.leaf 1980438497) (.leaf 1931604881)) (.branch 36 (.leaf 1884270038) (.leaf 1838374618)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1793862170) (.leaf 1750678978)) (.branch 40 (.leaf 1708773909) (.leaf 1668098267))) (.branch 43 (.branch 42 (.leaf 1628605658) (.leaf 1590251865)) (.branch 44 (.leaf 1552994728) (.leaf 1516794032))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1481611402) (.branch 47 (.leaf 1447410207) (.leaf 1414155466))) (.branch 50 (.branch 49 (.leaf 1381813759) (.leaf 1350353149)) (.branch 51 (.leaf 1319743101) (.leaf 1289954412)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1260959142) (.leaf 1232730550)) (.branch 55 (.leaf 1205243030) (.leaf 1178472058))) (.branch 58 (.branch 57 (.leaf 1152394137) (.leaf 1126986744)) (.branch 59 (.leaf 1102228282) (.leaf 1078098036))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1054576131) (.branch 62 (.leaf 1031643487) (.leaf 1009281786))) (.branch 65 (.branch 64 (.leaf 987473430) (.leaf 966201512)) (.branch 66 (.leaf 945449779) (.leaf 925202606)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 905444961) (.leaf 886162382)) (.branch 70 (.leaf 867340949) (.leaf 848967260))) (.branch 73 (.branch 72 (.leaf 831028406) (.leaf 813511951)) (.branch 74 (.leaf 796405909) (.leaf 779698724))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 763379252) (.branch 77 (.leaf 747436744) (.leaf 731860823))) (.branch 80 (.branch 79 (.leaf 716641478) (.leaf 701769037)) (.branch 81 (.leaf 687234161) (.leaf 673027827)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 659141313) (.leaf 645566189)) (.branch 85 (.leaf 632294300) (.leaf 619317760))) (.branch 88 (.branch 87 (.leaf 606628938) (.leaf 594220448)) (.branch 89 (.leaf 582085141) (.leaf 570216090)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 558606590) (.branch 92 (.leaf 547250142) (.leaf 536140446))) (.branch 95 (.branch 94 (.leaf 525271398) (.leaf 514637077)) (.branch 96 (.leaf 504231740) (.leaf 494049816)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 484085900) (.leaf 474334745)) (.branch 100 (.leaf 464791256) (.leaf 455450486))) (.branch 103 (.branch 102 (.leaf 446307632) (.leaf 437358024)) (.branch 104 (.leaf 428597128) (.leaf 420020535))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 411623960) (.leaf 403403234)) (.branch 108 (.leaf 395354306) (.leaf 387473233))) (.branch 111 (.branch 110 (.leaf 379756181) (.leaf 372199417)) (.branch 112 (.leaf 364799307) (.leaf 357552317)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 350455004) (.leaf 343504013)) (.branch 116 (.leaf 336696081) (.leaf 330028025))) (.branch 119 (.branch 118 (.leaf 323496746) (.leaf 317099223)) (.branch 120 (.leaf 310832514) (.leaf 304693747)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 713).prefactor = (2330180095078503/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 713).cutoff/(generalMeanRows 713).c)).2 =
    (4937703919809/12500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 713).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 713).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 713).q*(generalMeanRows 713).c/2-2 = (6161/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable180.value]
    have hcontinuation : (generalMeanRows 713).q*(generalMeanRows 713).cutoff/2-2 = (32058/15179:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable233.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 713).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 713

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 713).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 713).criticalRate j.val*(generalMeanRows 713).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 713).c*(generalMeanRows 713).criticalPoint j.val)).2-
      (generalMeanRows 713).J/2-(generalMeanRows 713).error (generalMeanGrid j.val)+
      (generalMeanRows 713).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 713).c)).2-
      (generalMeanRows 713).J/2-(generalMeanRows 713).error 4 := by
  have he : (generalMeanRows 713).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 713) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 713)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0713

/-! Kernel-checked entropy margins for general spectral rectangle 714. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0714
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5130109595) (.branch 2 (.leaf 4960806324) (.leaf 4798998551))) (.branch 5 (.branch 4 (.leaf 4644258119) (.leaf 4496187198)) (.branch 6 (.leaf 4354415643) (.leaf 4218598623)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4088414514) (.leaf 3963562991)) (.branch 10 (.leaf 3843763327) (.leaf 3728752845))) (.branch 13 (.branch 12 (.leaf 3618285521) (.leaf 3512130727)) (.branch 14 (.leaf 3410072074) (.leaf 3311906367))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3217442655) (.branch 17 (.leaf 3126501352) (.leaf 3038913443))) (.branch 20 (.branch 19 (.leaf 2954519751) (.leaf 2873170263)) (.branch 21 (.leaf 2794723512) (.leaf 2719046010)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2646011719) (.leaf 2575501569)) (.branch 25 (.leaf 2507403007) (.leaf 2441609585))) (.branch 28 (.branch 27 (.leaf 2378020573) (.leaf 2316540604)) (.branch 29 (.leaf 2257079341) (.leaf 2199551173)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2143874925) (.branch 32 (.leaf 2089973593) (.leaf 2037774098))) (.branch 35 (.branch 34 (.leaf 1987207049) (.leaf 1938206535)) (.branch 36 (.leaf 1890709915) (.leaf 1844657638)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1799993059) (.leaf 1756662280)) (.branch 40 (.leaf 1714613992) (.leaf 1673799333))) (.branch 43 (.branch 42 (.leaf 1634171750) (.leaf 1595686875)) (.branch 44 (.leaf 1558302404) (.leaf 1521977984))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1486675111) (.branch 47 (.leaf 1452357027) (.leaf 1418988630))) (.branch 50 (.branch 49 (.leaf 1386536389) (.leaf 1354968256)) (.branch 51 (.leaf 1324253592) (.leaf 1294363094)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1265268727) (.leaf 1236943658)) (.branch 55 (.leaf 1209362193) (.leaf 1182499727))) (.branch 58 (.branch 57 (.leaf 1156332679) (.leaf 1130838451)) (.branch 59 (.leaf 1105995371) (.leaf 1081782656))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1058180360) (.branch 62 (.leaf 1035169339) (.leaf 1012731212))) (.branch 65 (.branch 64 (.leaf 990848322) (.leaf 969503703)) (.branch 66 (.leaf 948681047) (.leaf 928364674)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 908539503) (.leaf 889191022)) (.branch 70 (.leaf 870305263) (.leaf 851868778))) (.branch 73 (.branch 72 (.leaf 833868615) (.leaf 816292294)) (.branch 74 (.leaf 799127788) (.leaf 782363503))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 765988257) (.branch 77 (.leaf 749991261) (.leaf 734362107))) (.branch 80 (.branch 79 (.leaf 719090746) (.leaf 704167476)) (.branch 81 (.leaf 689582924) (.leaf 675328037)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 661394063) (.leaf 647772543)) (.branch 85 (.leaf 634455294) (.leaf 621434404))) (.branch 88 (.branch 87 (.leaf 608702216) (.leaf 596251318)) (.branch 89 (.leaf 584074535) (.leaf 572164920)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 560515742) (.branch 92 (.leaf 549120481) (.leaf 537972816))) (.branch 95 (.branch 94 (.leaf 527066620) (.leaf 516395954)) (.branch 96 (.leaf 505955055) (.leaf 495738332)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 485740363) (.leaf 475955881)) (.branch 100 (.leaf 466379775) (.leaf 457007081))) (.branch 103 (.branch 102 (.leaf 447832979) (.leaf 438852785)) (.branch 104 (.leaf 430061947) (.leaf 421456041))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 413030768) (.leaf 404781947)) (.branch 108 (.leaf 396705510) (.leaf 388797502))) (.branch 111 (.branch 110 (.leaf 381054075) (.leaf 373471484)) (.branch 112 (.leaf 366046083) (.leaf 358774325)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 351652755) (.leaf 344678008)) (.branch 116 (.leaf 337846808) (.leaf 331155963))) (.branch 119 (.branch 118 (.leaf 324602362) (.leaf 318182974)) (.branch 120 (.leaf 311894847) (.leaf 305735100)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 714).prefactor = (1169071980380459/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 714).cutoff/(generalMeanRows 714).c)).2 =
    (4937703919809/12500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 714).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 714).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 714).q*(generalMeanRows 714).c/2-2 = (6161/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable180.value]
    have hcontinuation : (generalMeanRows 714).q*(generalMeanRows 714).cutoff/2-2 = (32058/15179:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable233.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 714).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 714

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 714).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 714).criticalRate j.val*(generalMeanRows 714).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 714).c*(generalMeanRows 714).criticalPoint j.val)).2-
      (generalMeanRows 714).J/2-(generalMeanRows 714).error (generalMeanGrid j.val)+
      (generalMeanRows 714).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 714).c)).2-
      (generalMeanRows 714).J/2-(generalMeanRows 714).error 4 := by
  have he : (generalMeanRows 714).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 714) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 714)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0714

/-! Kernel-checked entropy margins for general spectral rectangle 715. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0715
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5065290493) (.branch 2 (.leaf 4895759234) (.leaf 4733747930))) (.branch 5 (.branch 4 (.leaf 4578828343) (.leaf 4430602502)) (.branch 6 (.leaf 4288700061) (.leaf 4152775940)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4022508213) (.leaf 3897596218)) (.branch 10 (.leaf 3777758851) (.leaf 3662733026))) (.branch 13 (.branch 12 (.leaf 3552272284) (.leaf 3446145535)) (.branch 14 (.leaf 3344135909) (.leaf 3246039710))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3151665472) (.branch 17 (.leaf 3060833083) (.leaf 2973372990))) (.branch 20 (.branch 19 (.leaf 2889125470) (.leaf 2807939961)) (.branch 21 (.leaf 2729674443) (.leaf 2654194868)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2581374644) (.leaf 2511094144)) (.branch 25 (.leaf 2443240261) (.leaf 2377705996))) (.branch 28 (.branch 27 (.leaf 2314390072) (.leaf 2253196582)) (.branch 29 (.leaf 2194034654) (.leaf 2136818146)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2081465364) (.branch 32 (.leaf 2027898790) (.leaf 1976044839))) (.branch 35 (.branch 34 (.leaf 1925833627) (.leaf 1877198753)) (.branch 36 (.leaf 1830077102) (.leaf 1784408653)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1740136305) (.leaf 1697205712)) (.branch 40 (.leaf 1655565129) (.leaf 1615165268))) (.branch 43 (.branch 42 (.leaf 1575959161) (.leaf 1537902034)) (.branch 44 (.leaf 1500951189) (.leaf 1465065888))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1430207253) (.branch 47 (.leaf 1396338166) (.leaf 1363423171))) (.branch 50 (.branch 49 (.leaf 1331428394) (.leaf 1300321456)) (.branch 51 (.leaf 1270071396) (.leaf 1240648599)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1212024729) (.leaf 1184172658)) (.branch 55 (.leaf 1157066413) (.leaf 1130681113))) (.branch 58 (.branch 57 (.leaf 1104992914) (.leaf 1079978961)) (.branch 59 (.leaf 1055617339) (.leaf 1031887025))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1008767845) (.branch 62 (.leaf 986240434) (.leaf 964286198))) (.branch 65 (.branch 64 (.leaf 942887275) (.leaf 922026504)) (.branch 66 (.leaf 901687386) (.leaf 881854061)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 862511272) (.leaf 843644339)) (.branch 70 (.leaf 825239134) (.leaf 807282055))) (.branch 73 (.branch 72 (.leaf 789760002) (.leaf 772660354)) (.branch 74 (.leaf 755970950) (.leaf 739680065))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 723776393) (.branch 77 (.leaf 708249030) (.leaf 693087454))) (.branch 80 (.branch 79 (.leaf 678281509) (.leaf 663821391)) (.branch 81 (.leaf 649697632) (.leaf 635901086)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 622422912) (.leaf 609254570)) (.branch 85 (.leaf 596387800) (.leaf 583814613))) (.branch 88 (.branch 87 (.leaf 571527283) (.leaf 559518333)) (.branch 89 (.leaf 547780526) (.leaf 536306855)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 525090535) (.branch 92 (.leaf 514124995) (.leaf 503403867))) (.branch 95 (.branch 94 (.leaf 492920978) (.leaf 482670348)) (.branch 96 (.leaf 472646175) (.leaf 462842834)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 453254867) (.leaf 443876981)) (.branch 100 (.leaf 434704036) (.leaf 425731043))) (.branch 103 (.branch 102 (.leaf 416953159) (.leaf 408365681)) (.branch 104 (.leaf 399964039) (.leaf 391743794))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 383700633) (.leaf 375830362)) (.branch 108 (.leaf 368128905) (.leaf 360592300))) (.branch 111 (.branch 110 (.leaf 353216691) (.leaf 345998331)) (.branch 112 (.leaf 338933570) (.leaf 332018861)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 325250748) (.leaf 318625870)) (.branch 116 (.leaf 312140953) (.leaf 305792810))) (.branch 119 (.branch 118 (.leaf 299578336) (.leaf 293494509)) (.branch 120 (.leaf 287538383) (.leaf 281707088)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 715).prefactor = (4679730815502219/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 715).cutoff/(generalMeanRows 715).c)).2 =
    (76944947236531/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 715).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 715).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 715).q*(generalMeanRows 715).c/2-2 = (6327/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable234.value]
    have hcontinuation : (generalMeanRows 715).q*(generalMeanRows 715).cutoff/2-2 = (15986/7611:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable232.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 715).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 715

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 715).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 715).criticalRate j.val*(generalMeanRows 715).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 715).c*(generalMeanRows 715).criticalPoint j.val)).2-
      (generalMeanRows 715).J/2-(generalMeanRows 715).error (generalMeanGrid j.val)+
      (generalMeanRows 715).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 715).c)).2-
      (generalMeanRows 715).J/2-(generalMeanRows 715).error 4 := by
  have he : (generalMeanRows 715).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 715) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 715)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0715

/-! Kernel-checked entropy margins for general spectral rectangle 716. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0716
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5082745582) (.branch 2 (.leaf 4912630115) (.leaf 4750060517))) (.branch 5 (.branch 4 (.leaf 4594607074) (.leaf 4445870444)) (.branch 6 (.leaf 4303479004) (.leaf 4167086486)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4036369854) (.leaf 3911027410)) (.branch 10 (.leaf 3790777081) (.leaf 3675354874))) (.branch 13 (.branch 12 (.leaf 3564513483) (.leaf 3458021019)) (.branch 14 (.leaf 3355659865) (.leaf 3257225625))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3162526172) (.branch 17 (.leaf 3071380773) (.leaf 2983619290))) (.branch 20 (.branch 19 (.leaf 2899081452) (.leaf 2817616177)) (.branch 21 (.leaf 2739080953) (.leaf 2663341275)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2590270111) (.leaf 2519747423)) (.branch 25 (.leaf 2451659714) (.leaf 2385899616))) (.branch 28 (.branch 27 (.leaf 2322365505) (.leaf 2260961141)) (.branch 29 (.leaf 2201595339) (.leaf 2144181663)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2088638134) (.branch 32 (.leaf 2034886968) (.leaf 1982854328))) (.branch 35 (.branch 34 (.leaf 1932470087) (.leaf 1883667616)) (.branch 36 (.leaf 1836383583) (.leaf 1790557759)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1746132848) (.leaf 1703054315)) (.branch 40 (.leaf 1661270239) (.leaf 1620731159))) (.branch 43 (.branch 42 (.leaf 1581389947) (.leaf 1543201674)) (.branch 44 (.leaf 1506123495) (.leaf 1470114533))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1435135775) (.branch 47 (.leaf 1401149974) (.leaf 1368121553))) (.branch 50 (.branch 49 (.leaf 1336016522) (.leaf 1304802389)) (.branch 51 (.leaf 1274448086) (.leaf 1244923898)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1216201389) (.leaf 1188253340)) (.branch 55 (.leaf 1161053686) (.leaf 1134577462))) (.branch 58 (.branch 57 (.leaf 1108800741) (.leaf 1083700590)) (.branch 59 (.leaf 1059255017) (.leaf 1035442928))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1012244078) (.branch 62 (.leaf 989639037) (.leaf 967609147))) (.branch 65 (.branch 64 (.leaf 946136483) (.leaf 925203825)) (.branch 66 (.leaf 904794619) (.leaf 884892948)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 865483502) (.leaf 846551554)) (.branch 70 (.leaf 828082924) (.leaf 810063965))) (.branch 73 (.branch 72 (.leaf 792481530) (.leaf 775322957)) (.branch 74 (.leaf 758576040) (.leaf 742229016))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 726270540) (.branch 77 (.leaf 710689670) (.leaf 695475846))) (.branch 80 (.branch 79 (.leaf 680618880) (.leaf 666108933)) (.branch 81 (.leaf 651936503) (.leaf 638092413)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 624567794) (.leaf 611354073)) (.branch 85 (.leaf 598442964) (.leaf 585826450))) (.branch 88 (.branch 87 (.leaf 573496777) (.leaf 561446444)) (.branch 89 (.leaf 549668188) (.leaf 538154979)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 526900008) (.branch 92 (.leaf 515896680) (.leaf 505138606))) (.branch 95 (.branch 94 (.leaf 494619593) (.leaf 484333639)) (.branch 96 (.leaf 474274922) (.leaf 464437799)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 454816792) (.leaf 445406590)) (.branch 100 (.leaf 436202034) (.leaf 427198120))) (.branch 103 (.branch 102 (.leaf 418389988) (.leaf 409772917)) (.branch 104 (.leaf 401342323) (.leaf 393093751))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 385022872) (.leaf 377125480)) (.branch 108 (.leaf 369397484) (.leaf 361834908))) (.branch 111 (.branch 110 (.leaf 354433883) (.leaf 347190648)) (.branch 112 (.leaf 340101542) (.leaf 333163004)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 326371568) (.leaf 319723861)) (.branch 116 (.leaf 313216597) (.leaf 306846578))) (.branch 119 (.branch 118 (.leaf 300610689) (.leaf 294505897)) (.branch 120 (.leaf 288529246) (.leaf 282677856)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 716).prefactor = (1173964314493521/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 716).cutoff/(generalMeanRows 716).c)).2 =
    (76944947236531/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 716).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 716).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 716).q*(generalMeanRows 716).c/2-2 = (6327/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable234.value]
    have hcontinuation : (generalMeanRows 716).q*(generalMeanRows 716).cutoff/2-2 = (15986/7611:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable232.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 716).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 716

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 716).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 716).criticalRate j.val*(generalMeanRows 716).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 716).c*(generalMeanRows 716).criticalPoint j.val)).2-
      (generalMeanRows 716).J/2-(generalMeanRows 716).error (generalMeanGrid j.val)+
      (generalMeanRows 716).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 716).c)).2-
      (generalMeanRows 716).J/2-(generalMeanRows 716).error 4 := by
  have he : (generalMeanRows 716).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 716) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 716)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0716

/-! Kernel-checked entropy margins for general spectral rectangle 717. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0717
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5067774023) (.branch 2 (.leaf 4898196191) (.leaf 4736126905))) (.branch 5 (.branch 4 (.leaf 4581139525) (.leaf 4432837524)) (.branch 6 (.leaf 4290851859) (.leaf 4154838628)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4024476971) (.leaf 3899467180)) (.branch 10 (.leaf 3779529011) (.leaf 3664400151))) (.branch 13 (.branch 12 (.leaf 3553834832) (.leaf 3447602582)) (.branch 14 (.leaf 3345487079) (.leaf 3247285121))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3152805672) (.branch 17 (.leaf 3061869002) (.leaf 2974305896))) (.branch 20 (.branch 19 (.leaf 2889956923) (.leaf 2808671777)) (.branch 21 (.leaf 2730308655) (.leaf 2654733702)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2581820481) (.leaf 2511449501)) (.branch 25 (.leaf 2443507763) (.leaf 2377888357))) (.branch 28 (.branch 27 (.leaf 2314490076) (.leaf 2253217061)) (.branch 29 (.leaf 2193978478) (.leaf 2136688208)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2081264563) (.branch 32 (.leaf 2027630026) (.leaf 1975710998))) (.branch 35 (.branch 34 (.leaf 1925437574) (.leaf 1876743326)) (.branch 36 (.leaf 1829565103) (.leaf 1783842841)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1739519394) (.leaf 1696540365)) (.branch 40 (.leaf 1654853953) (.leaf 1614410811))) (.branch 43 (.branch 42 (.leaf 1575163911) (.leaf 1537068415)) (.branch 44 (.leaf 1500081559) (.leaf 1464162542))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1429272416) (.branch 47 (.leaf 1395373994) (.leaf 1362431753))) (.branch 50 (.branch 49 (.leaf 1330411750) (.leaf 1299281537)) (.branch 51 (.leaf 1269010085) (.leaf 1239567712)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1210926012) (.leaf 1183057793)) (.branch 55 (.leaf 1155937017) (.leaf 1129538735))) (.branch 58 (.branch 57 (.leaf 1103839044) (.leaf 1078815026)) (.branch 59 (.leaf 1054444703) (.leaf 1030706994))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1007581666) (.branch 62 (.leaf 985049299) (.leaf 963091243))) (.branch 65 (.branch 64 (.leaf 941689583) (.leaf 920827103)) (.branch 66 (.leaf 900487258) (.leaf 880654135)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 861312430) (.leaf 842447419)) (.branch 70 (.leaf 824044927) (.leaf 806091310))) (.branch 73 (.branch 72 (.leaf 788573426) (.leaf 771478614)) (.branch 74 (.leaf 754794673) (.leaf 738509842))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 722612779) (.branch 77 (.leaf 707092545) (.leaf 691938584))) (.branch 80 (.branch 79 (.leaf 677140710) (.leaf 662689086)) (.branch 81 (.leaf 648574215) (.leaf 634786923)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 621318343) (.leaf 608159907)) (.branch 85 (.leaf 595303330) (.leaf 582740602))) (.branch 88 (.branch 87 (.leaf 570463972) (.leaf 558465941)) (.branch 89 (.leaf 546739252) (.leaf 535276879)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 524072017) (.branch 92 (.leaf 513118077) (.leaf 502408674))) (.branch 95 (.branch 94 (.leaf 491937620) (.leaf 481698917)) (.branch 96 (.leaf 471686750) (.leaf 461895480)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 452319636) (.leaf 442953911)) (.branch 100 (.leaf 433793153) (.leaf 424832364))) (.branch 103 (.branch 102 (.leaf 416066690) (.leaf 407491415)) (.branch 104 (.leaf 399101963) (.leaf 390893884))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 382862856) (.leaf 375004680)) (.branch 108 (.leaf 367315271) (.leaf 359790658))) (.branch 111 (.branch 110 (.leaf 352426983) (.leaf 345220488)) (.branch 112 (.leaf 338167520) (.leaf 331264526)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 324508047) (.leaf 317894714)) (.branch 116 (.leaf 311421251) (.leaf 305084466))) (.branch 119 (.branch 118 (.leaf 298881252) (.leaf 292808581)) (.branch 120 (.leaf 286863506) (.leaf 281043153)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 717).prefactor = (4666973719460147/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 717).cutoff/(generalMeanRows 717).c)).2 =
    (381903859841009/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 717).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 717).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 717).q*(generalMeanRows 717).c/2-2 = (6327/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable234.value]
    have hcontinuation : (generalMeanRows 717).q*(generalMeanRows 717).cutoff/2-2 = (31886/15265:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable235.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 717).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 717

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 717).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 717).criticalRate j.val*(generalMeanRows 717).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 717).c*(generalMeanRows 717).criticalPoint j.val)).2-
      (generalMeanRows 717).J/2-(generalMeanRows 717).error (generalMeanGrid j.val)+
      (generalMeanRows 717).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 717).c)).2-
      (generalMeanRows 717).J/2-(generalMeanRows 717).error 4 := by
  have he : (generalMeanRows 717).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 717) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 717)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0717

/-! Kernel-checked entropy margins for general spectral rectangle 718. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0718
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5002146497) (.branch 2 (.leaf 4832424804) (.leaf 4670246836))) (.branch 5 (.branch 4 (.leaf 4515184253) (.leaf 4366838919)) (.branch 6 (.leaf 4224840271) (.leaf 4088842959)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3958524747) (.leaf 3833584621)) (.branch 10 (.leaf 3713741090) (.leaf 3598730652))) (.branch 13 (.branch 12 (.leaf 3488306407) (.leaf 3382236797)) (.branch 14 (.leaf 3280304467) (.leaf 3182305220))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3088047073) (.branch 17 (.leaf 2997349387) (.leaf 2910042073))) (.branch 20 (.branch 19 (.leaf 2825964866) (.leaf 2744966654)) (.branch 21 (.leaf 2666904868) (.leaf 2591644908)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2519059629) (.leaf 2449028854)) (.branch 25 (.leaf 2381438929) (.leaf 2316182309))) (.branch 28 (.branch 27 (.leaf 2253157180) (.leaf 2192267098)) (.branch 29 (.leaf 2133420666) (.leaf 2076531222)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2021516556) (.branch 32 (.leaf 1968298649) (.leaf 1916803419))) (.branch 35 (.branch 34 (.leaf 1866960495) (.leaf 1818702999)) (.branch 36 (.leaf 1771967349) (.leaf 1726693066)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1682822603) (.leaf 1640301175)) (.branch 40 (.leaf 1599076613) (.leaf 1559099211))) (.branch 43 (.branch 42 (.leaf 1520321596) (.leaf 1482698601)) (.branch 44 (.leaf 1446187142) (.leaf 1410746110))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1376336263) (.branch 47 (.leaf 1342920129) (.leaf 1310461914))) (.branch 50 (.branch 49 (.leaf 1278927410) (.leaf 1248283916)) (.branch 51 (.leaf 1218500162) (.leaf 1189546231)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1161393494) (.leaf 1134014544)) (.branch 55 (.leaf 1107383134) (.leaf 1081474120))) (.branch 58 (.branch 57 (.leaf 1056263405) (.leaf 1031727890)) (.branch 59 (.leaf 1007845422) (.leaf 984594752))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 961955487) (.branch 62 (.leaf 939908051) (.leaf 918433648))) (.branch 65 (.branch 64 (.leaf 897514221) (.leaf 877132421)) (.branch 66 (.leaf 857271573) (.leaf 837915641)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 819049204) (.leaf 800657424)) (.branch 70 (.leaf 782726022) (.leaf 765241252))) (.branch 73 (.branch 72 (.leaf 748189874) (.leaf 731559136)) (.branch 74 (.leaf 715336749) (.leaf 699510869))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 684070077) (.branch 77 (.leaf 669003357) (.leaf 654300086))) (.branch 80 (.branch 79 (.leaf 639950007) (.leaf 625943225)) (.branch 81 (.leaf 612270181) (.leaf 598921645)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 585888700) (.leaf 573162728)) (.branch 85 (.leaf 560735399) (.leaf 548598659))) (.branch 88 (.branch 87 (.leaf 536744718) (.leaf 525166041)) (.branch 89 (.leaf 513855337) (.leaf 502805547)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 492009839) (.branch 92 (.leaf 481461596) (.leaf 471154410))) (.branch 95 (.branch 94 (.leaf 461082072) (.leaf 451238564)) (.branch 96 (.leaf 441618054) (.leaf 432214887)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 423023580) (.leaf 414038815)) (.branch 100 (.leaf 405255430) (.leaf 396668419))) (.branch 103 (.branch 102 (.leaf 388272922) (.leaf 380064221)) (.branch 104 (.leaf 372037734) (.leaf 364189012))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 356513733) (.leaf 349007699)) (.branch 108 (.leaf 341666829) (.leaf 334487157))) (.branch 111 (.branch 110 (.leaf 327464829) (.leaf 320596095)) (.branch 112 (.leaf 313877310) (.leaf 307304929)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 300875503) (.leaf 294585675)) (.branch 116 (.leaf 288432182) (.leaf 282411844))) (.branch 119 (.branch 118 (.leaf 276521567) (.leaf 270758339)) (.branch 120 (.leaf 265119228) (.leaf 259601376)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 718).prefactor = (4683190257502811/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 718).cutoff/(generalMeanRows 718).c)).2 =
    (93624104640787/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 718).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 718).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 718).q*(generalMeanRows 718).c/2-2 = (6493/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable213.value]
    have hcontinuation : (generalMeanRows 718).q*(generalMeanRows 718).cutoff/2-2 = (31886/15265:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable235.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 718).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 718

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 718).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 718).criticalRate j.val*(generalMeanRows 718).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 718).c*(generalMeanRows 718).criticalPoint j.val)).2-
      (generalMeanRows 718).J/2-(generalMeanRows 718).error (generalMeanGrid j.val)+
      (generalMeanRows 718).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 718).c)).2-
      (generalMeanRows 718).J/2-(generalMeanRows 718).error 4 := by
  have he : (generalMeanRows 718).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 718) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 718)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0718

/-! Kernel-checked entropy margins for general spectral rectangle 719. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0719
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5022229167) (.branch 2 (.leaf 4851874422) (.leaf 4689077895))) (.branch 5 (.branch 4 (.leaf 4533411364) (.leaf 4384476766)) (.branch 6 (.leaf 4241903562) (.leaf 4105346394)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3974482976) (.leaf 3849012219)) (.branch 10 (.leaf 3728652522) (.leaf 3613140251))) (.branch 13 (.branch 12 (.leaf 3502228348) (.leaf 3395685081)) (.branch 14 (.leaf 3293292898) (.leaf 3194847392))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3100156357) (.branch 17 (.leaf 3009038916) (.leaf 2921324736))) (.branch 20 (.branch 19 (.leaf 2836853296) (.leaf 2755473224)) (.branch 21 (.leaf 2677041682) (.leaf 2601423801)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2528492160) (.leaf 2458126305)) (.branch 25 (.leaf 2390212304) (.leaf 2324642334))) (.branch 28 (.branch 27 (.leaf 2261314302) (.leaf 2200131488)) (.branch 29 (.leaf 2141002218) (.leaf 2083839557)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2028561025) (.branch 32 (.leaf 1975088334) (.leaf 1923347139))) (.branch 35 (.branch 34 (.leaf 1873266807) (.leaf 1824780206)) (.branch 36 (.leaf 1777823500) (.leaf 1732335962)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1688259804) (.leaf 1645540004)) (.branch 40 (.leaf 1604124157) (.leaf 1563962333))) (.branch 43 (.branch 42 (.leaf 1525006934) (.leaf 1487212577)) (.branch 44 (.leaf 1450535965) (.leaf 1414935783))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1380372588) (.branch 47 (.leaf 1346808713) (.leaf 1314208171))) (.branch 50 (.branch 49 (.leaf 1282536570) (.leaf 1251761029)) (.branch 51 (.leaf 1221850101) (.leaf 1192773701)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1164503034) (.leaf 1137010532)) (.branch 55 (.leaf 1110269795) (.leaf 1084255526))) (.branch 58 (.branch 57 (.leaf 1058943484) (.leaf 1034310428)) (.branch 59 (.leaf 1010334068) (.leaf 986993023))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 964266772) (.branch 62 (.leaf 942135615) (.leaf 920580636))) (.branch 65 (.branch 64 (.leaf 899583663) (.leaf 879127235)) (.branch 66 (.leaf 859194568) (.leaf 839769522)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 820836575) (.leaf 802380793)) (.branch 70 (.leaf 784387802) (.leaf 766843764))) (.branch 73 (.branch 72 (.leaf 749735354) (.leaf 733049735)) (.branch 74 (.leaf 716774536) (.leaf 700897835))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 685408137) (.branch 77 (.leaf 670294354) (.leaf 655545791))) (.branch 80 (.branch 79 (.leaf 641152126) (.leaf 627103396)) (.branch 81 (.leaf 613389982) (.leaf 600002593)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 586932252) (.leaf 574170286)) (.branch 85 (.leaf 561708311) (.leaf 549538222))) (.branch 88 (.branch 87 (.leaf 537652178) (.leaf 526042596)) (.branch 89 (.leaf 514702139) (.leaf 503623703)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 492800415) (.branch 92 (.leaf 482225615) (.leaf 471892856))) (.branch 95 (.branch 94 (.leaf 461795890) (.leaf 451928664)) (.branch 96 (.leaf 442285311) (.leaf 432860140)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 423647638) (.leaf 414642453)) (.branch 100 (.leaf 405839396) (.leaf 397233430))) (.branch 103 (.branch 102 (.leaf 388819667) (.leaf 380593363)) (.branch 104 (.leaf 372549911) (.leaf 364684837))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 356993796) (.leaf 349472566)) (.branch 108 (.leaf 342117044) (.leaf 334923244))) (.branch 111 (.branch 110 (.leaf 327887291) (.leaf 321005416)) (.branch 112 (.leaf 314273956) (.leaf 307689348)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 301248125) (.leaf 294946915)) (.branch 116 (.leaf 288782437) (.leaf 282751497))) (.branch 119 (.branch 118 (.leaf 276850987) (.leaf 271077880)) (.branch 120 (.leaf 265429231) (.leaf 259902169)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 719).prefactor = (4686667581016313/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 719).cutoff/(generalMeanRows 719).c)).2 =
    (46460434648317/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 719).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 719).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 719).q*(generalMeanRows 719).c/2-2 = (6493/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable213.value]
    have hcontinuation : (generalMeanRows 719).q*(generalMeanRows 719).cutoff/2-2 = (7950/3827:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable231.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 719).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 719

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 719).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 719).criticalRate j.val*(generalMeanRows 719).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 719).c*(generalMeanRows 719).criticalPoint j.val)).2-
      (generalMeanRows 719).J/2-(generalMeanRows 719).error (generalMeanGrid j.val)+
      (generalMeanRows 719).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 719).c)).2-
      (generalMeanRows 719).J/2-(generalMeanRows 719).error 4 := by
  have he : (generalMeanRows 719).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 719) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 719)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0719

/-! Kernel-checked entropy margins for general spectral rectangle 720. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0720
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4957951108) (.branch 2 (.leaf 4787479739) (.leaf 4624601673))) (.branch 5 (.branch 4 (.leaf 4468886945) (.leaf 4319935840)) (.branch 6 (.leaf 4177376258) (.leaf 4040861355)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3910067440) (.leaf 3784692081)) (.branch 10 (.leaf 3664452406) (.leaf 3549083564))) (.branch 13 (.branch 12 (.leaf 3438337339) (.leaf 3331980893)) (.branch 14 (.leaf 3229795617) (.leaf 3131576095))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3037129154) (.branch 17 (.leaf 2946272992) (.leaf 2858836390))) (.branch 20 (.branch 19 (.leaf 2774657979) (.leaf 2693585573)) (.branch 21 (.leaf 2615475552) (.leaf 2540192300)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2467607676) (.leaf 2397600535)) (.branch 25 (.leaf 2330056284) (.leaf 2264866463))) (.branch 28 (.branch 27 (.leaf 2201928365) (.leaf 2141144685)) (.branch 29 (.leaf 2082423181) (.leaf 2025676376)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1970821269) (.branch 32 (.leaf 1917779067) (.leaf 1866474944))) (.branch 35 (.branch 34 (.leaf 1816837802) (.leaf 1768800063)) (.branch 36 (.leaf 1722297460) (.leaf 1677268856)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1633656063) (.leaf 1591403678)) (.branch 40 (.leaf 1550458931) (.leaf 1510771536))) (.branch 43 (.branch 42 (.leaf 1472293558) (.leaf 1434979288)) (.branch 44 (.leaf 1398785115) (.leaf 1363669424))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1329592482) (.branch 47 (.leaf 1296516345) (.leaf 1264404759))) (.branch 50 (.branch 49 (.leaf 1233223075) (.leaf 1202938169)) (.branch 51 (.leaf 1173518358) (.leaf 1144933329)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1117154072) (.leaf 1090152811)) (.branch 55 (.leaf 1063902946) (.leaf 1038378990))) (.branch 58 (.branch 57 (.leaf 1013556521) (.leaf 989412121)) (.branch 59 (.leaf 965923335) (.leaf 943068620))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 920827304) (.branch 62 (.leaf 899179542) (.leaf 878106277))) (.branch 65 (.branch 64 (.leaf 857589206) (.leaf 837610739)) (.branch 66 (.leaf 818153973) (.leaf 799202654)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 780741150) (.leaf 762754423)) (.branch 70 (.leaf 745228001) (.leaf 728147952))) (.branch 73 (.branch 72 (.leaf 711500863) (.leaf 695273812)) (.branch 74 (.leaf 679454350) (.leaf 664030480))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 648990635) (.branch 77 (.leaf 634323662) (.leaf 620018803))) (.branch 80 (.branch 79 (.leaf 606065677) (.leaf 592454266)) (.branch 81 (.leaf 579174899) (.leaf 566218237)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 553575259) (.leaf 541237251)) (.branch 85 (.leaf 529195791) (.leaf 517442735))) (.branch 88 (.branch 87 (.leaf 505970213) (.leaf 494770612)) (.branch 89 (.leaf 483836565) (.leaf 473160948)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 462736861) (.branch 92 (.leaf 452557628) (.leaf 442616784))) (.branch 95 (.branch 94 (.leaf 432908065) (.leaf 423425405)) (.branch 96 (.leaf 414162926) (.leaf 405114930)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 396275893) (.leaf 387640462)) (.branch 100 (.leaf 379203441) (.leaf 370959794))) (.branch 103 (.branch 102 (.leaf 362904631) (.leaf 355033210)) (.branch 104 (.leaf 347340927) (.leaf 339823311))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 332476024) (.leaf 325294850)) (.branch 108 (.leaf 318275696) (.leaf 311414583))) (.branch 111 (.branch 110 (.leaf 304707647) (.leaf 298151132)) (.branch 112 (.leaf 291741387) (.leaf 285474862)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 279348105) (.leaf 273357760)) (.branch 116 (.leaf 267500561) (.leaf 261773333))) (.branch 119 (.branch 118 (.leaf 256172984) (.leaf 250696509)) (.branch 120 (.leaf 245340978) (.leaf 240103544)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 720).prefactor = (94061782788551/20000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 720).cutoff/(generalMeanRows 720).c)).2 =
    (14573220115251/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 720).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 720).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 720).q*(generalMeanRows 720).c/2-2 = (6659/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable215.value]
    have hcontinuation : (generalMeanRows 720).q*(generalMeanRows 720).cutoff/2-2 = (7950/3827:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable231.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 720).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 720

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 720).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 720).criticalRate j.val*(generalMeanRows 720).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 720).c*(generalMeanRows 720).criticalPoint j.val)).2-
      (generalMeanRows 720).J/2-(generalMeanRows 720).error (generalMeanGrid j.val)+
      (generalMeanRows 720).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 720).c)).2-
      (generalMeanRows 720).J/2-(generalMeanRows 720).error 4 := by
  have he : (generalMeanRows 720).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 720) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 720)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0720

/-! Kernel-checked entropy margins for general spectral rectangle 721. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0721
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5019527675) (.branch 2 (.leaf 4849216242) (.leaf 4686474747))) (.branch 5 (.branch 4 (.leaf 4530873361) (.leaf 4382012566)) (.branch 6 (.leaf 4239520509) (.leaf 4103050641)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3972279606) (.leaf 3846905345)) (.branch 10 (.leaf 3726645388) (.leaf 3611235319))) (.branch 13 (.branch 12 (.leaf 3500427378) (.leaf 3393989203)) (.branch 14 (.leaf 3291702684) (.leaf 3193362915))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3098777246) (.branch 17 (.leaf 3007764408) (.leaf 2920153724))) (.branch 20 (.branch 19 (.leaf 2835784370) (.leaf 2754504710)) (.branch 21 (.leaf 2676171679) (.leaf 2600650210)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2527812716) (.leaf 2457538602)) (.branch 25 (.leaf 2389713819) (.leaf 2324230449))) (.branch 28 (.branch 27 (.leaf 2260986324) (.leaf 2199884665)) (.branch 29 (.leaf 2140833756) (.leaf 2083746636)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2028540808) (.branch 32 (.leaf 1975137983) (.leaf 1923463820))) (.branch 35 (.branch 34 (.leaf 1873447704) (.leaf 1825022526)) (.branch 36 (.leaf 1778124482) (.leaf 1732692882)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1688669980) (.leaf 1646000802)) (.branch 40 (.leaf 1604632994) (.leaf 1564516681))) (.branch 43 (.branch 42 (.leaf 1525604325) (.leaf 1487850599)) (.branch 44 (.leaf 1451212272) (.leaf 1415648091))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1381118679) (.branch 47 (.leaf 1347586433) (.leaf 1315015433))) (.branch 50 (.branch 49 (.leaf 1283371355) (.leaf 1252621383)) (.branch 51 (.leaf 1222734138) (.leaf 1193679599)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1165429039) (.leaf 1137954954)) (.branch 55 (.leaf 1111231007) (.leaf 1085231966))) (.branch 58 (.branch 57 (.leaf 1059933650) (.leaf 1035312880)) (.branch 59 (.leaf 1011347427) (.leaf 988015967))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 965298035) (.branch 62 (.leaf 943173990) (.leaf 921624969))) (.branch 65 (.branch 64 (.leaf 900632853) (.leaf 880180232)) (.branch 66 (.leaf 860250372) (.leaf 840827183)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 821895190) (.leaf 803439503)) (.branch 70 (.leaf 785445795) (.leaf 767900269))) (.branch 73 (.branch 72 (.leaf 750789642) (.leaf 734101116)) (.branch 74 (.leaf 717822361) (.leaf 701941490))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 686447045) (.branch 77 (.leaf 671327973) (.leaf 656573611))) (.branch 80 (.branch 79 (.leaf 642173670) (.leaf 628118217)) (.branch 81 (.leaf 614397663) (.leaf 601002744)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 587924513) (.leaf 575154322)) (.branch 85 (.leaf 562683811) (.leaf 550504899))) (.branch 88 (.branch 87 (.leaf 538609769) (.leaf 526990859)) (.branch 89 (.leaf 515640852) (.leaf 504552667)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 493719447) (.branch 92 (.leaf 483134552) (.leaf 472791551))) (.branch 95 (.branch 94 (.leaf 462684214) (.leaf 452806502)) (.branch 96 (.leaf 443152563) (.leaf 433716723)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 424493479) (.leaf 415477494)) (.branch 100 (.leaf 406663589) (.leaf 398046741))) (.branch 103 (.branch 102 (.leaf 389622071) (.leaf 381384846)) (.branch 104 (.leaf 373330469) (.leaf 365454475))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 357752527) (.leaf 350220411)) (.branch 108 (.leaf 342854034) (.leaf 335649415))) (.branch 111 (.branch 110 (.leaf 328602685) (.leaf 321710084)) (.branch 112 (.leaf 314967953) (.leaf 308372735)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 301920968) (.leaf 295609285)) (.branch 116 (.leaf 289434410) (.leaf 283393152))) (.branch 119 (.branch 118 (.leaf 277482408) (.leaf 271699155)) (.branch 120 (.leaf 266040449) (.leaf 260503425)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 721).prefactor = (2349731571930329/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 721).cutoff/(generalMeanRows 721).c)).2 =
    (93624104640787/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 721).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 721).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 721).q*(generalMeanRows 721).c/2-2 = (6493/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable213.value]
    have hcontinuation : (generalMeanRows 721).q*(generalMeanRows 721).cutoff/2-2 = (31886/15265:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable235.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 721).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 721

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 721).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 721).criticalRate j.val*(generalMeanRows 721).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 721).c*(generalMeanRows 721).criticalPoint j.val)).2-
      (generalMeanRows 721).J/2-(generalMeanRows 721).error (generalMeanGrid j.val)+
      (generalMeanRows 721).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 721).c)).2-
      (generalMeanRows 721).J/2-(generalMeanRows 721).error 4 := by
  have he : (generalMeanRows 721).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 721) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 721)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0721

/-! Kernel-checked entropy margins for general spectral rectangle 722. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0722
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4954942262) (.branch 2 (.leaf 4784518740) (.leaf 4621700095))) (.branch 5 (.branch 4 (.leaf 4466054766) (.leaf 4317181592)) (.branch 6 (.leaf 4174707167) (.leaf 4038283467)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3907585733) (.leaf 3782310575)) (.branch 10 (.leaf 3662174253) (.leaf 3546911142))) (.branch 13 (.branch 12 (.leaf 3436272330) (.leaf 3330024353)) (.branch 14 (.leaf 3227948048) (.leaf 3129837503))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3035499107) (.branch 17 (.leaf 2944750669) (.leaf 2857420629))) (.branch 20 (.branch 19 (.leaf 2773347317) (.leaf 2692378287)) (.branch 21 (.leaf 2614369694) (.leaf 2539185727)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2466698080) (.leaf 2396785470)) (.branch 25 (.leaf 2329333188) (.leaf 2264232680))) (.branch 28 (.branch 27 (.leaf 2201381168) (.leaf 2140681287)) (.branch 29 (.leaf 2082040757) (.leaf 2025372074)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1970592221) (.branch 32 (.leaf 1917622406) (.leaf 1866387808))) (.branch 35 (.branch 34 (.leaf 1816817348) (.leaf 1768843470)) (.branch 36 (.leaf 1722401942) (.leaf 1677431663)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1633874489) (.leaf 1591675065)) (.branch 40 (.leaf 1550780672) (.leaf 1511141081))) (.branch 43 (.branch 42 (.leaf 1472708415) (.leaf 1435437024)) (.branch 44 (.leaf 1399283361) (.leaf 1364205875))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1330164898) (.branch 47 (.leaf 1297122552) (.leaf 1265042649))) (.branch 50 (.branch 49 (.leaf 1233890609) (.leaf 1203633373)) (.branch 51 (.leaf 1174239324) (.leaf 1145678217)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1117921107) (.leaf 1090940284)) (.branch 55 (.leaf 1064709211) (.leaf 1039202466))) (.branch 58 (.branch 57 (.leaf 1014395686) (.leaf 990265517)) (.branch 59 (.leaf 966789563) (.leaf 943946340))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 921715232) (.branch 62 (.leaf 900076451) (.leaf 879010995))) (.branch 65 (.branch 64 (.leaf 858500612) (.leaf 838527767)) (.branch 66 (.leaf 819075605) (.leaf 800127921)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 781669130) (.leaf 763684241)) (.branch 70 (.leaf 746158825) (.leaf 729078995))) (.branch 73 (.branch 72 (.leaf 712431377) (.leaf 696203091)) (.branch 74 (.leaf 680381726) (.leaf 664955322))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 649912348) (.branch 77 (.leaf 635241687) (.leaf 620932612))) (.branch 80 (.branch 79 (.leaf 606974777) (.leaf 593358192)) (.branch 81 (.leaf 580073218) (.leaf 567110543)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 554461174) (.leaf 542116422)) (.branch 85 (.leaf 530067890) (.leaf 518307461))) (.branch 88 (.branch 87 (.leaf 506827285) (.leaf 495619771)) (.branch 89 (.leaf 484677575) (.leaf 473993591)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 463560940) (.branch 92 (.leaf 453372963) (.leaf 443423212))) (.branch 95 (.branch 94 (.leaf 433705441) (.leaf 424213599)) (.branch 96 (.leaf 414941823) (.leaf 405884429)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 397035908) (.leaf 388390918)) (.branch 100 (.leaf 379944278) (.leaf 371690960))) (.branch 103 (.branch 102 (.leaf 363626087) (.leaf 355744927)) (.branch 104 (.leaf 348042886) (.leaf 340515504))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 333158448) (.leaf 325967513)) (.branch 108 (.leaf 318938612) (.leaf 312067776))) (.branch 111 (.branch 110 (.leaf 305351146) (.leaf 298784972)) (.branch 112 (.leaf 292365610) (.leaf 286089515)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 279953241) (.leaf 273953437)) (.branch 116 (.leaf 268086841) (.leaf 262350283))) (.branch 119 (.branch 118 (.leaf 256740675) (.leaf 251255013)) (.branch 120 (.leaf 245890375) (.leaf 240643914)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 722).prefactor = (2357896287164823/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 722).cutoff/(generalMeanRows 722).c)).2 =
    (367143444257889/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 722).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 722).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 722).q*(generalMeanRows 722).c/2-2 = (6659/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable215.value]
    have hcontinuation : (generalMeanRows 722).q*(generalMeanRows 722).cutoff/2-2 = (31886/15265:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable235.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 722).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 722

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 722).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 722).criticalRate j.val*(generalMeanRows 722).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 722).c*(generalMeanRows 722).criticalPoint j.val)).2-
      (generalMeanRows 722).J/2-(generalMeanRows 722).error (generalMeanGrid j.val)+
      (generalMeanRows 722).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 722).c)).2-
      (generalMeanRows 722).J/2-(generalMeanRows 722).error 4 := by
  have he : (generalMeanRows 722).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 722) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 722)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0722

/-! Kernel-checked entropy margins for general spectral rectangle 723. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0723
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4894910418) (.branch 2 (.leaf 4724353406) (.leaf 4561424401))) (.branch 5 (.branch 4 (.leaf 4405691663) (.leaf 4256753802)) (.branch 6 (.leaf 4114237127) (.leaf 3977793293)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3847097176) (.leaf 3721844989)) (.branch 10 (.leaf 3601752565) (.leaf 3486553825))) (.branch 13 (.branch 12 (.leaf 3375999379) (.leaf 3269855270)) (.branch 14 (.leaf 3167901822) (.leaf 3069932599))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2975753452) (.branch 17 (.leaf 2885181648) (.leaf 2798045075))) (.branch 20 (.branch 19 (.leaf 2714181508) (.leaf 2633437944)) (.branch 21 (.leaf 2555669980) (.leaf 2480741246)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2408522881) (.leaf 2338893050)) (.branch 25 (.leaf 2271736495) (.leaf 2206944120))) (.branch 28 (.branch 27 (.leaf 2144412608) (.leaf 2084044066)) (.branch 29 (.leaf 2025745691) (.leaf 1969429465)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1915011867) (.branch 32 (.leaf 1862413607) (.leaf 1811559379))) (.branch 35 (.branch 34 (.leaf 1762377626) (.leaf 1714800327)) (.branch 36 (.leaf 1668762794) (.leaf 1624203481)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1581063809) (.leaf 1539288001)) (.branch 40 (.leaf 1498822925) (.leaf 1459617951))) (.branch 43 (.branch 42 (.leaf 1421624812) (.leaf 1384797478)) (.branch 44 (.leaf 1349092036) (.leaf 1314466575))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1280881084) (.branch 47 (.leaf 1248297346) (.leaf 1216678852))) (.branch 50 (.branch 49 (.leaf 1185990704) (.leaf 1156199541)) (.branch 51 (.leaf 1127273453) (.leaf 1099181911)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1071895695) (.leaf 1045386833)) (.branch 55 (.leaf 1019628532) (.leaf 994595126))) (.branch 58 (.branch 57 (.leaf 970262017) (.leaf 946605624)) (.branch 59 (.leaf 923603332) (.leaf 901233449))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 879475157) (.branch 62 (.leaf 858308476) (.leaf 837714219))) (.branch 65 (.branch 64 (.leaf 817673958) (.leaf 798169987)) (.branch 66 (.leaf 779185291) (.leaf 760703509)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 742708909) (.leaf 725186359)) (.branch 70 (.leaf 708121296) (.leaf 691499705))) (.branch 73 (.branch 72 (.leaf 675308090) (.leaf 659533456)) (.branch 74 (.leaf 644163282) (.leaf 629185506))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 614588497) (.branch 77 (.leaf 600361043) (.leaf 586492333))) (.branch 80 (.branch 79 (.leaf 572971936) (.leaf 559789785)) (.branch 81 (.leaf 546936165) (.leaf 534401699)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 522177328) (.leaf 510254302)) (.branch 85 (.leaf 498624169) (.leaf 487278759))) (.branch 88 (.branch 87 (.leaf 476210175) (.leaf 465410781)) (.branch 89 (.leaf 454873191) (.leaf 444590261)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 434555078) (.branch 92 (.leaf 424760953) (.leaf 415201409))) (.branch 95 (.branch 94 (.leaf 405870174) (.leaf 396761176)) (.branch 96 (.leaf 387868531) (.leaf 379186538)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 370709674) (.leaf 362432583)) (.branch 100 (.leaf 354350075) (.leaf 346457116))) (.branch 103 (.branch 102 (.leaf 338748822) (.leaf 331220457)) (.branch 104 (.leaf 323867425) (.leaf 316685267))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 309669653) (.leaf 302816379)) (.branch 108 (.leaf 296121367) (.leaf 289580651))) (.branch 111 (.branch 110 (.leaf 283190382) (.leaf 276946821)) (.branch 112 (.leaf 270846333) (.leaf 264885388)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 259060551) (.leaf 253368486)) (.branch 116 (.leaf 247805950) (.leaf 242369786))) (.branch 119 (.branch 118 (.leaf 237056926) (.leaf 231864385)) (.branch 120 (.leaf 226789260) (.leaf 221828725)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 723).prefactor = (2359784118570319/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 723).cutoff/(generalMeanRows 723).c)).2 =
    (357031200399663/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 723).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 723).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 723).q*(generalMeanRows 723).c/2-2 = (273/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable221.value]
    have hcontinuation : (generalMeanRows 723).q*(generalMeanRows 723).cutoff/2-2 = (7950/3827:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable231.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 723).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 723

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 723).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 723).criticalRate j.val*(generalMeanRows 723).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 723).c*(generalMeanRows 723).criticalPoint j.val)).2-
      (generalMeanRows 723).J/2-(generalMeanRows 723).error (generalMeanGrid j.val)+
      (generalMeanRows 723).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 723).c)).2-
      (generalMeanRows 723).J/2-(generalMeanRows 723).error 4 := by
  have he : (generalMeanRows 723).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 723) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 723)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0723

/-! Kernel-checked entropy margins for general spectral rectangle 724. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0724
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4912061636) (.branch 2 (.leaf 4740907011) (.leaf 4577407121))) (.branch 5 (.branch 4 (.leaf 4421128713) (.leaf 4271668990)) (.branch 6 (.leaf 4128652954) (.leaf 3991731035)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3860576974) (.leaf 3734885917)) (.branch 10 (.leaf 3614372703) (.leaf 3498770319))) (.branch 13 (.branch 12 (.leaf 3387828503) (.leaf 3281312476)) (.branch 14 (.leaf 3179001795) (.leaf 3080689299))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2986180159) (.branch 17 (.leaf 2895291002) (.leaf 2807849111))) (.branch 20 (.branch 19 (.leaf 2723691696) (.leaf 2642665216)) (.branch 21 (.leaf 2564624761) (.leaf 2489433485)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2416962075) (.leaf 2347088269)) (.branch 25 (.leaf 2279696405) (.leaf 2214677005))) (.branch 28 (.branch 27 (.leaf 2151926390) (.leaf 2091346323)) (.branch 29 (.leaf 2032843678) (.leaf 1976330126)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1921721854) (.branch 32 (.leaf 1868939296) (.leaf 1817906880))) (.branch 35 (.branch 34 (.leaf 1768552799) (.leaf 1720808795)) (.branch 36 (.leaf 1674609952) (.leaf 1629894508)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1586603679) (.leaf 1544681494)) (.branch 40 (.leaf 1504074633) (.leaf 1464732289))) (.branch 43 (.branch 42 (.leaf 1426606026) (.leaf 1389649654)) (.branch 44 (.leaf 1353819104) (.leaf 1319072319))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1285369148) (.branch 47 (.leaf 1252671240) (.leaf 1220941958))) (.branch 50 (.branch 49 (.leaf 1190146283) (.leaf 1160250735)) (.branch 51 (.leaf 1131223293) (.leaf 1103033321)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1075651498) (.leaf 1049049751)) (.branch 55 (.leaf 1023201196) (.leaf 998080076))) (.branch 58 (.branch 57 (.leaf 973661707) (.leaf 949922424)) (.branch 59 (.leaf 926839535) (.leaf 904391270))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 882556740) (.branch 62 (.leaf 861315893) (.leaf 840649476))) (.branch 65 (.branch 64 (.leaf 820538996) (.leaf 800966686)) (.branch 66 (.leaf 781915469) (.leaf 763368928)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 745311278) (.leaf 727727331)) (.branch 70 (.leaf 710602474) (.leaf 693922642))) (.branch 73 (.branch 72 (.leaf 677674294) (.leaf 661844387)) (.branch 74 (.leaf 646420358) (.leaf 631390101))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 616741946) (.branch 77 (.leaf 602464641) (.leaf 588547337))) (.branch 80 (.branch 79 (.leaf 574979565) (.leaf 561751225)) (.branch 81 (.leaf 548852568) (.leaf 536274183)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 524006978) (.leaf 512042176)) (.branch 85 (.leaf 500371292) (.leaf 488986130))) (.branch 88 (.branch 87 (.leaf 477878762) (.leaf 467041528)) (.branch 89 (.leaf 456467015) (.leaf 446148055)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 436077711) (.branch 92 (.leaf 426249268) (.leaf 416656228))) (.branch 95 (.branch 94 (.leaf 407292298) (.leaf 398151383)) (.branch 96 (.leaf 389227578) (.leaf 380515165)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 372008599) (.leaf 363702506)) (.branch 100 (.leaf 355591678) (.leaf 347671063))) (.branch 103 (.branch 102 (.leaf 339935760) (.leaf 332381016)) (.branch 104 (.leaf 325002221) (.leaf 317794897))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 310754700) (.leaf 303877414)) (.branch 108 (.leaf 297158943) (.leaf 290595309))) (.branch 111 (.branch 110 (.leaf 284182650) (.leaf 277917212)) (.branch 112 (.leaf 271795349) (.leaf 265813516)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 259968270) (.leaf 254256261)) (.branch 116 (.leaf 248674234) (.leaf 243219022))) (.branch 119 (.branch 118 (.leaf 237887547) (.leaf 232676812)) (.branch 120 (.leaf 227583904) (.leaf 222605988)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 724).prefactor = (947221015153373/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 724).cutoff/(generalMeanRows 724).c)).2 =
    (357031200399663/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 724).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 724).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 724).q*(generalMeanRows 724).c/2-2 = (273/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable221.value]
    have hcontinuation : (generalMeanRows 724).q*(generalMeanRows 724).cutoff/2-2 = (7950/3827:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable231.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 724).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 724

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 724).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 724).criticalRate j.val*(generalMeanRows 724).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 724).c*(generalMeanRows 724).criticalPoint j.val)).2-
      (generalMeanRows 724).J/2-(generalMeanRows 724).error (generalMeanGrid j.val)+
      (generalMeanRows 724).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 724).c)).2-
      (generalMeanRows 724).J/2-(generalMeanRows 724).error 4 := by
  have he : (generalMeanRows 724).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 724) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 724)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0724

/-! Kernel-checked entropy margins for general spectral rectangle 725. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0725
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5033868168) (.branch 2 (.leaf 4863025999) (.leaf 4699790983))) (.branch 5 (.branch 4 (.leaf 4543730224) (.leaf 4394441396)) (.branch 6 (.leaf 4251550069) (.leaf 4114707330)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3983587658) (.leaf 3857887001)) (.branch 10 (.leaf 3737321067) (.leaf 3621623763))) (.branch 13 (.branch 12 (.leaf 3510545792) (.leaf 3403853381)) (.branch 14 (.leaf 3301327124) (.leaf 3202760926))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3107961047) (.branch 17 (.leaf 3016745217) (.leaf 2928941839))) (.branch 20 (.branch 19 (.leaf 2844389249) (.leaf 2762935039)) (.branch 21 (.leaf 2684435434) (.leaf 2608754719)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2535764713) (.leaf 2465344277)) (.branch 25 (.leaf 2397378862) (.leaf 2331760097))) (.branch 28 (.branch 27 (.leaf 2268385394) (.leaf 2207157595)) (.branch 29 (.leaf 2147984635) (.leaf 2090779234)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2035458608) (.branch 32 (.leaf 1981944199) (.leaf 1930161429))) (.branch 35 (.branch 34 (.leaf 1880039462) (.leaf 1831510989)) (.branch 36 (.leaf 1784512024) (.leaf 1738981713)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1694862159) (.leaf 1652098253)) (.branch 40 (.leaf 1610637519) (.leaf 1570429970))) (.branch 43 (.branch 42 (.leaf 1531427966) (.leaf 1493586091)) (.branch 44 (.leaf 1456861031) (.leaf 1421211461))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1386597935) (.branch 47 (.leaf 1352982793) (.leaf 1320330060))) (.branch 50 (.branch 49 (.leaf 1288605363) (.leaf 1257775846)) (.branch 51 (.leaf 1227810089) (.leaf 1198678040)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1170350938) (.leaf 1142801254)) (.branch 55 (.leaf 1116002627) (.leaf 1089929802))) (.branch 58 (.branch 57 (.leaf 1064558583) (.leaf 1039865771)) (.branch 59 (.leaf 1015829123) (.leaf 992427302))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 969639833) (.branch 62 (.leaf 947447064) (.leaf 925830122))) (.branch 65 (.branch 64 (.leaf 904770881) (.leaf 884251925)) (.branch 66 (.leaf 864256514) (.leaf 844768551)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 825772556) (.leaf 807253638)) (.branch 70 (.leaf 789197461) (.leaf 771590228))) (.branch 73 (.branch 72 (.leaf 754418651) (.leaf 737669930)) (.branch 74 (.leaf 721331731) (.leaf 705392165))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 689839770) (.branch 77 (.leaf 674663490) (.leaf 659852660))) (.branch 80 (.branch 79 (.leaf 645396989) (.leaf 631286540)) (.branch 81 (.leaf 617511720) (.leaf 604063264)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 590932220) (.leaf 578109937)) (.branch 85 (.leaf 565588053) (.leaf 553358483))) (.branch 88 (.branch 87 (.leaf 541413404) (.leaf 529745253)) (.branch 89 (.leaf 518346708) (.leaf 507210683)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 496330317) (.branch 92 (.leaf 485698966) (.leaf 475310195))) (.branch 95 (.branch 94 (.leaf 465157767) (.leaf 455235640)) (.branch 96 (.leaf 445537956) (.leaf 436059036)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 426793372) (.leaf 417735620)) (.branch 100 (.leaf 408880598) (.leaf 400223274))) (.branch 103 (.branch 102 (.leaf 391758767) (.leaf 383482335)) (.branch 104 (.leaf 375389376) (.leaf 367475419))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 359736119) (.leaf 352167259)) (.branch 108 (.leaf 344764736) (.leaf 337524565))) (.branch 111 (.branch 110 (.leaf 330442871) (.leaf 323515885)) (.branch 112 (.leaf 316739942) (.leaf 310111479)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 303627028) (.leaf 297283214)) (.branch 116 (.leaf 291076753) (.leaf 285004451))) (.branch 119 (.branch 118 (.leaf 279063194) (.leaf 273249954)) (.branch 120 (.leaf 267561781) (.leaf 261995801)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 725).prefactor = (4728277050513661/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 725).cutoff/(generalMeanRows 725).c)).2 =
    (377317294904789/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 725).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 725).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 725).q*(generalMeanRows 725).c/2-2 = (6493/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable213.value]
    have hcontinuation : (generalMeanRows 725).q*(generalMeanRows 725).cutoff/2-2 = (15986/7611:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable232.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 725).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 725

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 725).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 725).criticalRate j.val*(generalMeanRows 725).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 725).c*(generalMeanRows 725).criticalPoint j.val)).2-
      (generalMeanRows 725).J/2-(generalMeanRows 725).error (generalMeanGrid j.val)+
      (generalMeanRows 725).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 725).c)).2-
      (generalMeanRows 725).J/2-(generalMeanRows 725).error 4 := by
  have he : (generalMeanRows 725).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 725) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 725)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0725

/-! Kernel-checked entropy margins for general spectral rectangle 726. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0726
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5153169518) (.branch 2 (.leaf 4980697018) (.leaf 4815874938))) (.branch 5 (.branch 4 (.leaf 4658267611) (.leaf 4507470162)) (.branch 6 (.leaf 4363105820) (.leaf 4224823515)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4092295740) (.leaf 3965216615)) (.branch 10 (.leaf 3843300159) (.leaf 3726278721))) (.branch 13 (.branch 12 (.leaf 3613901568) (.leaf 3505933599)) (.branch 14 (.leaf 3402154181) (.leaf 3302356086))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3206344525) (.branch 17 (.leaf 3113936262) (.leaf 3024958801))) (.branch 20 (.branch 19 (.leaf 2939249650) (.leaf 2856655632)) (.branch 21 (.leaf 2777032265) (.leaf 2700243176)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2626159575) (.leaf 2554659761)) (.branch 25 (.leaf 2485628663) (.leaf 2418957427))) (.branch 28 (.branch 27 (.leaf 2354543020) (.leaf 2292287868)) (.branch 29 (.leaf 2232099524) (.leaf 2173890353)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2117577241) (.branch 32 (.leaf 2063081327) (.leaf 2010327748))) (.branch 35 (.branch 34 (.leaf 1959245409) (.leaf 1909766756)) (.branch 36 (.leaf 1861827579) (.leaf 1815366816)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1770326376) (.leaf 1726650969)) (.branch 40 (.leaf 1684287954) (.leaf 1643187185))) (.branch 43 (.branch 42 (.leaf 1603300881) (.leaf 1564583491)) (.branch 44 (.leaf 1526991576) (.leaf 1490483692))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1455020286) (.branch 47 (.leaf 1420563595) (.leaf 1387077550))) (.branch 50 (.branch 49 (.leaf 1354527687) (.leaf 1322881067)) (.branch 51 (.leaf 1292106190) (.leaf 1262172930)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1233052457) (.leaf 1204717174)) (.branch 55 (.leaf 1177140656) (.leaf 1150297589))) (.branch 58 (.branch 57 (.leaf 1124163719) (.leaf 1098715793)) (.branch 59 (.leaf 1073931516) (.leaf 1049789498))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1026269217) (.branch 62 (.leaf 1003350972) (.leaf 981015846))) (.branch 65 (.branch 64 (.leaf 959245669) (.leaf 938022978)) (.branch 66 (.leaf 917330992) (.leaf 897153574)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 877475201) (.leaf 858280941)) (.branch 70 (.leaf 839556420) (.leaf 821287799))) (.branch 73 (.branch 72 (.leaf 803461751) (.leaf 786065437)) (.branch 74 (.leaf 769086484) (.leaf 752512964))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 736333375) (.branch 77 (.leaf 720536624) (.leaf 705112006))) (.branch 80 (.branch 79 (.leaf 690049189) (.leaf 675338199)) (.branch 81 (.leaf 660969403) (.leaf 646933497)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 633221487) (.leaf 619824684)) (.branch 85 (.leaf 606734685) (.leaf 593943363))) (.branch 88 (.branch 87 (.leaf 581442857) (.leaf 569225560)) (.branch 89 (.leaf 557284111) (.leaf 545611380)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 534200466) (.branch 92 (.leaf 523044682) (.leaf 512137550))) (.branch 95 (.branch 94 (.leaf 501472791) (.leaf 491044319)) (.branch 96 (.leaf 480846234) (.leaf 470872813)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 461118502) (.leaf 451577917)) (.branch 100 (.leaf 442245828) (.leaf 433117160))) (.branch 103 (.branch 102 (.leaf 424186987) (.leaf 415450522)) (.branch 104 (.leaf 406903118) (.leaf 398540258))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 390357553) (.leaf 382350739)) (.branch 108 (.leaf 374515668) (.leaf 366848308))) (.branch 111 (.branch 110 (.leaf 359344738) (.leaf 352001145)) (.branch 112 (.leaf 344813816) (.leaf 337779141)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 330893607) (.leaf 324153792)) (.branch 116 (.leaf 317556367) (.leaf 311098088))) (.branch 119 (.branch 118 (.leaf 304775798) (.leaf 298586421)) (.branch 120 (.leaf 292526960) (.leaf 286594496)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 726).prefactor = (1190230166624537/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 726).cutoff/(generalMeanRows 726).c)).2 =
    (76944947236531/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 726).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 726).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 726).q*(generalMeanRows 726).c/2-2 = (6327/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable234.value]
    have hcontinuation : (generalMeanRows 726).q*(generalMeanRows 726).cutoff/2-2 = (15986/7611:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable232.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 726).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 726

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 726).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 726).criticalRate j.val*(generalMeanRows 726).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 726).c*(generalMeanRows 726).criticalPoint j.val)).2-
      (generalMeanRows 726).J/2-(generalMeanRows 726).error (generalMeanGrid j.val)+
      (generalMeanRows 726).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 726).c)).2-
      (generalMeanRows 726).J/2-(generalMeanRows 726).error 4 := by
  have he : (generalMeanRows 726).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 726) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 726)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0726

/-! Kernel-checked entropy margins for general spectral rectangle 727. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0727
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5263793526) (.branch 2 (.leaf 5096295096) (.leaf 4936138828))) (.branch 5 (.branch 4 (.leaf 4782904293) (.leaf 4636200937)) (.branch 6 (.leaf 4495665469) (.leaf 4360959530)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4231767610) (.leaf 4107795171)) (.branch 10 (.leaf 3988766966) (.leaf 3874425518))) (.branch 13 (.branch 12 (.leaf 3764529738) (.leaf 3658853686)) (.branch 14 (.leaf 3557185432) (.leaf 3459326027))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3365088559) (.branch 17 (.leaf 3274297295) (.leaf 3186786894))) (.branch 20 (.branch 19 (.leaf 3102401683) (.leaf 3020994995)) (.branch 21 (.leaf 2942428560) (.leaf 2866571944)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2793302029) (.leaf 2722502537)) (.branch 25 (.leaf 2654063587) (.leaf 2587881288))) (.branch 28 (.branch 27 (.leaf 2523857356) (.leaf 2461898770)) (.branch 29 (.leaf 2401917437) (.leaf 2343829897)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2287557036) (.branch 32 (.leaf 2233023825) (.leaf 2180159078))) (.branch 35 (.branch 34 (.leaf 2128895221) (.leaf 2079168081)) (.branch 36 (.leaf 2030916690) (.leaf 1984083096)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1938612189) (.leaf 1894451544)) (.branch 40 (.leaf 1851551266) (.leaf 1809863847))) (.branch 43 (.branch 42 (.leaf 1769344037) (.leaf 1729948714)) (.branch 44 (.leaf 1691636771) (.leaf 1654369003))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1618108007) (.branch 47 (.leaf 1582818083) (.leaf 1548465144))) (.branch 50 (.branch 49 (.leaf 1515016628) (.leaf 1482441422)) (.branch 51 (.leaf 1450709781) (.leaf 1419793260)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1389664646) (.leaf 1360297894)) (.branch 55 (.leaf 1331668069) (.leaf 1303751287))) (.branch 58 (.branch 57 (.leaf 1276524664) (.leaf 1249966266)) (.branch 59 (.leaf 1224055060) (.leaf 1198770872))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1174094341) (.branch 62 (.leaf 1150006885) (.leaf 1126490657))) (.branch 65 (.branch 64 (.leaf 1103528512) (.leaf 1081103977)) (.branch 66 (.leaf 1059201212) (.leaf 1037804987)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1016900648) (.leaf 996474093)) (.branch 70 (.leaf 976511747) (.leaf 957000534))) (.branch 73 (.branch 72 (.leaf 937927859) (.leaf 919281582)) (.branch 74 (.leaf 901050002) (.leaf 883221833))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 865786186) (.branch 77 (.leaf 848732555) (.leaf 832050797))) (.branch 80 (.branch 79 (.leaf 815731118) (.leaf 799764055)) (.branch 81 (.leaf 784140466) (.leaf 768851513)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 753888652) (.leaf 739243617)) (.branch 85 (.leaf 724908411) (.leaf 710875295))) (.branch 88 (.branch 87 (.leaf 697136778) (.leaf 683685603)) (.branch 89 (.leaf 670514741) (.leaf 657617384)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 644986928) (.branch 92 (.leaf 632616976) (.leaf 620501321))) (.branch 95 (.branch 94 (.leaf 608633943) (.leaf 597008999)) (.branch 96 (.leaf 585620820) (.leaf 574463902)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 563532899) (.leaf 552822619)) (.branch 100 (.leaf 542328019) (.leaf 532044195))) (.branch 103 (.branch 102 (.leaf 521966384) (.leaf 512089951)) (.branch 104 (.leaf 502410392) (.leaf 492923324))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 483624483) (.leaf 474509720)) (.branch 108 (.leaf 465574995) (.leaf 456816376))) (.branch 111 (.branch 110 (.leaf 448230035) (.leaf 439812243)) (.branch 112 (.leaf 431559365) (.leaf 423467864)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 415534288) (.leaf 407755276)) (.branch 116 (.leaf 400127550) (.leaf 392647915))) (.branch 119 (.branch 118 (.leaf 385313252) (.leaf 378120521)) (.branch 120 (.leaf 371066758) (.leaf 364149068)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 727).prefactor = (2311632775052493/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 727).cutoff/(generalMeanRows 727).c)).2 =
    (41383648669473/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 727).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 727).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 727).q*(generalMeanRows 727).c/2-2 = (1453/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable239.value]
    have hcontinuation : (generalMeanRows 727).q*(generalMeanRows 727).cutoff/2-2 = (3970/1869:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable240.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 727).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 727

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 727).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 727).criticalRate j.val*(generalMeanRows 727).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 727).c*(generalMeanRows 727).criticalPoint j.val)).2-
      (generalMeanRows 727).J/2-(generalMeanRows 727).error (generalMeanGrid j.val)+
      (generalMeanRows 727).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 727).c)).2-
      (generalMeanRows 727).J/2-(generalMeanRows 727).error 4 := by
  have he : (generalMeanRows 727).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 727) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 727)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0727

/-! Kernel-checked entropy margins for general spectral rectangle 728. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0728
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4981269577) (.branch 2 (.leaf 4807703488) (.leaf 4641899985))) (.branch 5 (.branch 4 (.leaf 4483419710) (.leaf 4331854191)) (.branch 6 (.leaf 4186823146) (.leaf 4047972081)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3914970140) (.leaf 3787508173)) (.branch 10 (.leaf 3665297001) (.leaf 3548065850))) (.branch 13 (.branch 12 (.leaf 3435560932) (.leaf 3327544160)) (.branch 14 (.leaf 3223791984) (.leaf 3124094325))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3028253609) (.branch 17 (.leaf 2936083879) (.leaf 2847409986))) (.branch 20 (.branch 19 (.leaf 2762066845) (.leaf 2679898751)) (.branch 21 (.leaf 2600758754) (.leaf 2524508079)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2451015591) (.leaf 2380157306)) (.branch 25 (.leaf 2311815931) (.leaf 2245880448))) (.branch 28 (.branch 27 (.leaf 2182245715) (.leaf 2120812112)) (.branch 29 (.leaf 2061485200) (.leaf 2004175407)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1948797738) (.branch 32 (.leaf 1895271506) (.leaf 1843520075))) (.branch 35 (.branch 34 (.leaf 1793470626) (.leaf 1745053938)) (.branch 36 (.leaf 1698204180) (.leaf 1652858723)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1608957954) (.leaf 1566445110)) (.branch 40 (.leaf 1525266124) (.leaf 1485369470))) (.branch 43 (.branch 42 (.leaf 1446706032) (.leaf 1409228966)) (.branch 44 (.leaf 1372893586) (.leaf 1337657240))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1303479212) (.branch 47 (.leaf 1270320611) (.leaf 1238144283))) (.branch 50 (.branch 49 (.leaf 1206914715) (.leaf 1176597957)) (.branch 51 (.leaf 1147161537) (.leaf 1118574385)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1090806769) (.leaf 1063830220)) (.branch 55 (.leaf 1037617475) (.leaf 1012142413))) (.branch 58 (.branch 57 (.leaf 987380004) (.leaf 963306249)) (.branch 59 (.leaf 939898136) (.leaf 917133589))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 894991424) (.branch 62 (.leaf 873451306) (.leaf 852493712))) (.branch 65 (.branch 64 (.leaf 832099888) (.leaf 812251816)) (.branch 66 (.leaf 792932179) (.leaf 774124329)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 755812258) (.leaf 737980563)) (.branch 70 (.leaf 720614427) (.leaf 703699587))) (.branch 73 (.branch 72 (.leaf 687222310) (.leaf 671169369)) (.branch 74 (.leaf 655528025) (.leaf 640286001))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 625431462) (.branch 77 (.leaf 610952999) (.leaf 596839609))) (.branch 80 (.branch 79 (.leaf 583080675) (.leaf 569665956)) (.branch 81 (.leaf 556585565) (.leaf 543829957)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 531389916) (.leaf 519256537)) (.branch 85 (.leaf 507421218) (.leaf 495875645))) (.branch 88 (.branch 87 (.leaf 484611781) (.leaf 473621857)) (.branch 89 (.leaf 462898356) (.leaf 452434008)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 442221779) (.branch 92 (.leaf 432254859) (.leaf 422526660))) (.branch 95 (.branch 94 (.leaf 413030797) (.leaf 403761092)) (.branch 96 (.leaf 394711557) (.leaf 385876391)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 377249972) (.leaf 368826852)) (.branch 100 (.leaf 360601747) (.leaf 352569535))) (.branch 103 (.branch 102 (.leaf 344725247) (.leaf 337064061)) (.branch 104 (.leaf 329581303) (.leaf 322272432))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 315133044) (.leaf 308158861)) (.branch 108 (.leaf 301345730) (.leaf 294689619))) (.branch 111 (.branch 110 (.leaf 288186609) (.leaf 281832895)) (.branch 112 (.leaf 275624779) (.leaf 269558666)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 263631064) (.leaf 257838576)) (.branch 116 (.leaf 252177902) (.leaf 246645829))) (.branch 119 (.branch 118 (.leaf 241239237) (.leaf 235955086)) (.branch 120 (.leaf 230790422) (.leaf 225742370)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 728).prefactor = (960566779281063/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 728).cutoff/(generalMeanRows 728).c)).2 =
    (357031200399663/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 728).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 728).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 728).q*(generalMeanRows 728).c/2-2 = (273/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable221.value]
    have hcontinuation : (generalMeanRows 728).q*(generalMeanRows 728).cutoff/2-2 = (7950/3827:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable231.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 728).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 728

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 728).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 728).criticalRate j.val*(generalMeanRows 728).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 728).c*(generalMeanRows 728).criticalPoint j.val)).2-
      (generalMeanRows 728).J/2-(generalMeanRows 728).error (generalMeanGrid j.val)+
      (generalMeanRows 728).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 728).c)).2-
      (generalMeanRows 728).J/2-(generalMeanRows 728).error 4 := by
  have he : (generalMeanRows 728).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 728) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 728)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0728

/-! Kernel-checked entropy margins for general spectral rectangle 729. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0729
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4897978896) (.branch 2 (.leaf 4727382091) (.leaf 4564401241))) (.branch 5 (.branch 4 (.leaf 4408606216) (.leaf 4259597088)) (.branch 6 (.leaf 4117001490) (.leaf 3980472272)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3849685394) (.leaf 3724338043)) (.branch 10 (.leaf 3604146935) (.leaf 3488846780))) (.branch 13 (.branch 12 (.leaf 3378188901) (.leaf 3271939978)) (.branch 14 (.leaf 3169880906) (.leaf 3071805757))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2977520835) (.branch 17 (.leaf 2886843809) (.leaf 2799602919))) (.branch 20 (.branch 19 (.leaf 2715636255) (.leaf 2634791085)) (.branch 21 (.leaf 2556923244) (.leaf 2481896566)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2409582368) (.leaf 2339858963)) (.branch 25 (.leaf 2272611218) (.leaf 2207730140))) (.branch 28 (.branch 27 (.leaf 2145112496) (.leaf 2084660458)) (.branch 29 (.leaf 2026281272) (.leaf 1969886954)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1915394006) (.branch 32 (.leaf 1862723147) (.leaf 1811799071))) (.branch 35 (.branch 34 (.leaf 1762550211) (.leaf 1714908529)) (.branch 36 (.leaf 1668809309) (.leaf 1624190975)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1580994911) (.leaf 1539165295)) (.branch 40 (.leaf 1498648951) (.leaf 1459395196))) (.branch 43 (.branch 42 (.leaf 1421355711) (.leaf 1384484410)) (.branch 44 (.leaf 1348737321) (.leaf 1314072474))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1280449794) (.branch 47 (.leaf 1247831005) (.leaf 1216179533))) (.branch 50 (.branch 49 (.leaf 1185460417) (.leaf 1155640232)) (.branch 51 (.leaf 1126687004) (.leaf 1098570140)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1071260359) (.leaf 1044729624)) (.branch 55 (.leaf 1018951081) (.leaf 993899004))) (.branch 58 (.branch 57 (.leaf 969548733) (.leaf 945876628)) (.branch 59 (.leaf 922860018) (.leaf 900477151))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 878707157) (.branch 62 (.leaf 857529998) (.leaf 836926436))) (.branch 65 (.branch 64 (.leaf 816877990) (.leaf 797366905)) (.branch 66 (.leaf 778376115) (.leaf 759889213)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 741890420) (.leaf 724364559)) (.branch 70 (.leaf 707297024) (.leaf 690673756))) (.branch 73 (.branch 72 (.leaf 674481221) (.leaf 658706382)) (.branch 74 (.leaf 643336683) (.leaf 628360021))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 613764732) (.branch 77 (.leaf 599539572) (.leaf 585673693))) (.branch 80 (.branch 79 (.leaf 572156633) (.leaf 558978297)) (.branch 81 (.leaf 546128939) (.leaf 533599154)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 521379855) (.leaf 509462269)) (.branch 85 (.leaf 497837916) (.leaf 486498603))) (.branch 88 (.branch 87 (.leaf 475436411) (.leaf 464643681)) (.branch 89 (.leaf 454113007) (.leaf 443837225)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 433809404) (.branch 92 (.leaf 424022834) (.leaf 414471022))) (.branch 95 (.branch 94 (.leaf 405147679) (.leaf 396046718)) (.branch 96 (.leaf 387162239) (.leaf 378488529)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 370020048) (.leaf 361751430)) (.branch 100 (.leaf 353677471) (.leaf 345793125))) (.branch 103 (.branch 102 (.leaf 338093498) (.leaf 330573843)) (.branch 104 (.leaf 323229555) (.leaf 316056164))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 309049332) (.leaf 302204848)) (.branch 108 (.leaf 295518623) (.leaf 288986686))) (.branch 111 (.branch 110 (.leaf 282605181) (.leaf 276370361)) (.branch 112 (.leaf 270278585) (.leaf 264326318)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 258510119) (.leaf 252826648)) (.branch 116 (.leaf 247272656) (.leaf 241844982))) (.branch 119 (.branch 118 (.leaf 236540553) (.leaf 231356383)) (.branch 120 (.leaf 226289562) (.leaf 221337262)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 729).prefactor = (4706736702440241/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 729).cutoff/(generalMeanRows 729).c)).2 =
    (70845229894411/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 729).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 729).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 729).q*(generalMeanRows 729).c/2-2 = (273/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable221.value]
    have hcontinuation : (generalMeanRows 729).q*(generalMeanRows 729).cutoff/2-2 = (31714/15351:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable238.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 729).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 729

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 729).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 729).criticalRate j.val*(generalMeanRows 729).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 729).c*(generalMeanRows 729).criticalPoint j.val)).2-
      (generalMeanRows 729).J/2-(generalMeanRows 729).error (generalMeanGrid j.val)+
      (generalMeanRows 729).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 729).c)).2-
      (generalMeanRows 729).J/2-(generalMeanRows 729).error 4 := by
  have he : (generalMeanRows 729).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 729) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 729)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0729

/-! Kernel-checked entropy margins for general spectral rectangle 730. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0730
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4915285722) (.branch 2 (.leaf 4744086120) (.leaf 4580529382))) (.branch 5 (.branch 4 (.leaf 4424183862) (.leaf 4274648215)) (.branch 6 (.leaf 4131548761) (.leaf 3994537122)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3863288114) (.leaf 3737497853)) (.branch 10 (.leaf 3616882054) (.leaf 3501174490))) (.branch 13 (.branch 12 (.leaf 3390125605) (.leaf 3283501256)) (.branch 14 (.leaf 3181081562) (.leaf 3082659868))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2988041794) (.branch 17 (.leaf 2897044364) (.leaf 2809495212))) (.branch 20 (.branch 19 (.leaf 2725231854) (.leaf 2644101021)) (.branch 21 (.leaf 2565958037) (.leaf 2490666255)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2418096538) (.leaf 2348126768)) (.branch 25 (.leaf 2280641405) (.leaf 2215531072))) (.branch 28 (.branch 27 (.leaf 2152692171) (.leaf 2092026528)) (.branch 29 (.leaf 2033441061) (.leaf 1976847476)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1922161979) (.branch 32 (.leaf 1869305010) (.leaf 1818200996))) (.branch 35 (.branch 34 (.leaf 1768778117) (.leaf 1720968094)) (.branch 36 (.leaf 1674705985) (.leaf 1629929994)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1586581297) (.leaf 1544603878)) (.branch 40 (.leaf 1503944371) (.leaf 1464551915))) (.branch 43 (.branch 42 (.leaf 1426378019) (.leaf 1389376434)) (.branch 44 (.leaf 1353503034) (.leaf 1318715700))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1284974216) (.branch 47 (.leaf 1252240170) (.leaf 1220476858))) (.branch 50 (.branch 49 (.leaf 1189649198) (.leaf 1159723644)) (.branch 51 (.leaf 1130668110) (.leaf 1102451897)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1075045617) (.leaf 1048421137)) (.branch 55 (.leaf 1022551507) (.leaf 997410909))) (.branch 58 (.branch 57 (.leaf 972974597) (.leaf 949218848)) (.branch 59 (.leaf 926120909) (.leaf 903658954))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 881812036) (.branch 62 (.leaf 860560048) (.leaf 839883684))) (.branch 65 (.branch 64 (.leaf 819764398) (.leaf 800184371)) (.branch 66 (.leaf 781126478) (.leaf 762574253)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 744511862) (.leaf 726924074)) (.branch 70 (.leaf 709796231) (.leaf 693114226))) (.branch 73 (.branch 72 (.leaf 676864475) (.leaf 661033897)) (.branch 74 (.leaf 645609889) (.leaf 630580307))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 615933447) (.branch 77 (.leaf 601658022) (.leaf 587743149))) (.branch 80 (.branch 79 (.leaf 574178327) (.leaf 560953426)) (.branch 81 (.leaf 548058666) (.leaf 535484606)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 523222131) (.leaf 511262435)) (.branch 85 (.leaf 499597008) (.leaf 488217628))) (.branch 88 (.branch 87 (.leaf 477116348) (.leaf 466285482)) (.branch 89 (.leaf 455717599) (.leaf 445405508)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 435342253) (.branch 92 (.leaf 425521103) (.leaf 415935540))) (.branch 95 (.branch 94 (.leaf 406579254) (.leaf 397446134)) (.branch 96 (.leaf 388530263) (.leaf 379825904)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 371327500) (.leaf 363029665)) (.branch 100 (.leaf 354927177) (.leaf 347014972))) (.branch 103 (.branch 102 (.leaf 339288139) (.leaf 331741914)) (.branch 104 (.leaf 324371675) (.leaf 317172937))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 310141346) (.leaf 303272678)) (.branch 108 (.leaf 296562827) (.leaf 290007810))) (.branch 111 (.branch 110 (.leaf 283603756) (.leaf 277346905)) (.branch 112 (.leaf 271233605) (.leaf 265260305)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 259423555) (.leaf 253720002)) (.branch 116 (.leaf 248146384) (.leaf 242699532))) (.branch 119 (.branch 118 (.leaf 237376361) (.leaf 232173872)) (.branch 120 (.leaf 227089148) (.leaf 222119349)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 730).prefactor = (236168389045319/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 730).cutoff/(generalMeanRows 730).c)).2 =
    (70845229894411/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 730).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 730).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 730).q*(generalMeanRows 730).c/2-2 = (273/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable221.value]
    have hcontinuation : (generalMeanRows 730).q*(generalMeanRows 730).cutoff/2-2 = (31714/15351:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable238.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 730).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 730

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 730).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 730).criticalRate j.val*(generalMeanRows 730).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 730).c*(generalMeanRows 730).criticalPoint j.val)).2-
      (generalMeanRows 730).J/2-(generalMeanRows 730).error (generalMeanGrid j.val)+
      (generalMeanRows 730).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 730).c)).2-
      (generalMeanRows 730).J/2-(generalMeanRows 730).error 4 := by
  have he : (generalMeanRows 730).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 730) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 730)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0730

/-! Kernel-checked entropy margins for general spectral rectangle 731. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0731
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5249454706) (.branch 2 (.leaf 5082420525) (.leaf 4922682820))) (.branch 5 (.branch 4 (.leaf 4769825634) (.leaf 4623462494)) (.branch 6 (.leaf 4483233822) (.leaf 4348804648)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4219862545) (.leaf 4096115786)) (.branch 10 (.leaf 3977291680) (.leaf 3863135076))) (.branch 13 (.branch 12 (.leaf 3753407001) (.leaf 3647883437)) (.branch 14 (.leaf 3546354200) (.leaf 3448621923))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3354501130) (.branch 17 (.leaf 3263817388) (.leaf 3176406530))) (.branch 20 (.branch 19 (.leaf 3092113944) (.leaf 3010793921)) (.branch 21 (.leaf 2932309054) (.leaf 2856529683)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2783333384) (.leaf 2712604503)) (.branch 25 (.leaf 2644233715) (.leaf 2578117623))) (.branch 28 (.branch 27 (.leaf 2514158385) (.leaf 2452263366)) (.branch 29 (.leaf 2392344819) (.leaf 2334319584)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2278108809) (.branch 32 (.leaf 2223637696) (.leaf 2170835255))) (.branch 35 (.branch 34 (.leaf 2119634080) (.leaf 2069970143)) (.branch 36 (.leaf 2021782593) (.leaf 1975013576)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1929608063) (.leaf 1885513693)) (.branch 40 (.leaf 1842680615) (.leaf 1801061356))) (.branch 43 (.branch 42 (.leaf 1760610687) (.leaf 1721285497)) (.branch 44 (.leaf 1683044678) (.leaf 1645849019))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1609661101) (.branch 47 (.leaf 1574445202) (.leaf 1540167208))) (.branch 50 (.branch 49 (.leaf 1506794525) (.leaf 1474296001)) (.branch 51 (.leaf 1442641854) (.leaf 1411803594)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1381753962) (.leaf 1352466867)) (.branch 55 (.leaf 1323917323) (.leaf 1296081397))) (.branch 58 (.branch 57 (.leaf 1268936153) (.leaf 1242459606)) (.branch 59 (.leaf 1216630671) (.leaf 1191429122))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1166835547) (.branch 62 (.leaf 1142831312) (.leaf 1119398519))) (.branch 65 (.branch 64 (.leaf 1096519976) (.leaf 1074179157)) (.branch 66 (.leaf 1052360178) (.leaf 1031047759)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1010227203) (.leaf 989884363)) (.branch 70 (.leaf 970005620) (.leaf 950577858))) (.branch 73 (.branch 72 (.leaf 931588441) (.leaf 913025192)) (.branch 74 (.leaf 894876370) (.leaf 877130653))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 859777120) (.branch 77 (.leaf 842805232) (.leaf 826204813))) (.branch 80 (.branch 79 (.leaf 809966040) (.leaf 794079421)) (.branch 81 (.leaf 778535788) (.leaf 763326277)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 748442319) (.leaf 733875625)) (.branch 85 (.leaf 719618178) (.leaf 705662218))) (.branch 88 (.branch 87 (.leaf 692000234) (.leaf 678624952)) (.branch 89 (.leaf 665529328) (.leaf 652706535)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 640149959) (.branch 92 (.leaf 627853187) (.leaf 615810000))) (.branch 95 (.branch 94 (.leaf 604014368) (.leaf 592460438)) (.branch 96 (.leaf 581142532) (.leaf 570055136)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 559192899) (.leaf 548550623)) (.branch 100 (.leaf 538123257) (.leaf 527905894))) (.branch 103 (.branch 102 (.leaf 517893765) (.leaf 508082235)) (.branch 104 (.leaf 498466795) (.leaf 489043060))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 479806765) (.leaf 470753760)) (.branch 108 (.leaf 461880007) (.leaf 453181572))) (.branch 111 (.branch 110 (.leaf 444654629) (.leaf 436295450)) (.branch 112 (.leaf 428100402) (.leaf 420065950)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 412188646) (.leaf 404465131)) (.branch 116 (.leaf 396892131) (.leaf 389466453))) (.branch 119 (.branch 118 (.leaf 382184986) (.leaf 375044692)) (.branch 120 (.leaf 368042612) (.leaf 361175856)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 731).prefactor = (458309578226791/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 731).cutoff/(generalMeanRows 731).c)).2 =
    (408234231146061/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 731).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 731).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 731).q*(generalMeanRows 731).c/2-2 = (1453/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable239.value]
    have hcontinuation : (generalMeanRows 731).q*(generalMeanRows 731).cutoff/2-2 = (7898/3759:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable241.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 731).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 731

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 731).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 731).criticalRate j.val*(generalMeanRows 731).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 731).c*(generalMeanRows 731).criticalPoint j.val)).2-
      (generalMeanRows 731).J/2-(generalMeanRows 731).error (generalMeanGrid j.val)+
      (generalMeanRows 731).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 731).c)).2-
      (generalMeanRows 731).J/2-(generalMeanRows 731).error 4 := by
  have he : (generalMeanRows 731).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 731) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 731)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0731

/-! Kernel-checked entropy margins for general spectral rectangle 732. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0732
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5267491568) (.branch 2 (.leaf 5099883466) (.leaf 4939596909))) (.branch 5 (.branch 4 (.leaf 4786214515) (.leaf 4639348478)) (.branch 6 (.leaf 4498637987) (.leaf 4363746922)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4234361780) (.leaf 4110189833)) (.branch 10 (.leaf 3990957454) (.leaf 3876408613))) (.branch 13 (.branch 12 (.leaf 3766303518) (.leaf 3660417381)) (.branch 14 (.leaf 3558539294) (.leaf 3460471214))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3366027027) (.branch 17 (.leaf 3275031700) (.leaf 3187320502))) (.branch 20 (.branch 19 (.leaf 3102738291) (.leaf 3021138858)) (.branch 21 (.leaf 2942384320) (.leaf 2866344575)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2792896778) (.leaf 2721924876)) (.branch 25 (.leaf 2653319169) (.leaf 2586975905))) (.branch 28 (.branch 27 (.leaf 2522796906) (.leaf 2460689219)) (.branch 29 (.leaf 2400564795) (.leaf 2342340188)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2285936276) (.branch 32 (.leaf 2231278003) (.leaf 2178294135))) (.branch 35 (.branch 34 (.leaf 2126917036) (.leaf 2077082456)) (.branch 36 (.leaf 2028729336) (.leaf 1981799623)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1936238099) (.leaf 1891992223)) (.branch 40 (.leaf 1849011972) (.leaf 1807249712))) (.branch 43 (.branch 42 (.leaf 1766660057) (.leaf 1727199747)) (.branch 44 (.leaf 1688827535) (.leaf 1651504073))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1615191815) (.branch 47 (.leaf 1579854917) (.leaf 1545459145))) (.branch 50 (.branch 49 (.leaf 1511971795) (.leaf 1479361608)) (.branch 51 (.leaf 1447598698) (.leaf 1416654479)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1386501599) (.leaf 1357113875)) (.branch 55 (.leaf 1328466236) (.leaf 1300534667))) (.branch 58 (.branch 57 (.leaf 1273296154) (.leaf 1246728635)) (.branch 59 (.leaf 1220810953) (.leaf 1195522812))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1170844735) (.branch 62 (.leaf 1146758023) (.leaf 1123244716))) (.branch 65 (.branch 64 (.leaf 1100287563) (.leaf 1077869983)) (.branch 66 (.leaf 1055976034) (.leaf 1034590388)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1013698293) (.leaf 993285556)) (.branch 70 (.leaf 973338511) (.leaf 953843996))) (.branch 73 (.branch 72 (.leaf 934789332) (.leaf 916162300)) (.branch 74 (.leaf 897951120) (.leaf 880144430))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 862731271) (.branch 77 (.leaf 845701068) (.leaf 829043611))) (.branch 80 (.branch 79 (.leaf 812749042) (.leaf 796807838)) (.branch 81 (.leaf 781210798) (.leaf 765949028)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 751013929) (.leaf 736397185)) (.branch 85 (.leaf 722090750) (.leaf 708086838))) (.branch 88 (.branch 87 (.leaf 694377912) (.leaf 680956673)) (.branch 89 (.leaf 667816053) (.leaf 654949202)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 642349482) (.branch 92 (.leaf 630010459) (.leaf 617925892))) (.branch 95 (.branch 94 (.leaf 606089731) (.leaf 594496102)) (.branch 96 (.leaf 583139308) (.leaf 572013817)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 561114258) (.leaf 550435415)) (.branch 100 (.leaf 539972221) (.leaf 529719752))) (.branch 103 (.branch 102 (.leaf 519673222) (.leaf 509827980)) (.branch 104 (.leaf 500179501) (.leaf 490723387))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 481455357) (.leaf 472371247)) (.branch 108 (.leaf 463467003) (.leaf 454738681))) (.branch 111 (.branch 110 (.leaf 446182440) (.leaf 437794539)) (.branch 112 (.leaf 429571334) (.leaf 421509275)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 413604905) (.leaf 405854853)) (.branch 116 (.leaf 398255832) (.leaf 390804640))) (.branch 119 (.branch 118 (.leaf 383498154) (.leaf 376333327)) (.branch 120 (.leaf 369307188) (.leaf 362416838)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 732).prefactor = (4598843068214853/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 732).cutoff/(generalMeanRows 732).c)).2 =
    (408234231146061/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 732).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 732).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 732).q*(generalMeanRows 732).c/2-2 = (1453/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable239.value]
    have hcontinuation : (generalMeanRows 732).q*(generalMeanRows 732).cutoff/2-2 = (7898/3759:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable241.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 732).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 732

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 732).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 732).criticalRate j.val*(generalMeanRows 732).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 732).c*(generalMeanRows 732).criticalPoint j.val)).2-
      (generalMeanRows 732).J/2-(generalMeanRows 732).error (generalMeanGrid j.val)+
      (generalMeanRows 732).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 732).c)).2-
      (generalMeanRows 732).J/2-(generalMeanRows 732).error 4 := by
  have he : (generalMeanRows 732).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 732) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 732)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0732

/-! Kernel-checked entropy margins for general spectral rectangle 733. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0733
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5247884104) (.branch 2 (.leaf 5080893814) (.leaf 4921210779))) (.branch 5 (.branch 4 (.leaf 4768417502) (.leaf 4622126114)) (.branch 6 (.leaf 4481975781) (.leaf 4347630395)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4218776510) (.leaf 4095121477)) (.branch 10 (.leaf 3976391781) (.leaf 3862331530))) (.branch 13 (.branch 12 (.leaf 3752701091) (.leaf 3647275856)) (.branch 14 (.leaf 3545845115) (.leaf 3448211036))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3354187732) (.branch 17 (.leaf 3263600408) (.leaf 3176284580))) (.branch 20 (.branch 19 (.leaf 3092085362) (.leaf 3010856805)) (.branch 21 (.leaf 2932461295) (.leaf 2856769000)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2783657350) (.leaf 2713010567)) (.branch 25 (.leaf 2644719230) (.leaf 2578679862))) (.branch 28 (.branch 27 (.leaf 2514794562) (.leaf 2452970653)) (.branch 29 (.leaf 2393120359) (.leaf 2335160506)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2279012239) (.branch 32 (.leaf 2224600768) (.leaf 2171855120))) (.branch 35 (.branch 34 (.leaf 2120707916) (.leaf 2071095159)) (.branch 36 (.leaf 2022956040) (.leaf 1976232749)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1930870308) (.leaf 1886816407)) (.branch 40 (.leaf 1844021257) (.leaf 1802437444))) (.branch 43 (.branch 42 (.leaf 1762019801) (.leaf 1722725283)) (.branch 44 (.leaf 1684512849) (.leaf 1647343356))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1611179454) (.branch 47 (.leaf 1575985489) (.leaf 1541727416))) (.branch 50 (.branch 49 (.leaf 1508372711) (.leaf 1475890293)) (.branch 51 (.leaf 1444250446) (.leaf 1413424749)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1383386012) (.leaf 1354108209)) (.branch 55 (.leaf 1325566419) (.leaf 1297736773))) (.branch 58 (.branch 57 (.leaf 1270596401) (.leaf 1244123376)) (.branch 59 (.leaf 1218296676) (.leaf 1193096133))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1168502394) (.branch 62 (.leaf 1144496879) (.leaf 1121061746))) (.branch 65 (.branch 64 (.leaf 1098179855) (.leaf 1075834733)) (.branch 66 (.leaf 1054010545) (.leaf 1032692061)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1011864629) (.leaf 991514149)) (.branch 70 (.leaf 971627044) (.leaf 952190243))) (.branch 73 (.branch 72 (.leaf 933191149) (.leaf 914617624)) (.branch 74 (.leaf 896457966) (.leaf 878700891))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 861335512) (.branch 77 (.leaf 844351323) (.leaf 827738182))) (.branch 80 (.branch 79 (.leaf 811486295) (.leaf 795586203)) (.branch 81 (.leaf 780028765) (.leaf 764805144)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 749906799) (.leaf 735325465)) (.branch 85 (.leaf 721053150) (.leaf 707082117))) (.branch 88 (.branch 87 (.leaf 693404875) (.leaf 680014174)) (.branch 89 (.leaf 666902987) (.leaf 654064509)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 641492143) (.branch 92 (.leaf 629179492) (.leaf 617120355))) (.branch 95 (.branch 94 (.leaf 605308717) (.leaf 593738741)) (.branch 96 (.leaf 582404760) (.leaf 571301278)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 560422952) (.leaf 549764598)) (.branch 100 (.leaf 539321176) (.leaf 529087790))) (.branch 103 (.branch 102 (.leaf 519059681) (.leaf 509232222)) (.branch 104 (.leaf 499600915) (.leaf 490161382))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 480909367) (.leaf 471840726)) (.branch 108 (.leaf 462951428) (.leaf 454237547))) (.branch 111 (.branch 110 (.leaf 445695261) (.leaf 437320848)) (.branch 112 (.leaf 429110682) (.leaf 421061230)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 413169050) (.leaf 405430787)) (.branch 116 (.leaf 397843170) (.leaf 390403012))) (.branch 119 (.branch 118 (.leaf 383107201) (.leaf 375952706)) (.branch 120 (.leaf 368936567) (.leaf 362055899)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 733).prefactor = (2297749990608629/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 733).cutoff/(generalMeanRows 733).c)).2 =
    (411031435767121/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 733).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 733).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 733).q*(generalMeanRows 733).c/2-2 = (1453/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable239.value]
    have hcontinuation : (generalMeanRows 733).q*(generalMeanRows 733).cutoff/2-2 = (15838/7497:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable242.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 733).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 733

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 733).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 733).criticalRate j.val*(generalMeanRows 733).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 733).c*(generalMeanRows 733).criticalPoint j.val)).2-
      (generalMeanRows 733).J/2-(generalMeanRows 733).error (generalMeanGrid j.val)+
      (generalMeanRows 733).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 733).c)).2-
      (generalMeanRows 733).J/2-(generalMeanRows 733).error 4 := by
  have he : (generalMeanRows 733).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 733) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 733)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0733

/-! Kernel-checked entropy margins for general spectral rectangle 734. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0734
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5265766644) (.branch 2 (.leaf 5098207323) (.leaf 4937980156))) (.branch 5 (.branch 4 (.leaf 4784666226) (.leaf 4637876339)) (.branch 6 (.leaf 4497248433) (.leaf 4362445257)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4233152292) (.leaf 4109075896)) (.branch 10 (.leaf 3989941620) (.leaf 3875492701))) (.branch 13 (.branch 12 (.leaf 3765488688) (.leaf 3659704209)) (.branch 14 (.leaf 3557927835) (.leaf 3459961061))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3365617366) (.branch 17 (.leaf 3274721360) (.leaf 3187107997))) (.branch 20 (.branch 19 (.leaf 3102621864) (.leaf 3021116514)) (.branch 21 (.leaf 2942453867) (.leaf 2866503644)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2793142861) (.leaf 2722255345)) (.branch 25 (.leaf 2653731299) (.leaf 2587466898))) (.branch 28 (.branch 27 (.leaf 2523363904) (.leaf 2461329326)) (.branch 29 (.leaf 2401275088) (.leaf 2343117732)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2286778136) (.branch 32 (.leaf 2232181254) (.leaf 2179255871))) (.branch 35 (.branch 34 (.leaf 2127934380) (.leaf 2078152564)) (.branch 36 (.leaf 2029849407) (.leaf 1982966903)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1937449886) (.leaf 1893245869)) (.branch 40 (.leaf 1850304891) (.leaf 1808579378))) (.branch 43 (.branch 42 (.leaf 1768024010) (.leaf 1728595593)) (.branch 44 (.leaf 1690252947) (.leaf 1652956797))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1616669663) (.branch 47 (.leaf 1581355772) (.leaf 1546980962))) (.branch 50 (.branch 49 (.leaf 1513512599) (.leaf 1480919495)) (.branch 51 (.leaf 1449171832) (.leaf 1418241095)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1388099999) (.leaf 1358722429)) (.branch 55 (.leaf 1330083381) (.leaf 1302158904))) (.branch 58 (.branch 57 (.leaf 1274926049) (.leaf 1248362816)) (.branch 59 (.leaf 1222448109) (.leaf 1197161694))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1172484149) (.branch 62 (.leaf 1148396833) (.leaf 1124881844))) (.branch 65 (.branch 64 (.leaf 1101921981) (.leaf 1079500717)) (.branch 66 (.leaf 1057602162) (.leaf 1036211033)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1015312630) (.leaf 994892804)) (.branch 70 (.leaf 974937933) (.leaf 955434899))) (.branch 73 (.branch 72 (.leaf 936371064) (.leaf 917734249)) (.branch 74 (.leaf 899512711) (.leaf 881695127))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 864270574) (.branch 77 (.leaf 847228510) (.leaf 830558759))) (.branch 80 (.branch 79 (.leaf 814251493) (.leaf 798297220)) (.branch 81 (.leaf 782686769) (.leaf 767411273)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 752462160) (.leaf 737831140)) (.branch 85 (.leaf 723510190) (.leaf 709491549))) (.branch 88 (.branch 87 (.leaf 695767702) (.leaf 682331371)) (.branch 89 (.leaf 669175507) (.leaf 656293281)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 643678073) (.branch 92 (.leaf 631323466) (.leaf 619223237))) (.branch 95 (.branch 94 (.leaf 607371350) (.leaf 595761948)) (.branch 96 (.leaf 584389346) (.leaf 573248027)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 562332633) (.leaf 551637960)) (.branch 100 (.leaf 541158951) (.leaf 530890694))) (.branch 103 (.branch 102 (.leaf 520828414) (.leaf 510967468)) (.branch 104 (.leaf 501303341) (.leaf 491831642))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 482548100) (.leaf 473448557)) (.branch 108 (.leaf 464528968) (.leaf 455785394))) (.branch 111 (.branch 110 (.leaf 447214000) (.leaf 438811050)) (.branch 112 (.leaf 430572907) (.leaf 422496026)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 414576953) (.leaf 406812321)) (.branch 116 (.leaf 399198849) (.leaf 391733338))) (.branch 119 (.branch 118 (.leaf 384412666) (.leaf 377233791)) (.branch 120 (.leaf 370193745) (.leaf 363289630)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 734).prefactor = (2305579737906931/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 734).cutoff/(generalMeanRows 734).c)).2 =
    (411031435767121/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 734).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 734).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 734).q*(generalMeanRows 734).c/2-2 = (1453/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable239.value]
    have hcontinuation : (generalMeanRows 734).q*(generalMeanRows 734).cutoff/2-2 = (15838/7497:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable242.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 734).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 734

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 734).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 734).criticalRate j.val*(generalMeanRows 734).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 734).c*(generalMeanRows 734).criticalPoint j.val)).2-
      (generalMeanRows 734).J/2-(generalMeanRows 734).error (generalMeanGrid j.val)+
      (generalMeanRows 734).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 734).c)).2-
      (generalMeanRows 734).J/2-(generalMeanRows 734).error 4 := by
  have he : (generalMeanRows 734).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 734) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 734)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0734

/-! Kernel-checked entropy margins for general spectral rectangle 735. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0735
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5198071306) (.branch 2 (.leaf 5030211937) (.leaf 4869710010))) (.branch 5 (.branch 4 (.leaf 4716146562) (.leaf 4569132289)) (.branch 6 (.leaf 4428304957) (.leaf 4293327092)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4163883905) (.leaf 4039681440)) (.branch 10 (.leaf 3920444897) (.leaf 3805917128))) (.branch 13 (.branch 12 (.leaf 3695857269) (.leaf 3590039506)) (.branch 14 (.leaf 3488251950) (.leaf 3390295613))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3295983478) (.branch 17 (.leaf 3205139641) (.leaf 3117598537))) (.branch 20 (.branch 19 (.leaf 3033204219) (.leaf 2951809704)) (.branch 21 (.leaf 2873276367) (.leaf 2797473383)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2724277219) (.leaf 2653571155)) (.branch 25 (.leaf 2585244847) (.leaf 2519193921))) (.branch 28 (.branch 27 (.leaf 2455319601) (.leaf 2393528355)) (.branch 29 (.leaf 2333731576) (.leaf 2275845277)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2219789816) (.branch 32 (.leaf 2165489633) (.leaf 2112873007))) (.branch 35 (.branch 34 (.leaf 2061871831) (.leaf 2012421401)) (.branch 36 (.leaf 1964460218) (.leaf 1917929804)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1872774530) (.leaf 1828941457)) (.branch 40 (.leaf 1786380180) (.leaf 1745042691))) (.branch 43 (.branch 42 (.leaf 1704883246) (.leaf 1665858238)) (.branch 44 (.leaf 1627926083) (.leaf 1591047110))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1555183459) (.branch 47 (.leaf 1520298982) (.leaf 1486359152))) (.branch 50 (.branch 49 (.leaf 1453330982) (.leaf 1421182939)) (.branch 51 (.leaf 1389884874) (.leaf 1359407943)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1329724548) (.leaf 1300808268)) (.branch 55 (.leaf 1272633803) (.leaf 1245176914))) (.branch 58 (.branch 57 (.leaf 1218414373) (.leaf 1192323911)) (.branch 59 (.leaf 1166884172) (.leaf 1142074667))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1117875733) (.branch 62 (.leaf 1094268491) (.leaf 1071234810))) (.branch 65 (.branch 64 (.leaf 1048757272) (.leaf 1026819136)) (.branch 66 (.leaf 1005404306) (.leaf 984497303)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 964083236) (.leaf 944147772)) (.branch 70 (.leaf 924677113) (.leaf 905657971))) (.branch 73 (.branch 72 (.leaf 887077543) (.leaf 868923495)) (.branch 74 (.leaf 851183931) (.leaf 833847385))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 816902792) (.branch 77 (.leaf 800339478) (.leaf 784147139))) (.branch 80 (.branch 79 (.leaf 768315824) (.leaf 752835924)) (.branch 81 (.leaf 737698154) (.leaf 722893541)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 708413411) (.leaf 694249373)) (.branch 85 (.leaf 680393314) (.leaf 666837381))) (.branch 88 (.branch 87 (.leaf 653573975) (.leaf 640595737)) (.branch 89 (.leaf 627895542) (.leaf 615466487)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 603301884) (.branch 92 (.leaf 591395248) (.leaf 579740297))) (.branch 95 (.branch 94 (.leaf 568330933) (.leaf 557161246)) (.branch 96 (.leaf 546225498) (.leaf 535518123)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 525033717) (.leaf 514767031)) (.branch 100 (.leaf 504712971) (.leaf 494866584))) (.branch 103 (.branch 102 (.leaf 485223061) (.leaf 475777726)) (.branch 104 (.leaf 466526035) (.leaf 457463569))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 448586029) (.leaf 439889237)) (.branch 108 (.leaf 431369123) (.leaf 423021732))) (.branch 111 (.branch 110 (.leaf 414843209) (.leaf 406829806)) (.branch 112 (.leaf 398977869) (.leaf 391283843)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 383744263) (.leaf 376355755)) (.branch 116 (.leaf 369115029) (.leaf 362018881))) (.branch 119 (.branch 118 (.leaf 355064187) (.leaf 348247901)) (.branch 120 (.leaf 341567052) (.leaf 335018746)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 735).prefactor = (4614644461042061/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 735).cutoff/(generalMeanRows 735).c)).2 =
    (400743559416903/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 735).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 735).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 735).q*(generalMeanRows 735).c/2-2 = (747/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable220.value]
    have hcontinuation : (generalMeanRows 735).q*(generalMeanRows 735).cutoff/2-2 = (7898/3759:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable241.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 735).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 735

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 735).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 735).criticalRate j.val*(generalMeanRows 735).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 735).c*(generalMeanRows 735).criticalPoint j.val)).2-
      (generalMeanRows 735).J/2-(generalMeanRows 735).error (generalMeanGrid j.val)+
      (generalMeanRows 735).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 735).c)).2-
      (generalMeanRows 735).J/2-(generalMeanRows 735).error 4 := by
  have he : (generalMeanRows 735).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 735) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 735)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0735

/-! Kernel-checked entropy margins for general spectral rectangle 736. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0736
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5129978602) (.branch 2 (.leaf 4961903523) (.leaf 4801221521))) (.branch 5 (.branch 4 (.leaf 4647512017) (.leaf 4500384177)) (.branch 6 (.leaf 4359474319) (.leaf 4224443586)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4094975877) (.leaf 3970775985)) (.branch 10 (.leaf 3851567918) (.leaf 3737093386))) (.branch 13 (.branch 12 (.leaf 3627110437) (.leaf 3521392214)) (.branch 14 (.leaf 3419725829) (.leaf 3321911337))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3227760802) (.branch 17 (.leaf 3137097440) (.leaf 3049754838))) (.branch 20 (.branch 19 (.leaf 2965576235) (.leaf 2884413866)) (.branch 21 (.leaf 2806128351) (.leaf 2730588144)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2657669012) (.leaf 2587253561)) (.branch 25 (.leaf 2519230801) (.leaf 2453495733))) (.branch 28 (.branch 27 (.leaf 2389948978) (.leaf 2328496425)) (.branch 29 (.leaf 2269048904) (.leaf 2211521889)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2155835215) (.branch 32 (.leaf 2101912820) (.leaf 2049682495))) (.branch 35 (.branch 34 (.leaf 1999075664) (.leaf 1950027171)) (.branch 36 (.leaf 1902475078) (.leaf 1856360485)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1811627355) (.leaf 1768222354)) (.branch 40 (.leaf 1726094698) (.leaf 1685196011))) (.branch 43 (.branch 42 (.leaf 1645480193) (.leaf 1606903295)) (.branch 44 (.leaf 1569423403) (.leaf 1533000527))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1497596497) (.branch 47 (.leaf 1463174868) (.leaf 1429700827))) (.branch 50 (.branch 49 (.leaf 1397141109) (.leaf 1365463913)) (.branch 51 (.leaf 1334638832) (.leaf 1304636775)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1275429902) (.leaf 1246991562)) (.branch 55 (.leaf 1219296230) (.leaf 1192319454))) (.branch 58 (.branch 57 (.leaf 1166037798) (.leaf 1140428794)) (.branch 59 (.leaf 1115470894) (.leaf 1091143423))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1067426539) (.branch 62 (.leaf 1044301194) (.leaf 1021749092))) (.branch 65 (.branch 64 (.leaf 999752655) (.leaf 978294990)) (.branch 66 (.leaf 957359855) (.leaf 936931632)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 916995291) (.leaf 897536373)) (.branch 70 (.leaf 878540954) (.leaf 859995628))) (.branch 73 (.branch 72 (.leaf 841887477) (.leaf 824204057)) (.branch 74 (.leaf 806933370) (.leaf 790063847))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 773584329) (.branch 77 (.leaf 757484050) (.leaf 741752617))) (.branch 80 (.branch 79 (.leaf 726379999) (.leaf 711356506)) (.branch 81 (.leaf 696672777) (.leaf 682319767)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 668288734) (.leaf 654571222)) (.branch 85 (.leaf 641159056) (.leaf 628044325))) (.branch 88 (.branch 87 (.leaf 615219375) (.leaf 602676793)) (.branch 89 (.leaf 590409407) (.leaf 578410266)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 566672638) (.branch 92 (.leaf 555189999) (.leaf 543956025))) (.branch 95 (.branch 94 (.leaf 532964586) (.leaf 522209735)) (.branch 96 (.leaf 511685705) (.leaf 501386900)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 491307889) (.leaf 481443400)) (.branch 100 (.leaf 471788313) (.leaf 462337658))) (.branch 103 (.branch 102 (.leaf 453086605) (.leaf 444030462)) (.branch 104 (.leaf 435164670) (.leaf 426484795))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 417986528) (.leaf 409665680)) (.branch 108 (.leaf 401518174) (.leaf 393540045))) (.branch 111 (.branch 110 (.leaf 385727436) (.leaf 378076590)) (.branch 112 (.leaf 370583855) (.leaf 363245671)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 356058574) (.leaf 349019191)) (.branch 116 (.leaf 342124233) (.leaf 335370500))) (.branch 119 (.branch 118 (.leaf 328754871) (.leaf 322274306)) (.branch 120 (.leaf 315925841) (.leaf 309706587)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 736).prefactor = (115762503666451/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 736).cutoff/(generalMeanRows 736).c)).2 =
    (49163572616173/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 736).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 736).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 736).q*(generalMeanRows 736).c/2-2 = (307/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable081.value]
    have hcontinuation : (generalMeanRows 736).q*(generalMeanRows 736).cutoff/2-2 = (7898/3759:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable241.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 736).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 736

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 736).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 736).criticalRate j.val*(generalMeanRows 736).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 736).c*(generalMeanRows 736).criticalPoint j.val)).2-
      (generalMeanRows 736).J/2-(generalMeanRows 736).error (generalMeanGrid j.val)+
      (generalMeanRows 736).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 736).c)).2-
      (generalMeanRows 736).J/2-(generalMeanRows 736).error 4 := by
  have he : (generalMeanRows 736).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 736) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 736)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0736

/-! Kernel-checked entropy margins for general spectral rectangle 737. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0737
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5002889358) (.branch 2 (.leaf 4834390394) (.leaf 4673332916))) (.branch 5 (.branch 4 (.leaf 4519296089) (.leaf 4371888711)) (.branch 6 (.leaf 4230746622) (.leaf 4095530401)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3965923294) (.leaf 3841629369)) (.branch 10 (.leaf 3722371842) (.leaf 3607891575))) (.branch 13 (.branch 12 (.leaf 3497945719) (.leaf 3392306472)) (.branch 14 (.leaf 3290759968) (.leaf 3193105251))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3099153350) (.branch 17 (.leaf 3008726421) (.leaf 2921656978))) (.branch 20 (.branch 19 (.leaf 2837787174) (.leaf 2756968148)) (.branch 21 (.leaf 2679059420) (.leaf 2603928341)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2531449576) (.leaf 2461504633)) (.branch 25 (.leaf 2393981428) (.leaf 2328773877))) (.branch 28 (.branch 27 (.leaf 2265781525) (.leaf 2204909195)) (.branch 29 (.leaf 2146066667) (.leaf 2089168377)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2034133137) (.branch 32 (.leaf 1980883877) (.leaf 1929347401))) (.branch 35 (.branch 34 (.leaf 1879454161) (.leaf 1831138048)) (.branch 36 (.leaf 1784336191) (.leaf 1738988777)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1695038876) (.leaf 1652432279)) (.branch 40 (.leaf 1611117350) (.leaf 1571044882))) (.branch 43 (.branch 42 (.leaf 1532167963) (.leaf 1494441856)) (.branch 44 (.leaf 1457823876) (.leaf 1422273285))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1387751186) (.branch 47 (.leaf 1354220428) (.leaf 1321645511))) (.branch 50 (.branch 49 (.leaf 1289992504) (.leaf 1259228962)) (.branch 51 (.leaf 1229323850) (.leaf 1200247472)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1171971401) (.leaf 1144468418)) (.branch 55 (.leaf 1117712450) (.leaf 1091678512))) (.branch 58 (.branch 57 (.leaf 1066342658) (.leaf 1041681923)) (.branch 59 (.leaf 1017674282) (.leaf 994298601))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 971534593) (.branch 62 (.leaf 949362783) (.leaf 927764462))) (.branch 65 (.branch 64 (.leaf 906721658) (.leaf 886217096)) (.branch 66 (.leaf 866234169) (.leaf 846756907)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 827769944) (.leaf 809258495)) (.branch 70 (.leaf 791208329) (.leaf 773605739))) (.branch 73 (.branch 72 (.leaf 756437527) (.leaf 739690974)) (.branch 74 (.leaf 723353823) (.leaf 707414256))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 691860877) (.branch 77 (.leaf 676682695) (.leaf 661869101))) (.branch 80 (.branch 79 (.leaf 647409857) (.leaf 633295081)) (.branch 81 (.leaf 619515225) (.leaf 606061070)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 592923705) (.leaf 580094518)) (.branch 85 (.leaf 567565184) (.leaf 555327652))) (.branch 88 (.branch 87 (.leaf 543374133) (.leaf 531697093)) (.branch 89 (.leaf 520289237) (.leaf 509143508)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 498253070) (.branch 92 (.leaf 487611302) (.leaf 477211790))) (.branch 95 (.branch 94 (.leaf 467048321) (.leaf 457114870)) (.branch 96 (.leaf 447405599) (.leaf 437914847)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 428637120) (.leaf 419567094)) (.branch 100 (.leaf 410699598) (.leaf 402029616))) (.branch 103 (.branch 102 (.leaf 393552280) (.leaf 385262860)) (.branch 104 (.leaf 377156766) (.leaf 369229539))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 361476845) (.leaf 353894477)) (.branch 108 (.leaf 346478341) (.leaf 339224462))) (.branch 111 (.branch 110 (.leaf 332128972) (.leaf 325188113)) (.branch 112 (.leaf 318398228) (.leaf 311755760)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 305257249) (.leaf 298899327)) (.branch 116 (.leaf 292678717) (.leaf 286592230))) (.branch 119 (.branch 118 (.leaf 280636760) (.leaf 274809284)) (.branch 120 (.leaf 269106858) (.leaf 263526613)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 737).prefactor = (1159456169529859/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 737).cutoff/(generalMeanRows 737).c)).2 =
    (74606277698047/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 737).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 737).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 737).q*(generalMeanRows 737).c/2-2 = (1617/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable243.value]
    have hcontinuation : (generalMeanRows 737).q*(generalMeanRows 737).cutoff/2-2 = (1964/945:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable237.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 737).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 737

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 737).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 737).criticalRate j.val*(generalMeanRows 737).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 737).c*(generalMeanRows 737).criticalPoint j.val)).2-
      (generalMeanRows 737).J/2-(generalMeanRows 737).error (generalMeanGrid j.val)+
      (generalMeanRows 737).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 737).c)).2-
      (generalMeanRows 737).J/2-(generalMeanRows 737).error 4 := by
  have he : (generalMeanRows 737).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 737) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 737)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0737

/-! Kernel-checked entropy margins for general spectral rectangle 738. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0738
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5149874540) (.branch 2 (.leaf 4981172367) (.leaf 4819877900))) (.branch 5 (.branch 4 (.leaf 4665570647) (.leaf 4517859822)) (.branch 6 (.leaf 4376381744) (.leaf 4240797526)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4110790999) (.leaf 3986066860)) (.branch 10 (.leaf 3866348993) (.leaf 3751378960))) (.branch 13 (.branch 12 (.leaf 3640914640) (.leaf 3534728986)) (.branch 14 (.leaf 3432608905) (.leaf 3334354232))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3239776797) (.branch 17 (.leaf 3148699574) (.leaf 3060955895))) (.branch 20 (.branch 19 (.leaf 2976388740) (.leaf 2894850077)) (.branch 21 (.leaf 2816200255) (.leaf 2740307452)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2667047156) (.leaf 2596301697)) (.branch 25 (.leaf 2527959801) (.leaf 2461916192))) (.branch 28 (.branch 27 (.leaf 2398071209) (.leaf 2336330463)) (.branch 29 (.leaf 2276604510) (.leaf 2218808549)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2162862146) (.branch 32 (.leaf 2108688968) (.leaf 2056216547))) (.branch 35 (.branch 34 (.leaf 2005376045) (.leaf 1956102051)) (.branch 36 (.leaf 1908332377) (.leaf 1862007878)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1817072275) (.leaf 1773471997)) (.branch 40 (.leaf 1731156031) (.leaf 1690075774))) (.branch 43 (.branch 42 (.leaf 1650184908) (.leaf 1611439267)) (.branch 44 (.leaf 1573796729) (.leaf 1537217098))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1501662006) (.branch 47 (.leaf 1467094815) (.leaf 1433480523))) (.branch 50 (.branch 49 (.leaf 1400785682) (.leaf 1368978315)) (.branch 51 (.leaf 1338027840) (.leaf 1307905000)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1278581792) (.leaf 1250031407)) (.branch 55 (.leaf 1222228169) (.leaf 1195147476))) (.branch 58 (.branch 57 (.leaf 1168765750) (.leaf 1143060383)) (.branch 59 (.leaf 1118009693) (.leaf 1093592876))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1069789965) (.branch 62 (.leaf 1046581788) (.leaf 1023949933))) (.branch 65 (.branch 64 (.leaf 1001876708) (.leaf 980345110)) (.branch 66 (.leaf 959338793) (.leaf 938842034)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 918839708) (.leaf 899317257)) (.branch 70 (.leaf 880260667) (.leaf 861656442))) (.branch 73 (.branch 72 (.leaf 843491580) (.leaf 825753554)) (.branch 74 (.leaf 808430286) (.leaf 791510131))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 774981857) (.branch 77 (.leaf 758834624) (.leaf 743057974))) (.branch 80 (.branch 79 (.leaf 727641807) (.leaf 712576370)) (.branch 81 (.leaf 697852242) (.leaf 683460319)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 669391800) (.leaf 655638178)) (.branch 85 (.leaf 642191222) (.leaf 629042972))) (.branch 88 (.branch 87 (.leaf 616185724) (.leaf 603612022)) (.branch 89 (.leaf 591314644) (.leaf 579286598)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 567521110) (.branch 92 (.leaf 556011616) (.leaf 544751754))) (.branch 95 (.branch 94 (.leaf 533735356) (.leaf 522956440)) (.branch 96 (.leaf 512409204) (.leaf 502088020)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 491987424) (.leaf 482102115)) (.branch 100 (.leaf 472426943) (.leaf 462956910))) (.branch 103 (.branch 102 (.leaf 453687159) (.leaf 444612972)) (.branch 104 (.leaf 435729764) (.leaf 427033080))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 418518586) (.leaf 410182070)) (.branch 108 (.leaf 402019434) (.leaf 394026695))) (.branch 111 (.branch 110 (.leaf 386199973) (.leaf 378535495)) (.branch 112 (.leaf 371029588) (.leaf 363678678)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 356479282) (.leaf 349428011)) (.branch 116 (.leaf 342521562) (.leaf 335756718))) (.branch 119 (.branch 118 (.leaf 329130346) (.leaf 322639391)) (.branch 120 (.leaf 316280876) (.leaf 310051899)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 738).prefactor = (2317075214562879/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 738).cutoff/(generalMeanRows 738).c)).2 =
    (97629794710451/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 738).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 738).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 738).q*(generalMeanRows 738).c/2-2 = (307/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable081.value]
    have hcontinuation : (generalMeanRows 738).q*(generalMeanRows 738).cutoff/2-2 = (15754/7539:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable244.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 738).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 738

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 738).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 738).criticalRate j.val*(generalMeanRows 738).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 738).c*(generalMeanRows 738).criticalPoint j.val)).2-
      (generalMeanRows 738).J/2-(generalMeanRows 738).error (generalMeanGrid j.val)+
      (generalMeanRows 738).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 738).c)).2-
      (generalMeanRows 738).J/2-(generalMeanRows 738).error 4 := by
  have he : (generalMeanRows 738).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 738) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 738)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0738

/-! Kernel-checked entropy margins for general spectral rectangle 739. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0739
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5083163178) (.branch 2 (.leaf 4914274721) (.leaf 4752829569))) (.branch 5 (.branch 4 (.leaf 4598405570) (.leaf 4450610362)) (.branch 6 (.leaf 4309078773) (.leaf 4173470497)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4043468018) (.leaf 3918774748)) (.branch 10 (.leaf 3799113347) (.leaf 3684224209))) (.branch 13 (.branch 12 (.leaf 3573864097) (.leaf 3467804897)) (.branch 14 (.leaf 3365832495) (.leaf 3267745747))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3173355547) (.branch 17 (.leaf 3082483967) (.leaf 2994963480))) (.branch 20 (.branch 19 (.leaf 2910636236) (.leaf 2829353406)) (.branch 21 (.leaf 2750974576) (.leaf 2675367186)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2602406020) (.leaf 2531972722)) (.branch 25 (.leaf 2463955368) (.leaf 2398248046))) (.branch 28 (.branch 27 (.leaf 2334750491) (.leaf 2273367726)) (.branch 29 (.leaf 2214009742) (.leaf 2156591197)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2101031130) (.branch 32 (.leaf 2047252705) (.leaf 1995182964))) (.branch 35 (.branch 34 (.leaf 1944752603) (.leaf 1895895754)) (.branch 36 (.leaf 1848549794) (.leaf 1802655156)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1758155156) (.leaf 1714995831)) (.branch 40 (.leaf 1673125788) (.leaf 1632496063))) (.branch 43 (.branch 42 (.leaf 1593059983) (.leaf 1554773047)) (.branch 44 (.leaf 1517592803) (.leaf 1481478743))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1446392194) (.branch 47 (.leaf 1412296225) (.leaf 1379155554))) (.branch 50 (.branch 49 (.leaf 1346936460) (.leaf 1315606706)) (.branch 51 (.leaf 1285135456) (.leaf 1255493212)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1226651737) (.leaf 1198583997)) (.branch 55 (.leaf 1171264100) (.leaf 1144667236))) (.branch 58 (.branch 57 (.leaf 1118769626) (.leaf 1093548471)) (.branch 59 (.leaf 1068981903) (.leaf 1045048941))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1021729446) (.branch 62 (.leaf 999004085) (.leaf 976854285))) (.branch 65 (.branch 64 (.leaf 955262206) (.leaf 934210700)) (.branch 66 (.leaf 913683281) (.leaf 893664093)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 874137885) (.leaf 855089976)) (.branch 70 (.leaf 836506237) (.leaf 818373060))) (.branch 73 (.branch 72 (.leaf 800677336) (.leaf 783406437)) (.branch 74 (.leaf 766548188) (.leaf 750090851))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 734023105) (.branch 77 (.leaf 718334030) (.leaf 703013084))) (.branch 80 (.branch 79 (.leaf 688050094) (.leaf 673435234)) (.branch 81 (.leaf 659159015) (.leaf 645212269)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 631586133) (.leaf 618272043)) (.branch 85 (.leaf 605261713) (.leaf 592547133))) (.branch 88 (.branch 87 (.leaf 580120550) (.leaf 567974461)) (.branch 89 (.leaf 556101605) (.leaf 544494948)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 533147681) (.branch 92 (.leaf 522053204) (.leaf 511205124))) (.branch 95 (.branch 94 (.leaf 500597243) (.leaf 490223553)) (.branch 96 (.leaf 480078226) (.leaf 470155612)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 460450227) (.leaf 450956750)) (.branch 100 (.leaf 441670017) (.leaf 432585013))) (.branch 103 (.branch 102 (.leaf 423696869) (.leaf 415000856)) (.branch 104 (.leaf 406492380) (.leaf 398166977))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 390020309) (.leaf 382048158)) (.branch 108 (.leaf 374246423) (.leaf 366611119))) (.branch 111 (.branch 110 (.leaf 359138365) (.leaf 351824391)) (.branch 112 (.leaf 344665526) (.leaf 337658196)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 330798926) (.leaf 324084331)) (.branch 116 (.leaf 317511116) (.leaf 311076071))) (.branch 119 (.branch 118 (.leaf 304776071) (.leaf 298608071)) (.branch 120 (.leaf 292569105) (.leaf 286656282)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 739).prefactor = (465020657159403/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 739).cutoff/(generalMeanRows 739).c)).2 =
    (47892383943023/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 739).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 739).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 739).q*(generalMeanRows 739).c/2-2 = (197/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable218.value]
    have hcontinuation : (generalMeanRows 739).q*(generalMeanRows 739).cutoff/2-2 = (15754/7539:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable244.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 739).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 739

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 739).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 739).criticalRate j.val*(generalMeanRows 739).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 739).c*(generalMeanRows 739).criticalPoint j.val)).2-
      (generalMeanRows 739).J/2-(generalMeanRows 739).error (generalMeanGrid j.val)+
      (generalMeanRows 739).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 739).c)).2-
      (generalMeanRows 739).J/2-(generalMeanRows 739).error 4 := by
  have he : (generalMeanRows 739).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 739) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 739)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0739

/-! Kernel-checked entropy margins for general spectral rectangle 740. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0740
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5103268992) (.branch 2 (.leaf 4933748692) (.leaf 4771686424))) (.branch 5 (.branch 4 (.leaf 4616660117) (.leaf 4468277448)) (.branch 6 (.leaf 4326173240) (.leaf 4190007150)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4059461592) (.leaf 3934239878)) (.branch 10 (.leaf 3814064540) (.leaf 3698675823))) (.branch 13 (.branch 12 (.leaf 3587830316) (.leaf 3481299718)) (.branch 14 (.leaf 3378869705) (.leaf 3280338915))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3185518006) (.branch 17 (.leaf 3094228808) (.leaf 3006303539))) (.branch 20 (.branch 19 (.leaf 2921584090) (.leaf 2839921365)) (.branch 21 (.leaf 2761174679) (.leaf 2685211197)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2611905424) (.leaf 2541138727)) (.branch 25 (.leaf 2472798900) (.leaf 2406779754))) (.branch 28 (.branch 27 (.leaf 2342980742) (.leaf 2281306611)) (.branch 29 (.leaf 2221667077) (.leaf 2163976522)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2108153716) (.branch 32 (.leaf 2054121557) (.leaf 2001806823))) (.branch 35 (.branch 34 (.leaf 1951139950) (.leaf 1902054816)) (.branch 36 (.leaf 1854488547) (.leaf 1808381330)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1763676239) (.leaf 1720319077)) (.branch 40 (.leaf 1678258219) (.leaf 1637444475))) (.branch 43 (.branch 42 (.leaf 1597830952) (.leaf 1559372933)) (.branch 44 (.leaf 1522027757) (.leaf 1485754711))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1450514922) (.branch 47 (.leaf 1416271267) (.leaf 1382988273))) (.branch 50 (.branch 49 (.leaf 1350632037) (.leaf 1319170142)) (.branch 51 (.leaf 1288571581) (.leaf 1258806686)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1229847059) (.leaf 1201665506)) (.branch 55 (.leaf 1174235981) (.leaf 1147533527))) (.branch 58 (.branch 57 (.leaf 1121534220) (.leaf 1096215122)) (.branch 59 (.leaf 1071554229) (.leaf 1047530431))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1024123461) (.branch 62 (.leaf 1001313862) (.leaf 979082947))) (.branch 65 (.branch 64 (.leaf 957412759) (.leaf 936286040)) (.branch 66 (.leaf 915686197) (.leaf 895597272)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 876003912) (.leaf 856891343)) (.branch 70 (.leaf 838245341) (.leaf 820052210))) (.branch 73 (.branch 72 (.leaf 802298754) (.leaf 784972261)) (.branch 74 (.leaf 768060477) (.leaf 751551586))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 735434193) (.branch 77 (.leaf 719697304) (.leaf 704330310))) (.branch 80 (.branch 79 (.leaf 689322971) (.leaf 674665395)) (.branch 81 (.leaf 660348033) (.leaf 646361655)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 632697343) (.leaf 619346475)) (.branch 85 (.leaf 606300715) (.leaf 593551998))) (.branch 88 (.branch 87 (.leaf 581092524) (.leaf 568914743)) (.branch 89 (.leaf 557011346) (.leaf 545375258)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 533999624) (.branch 92 (.leaf 522877806) (.leaf 512003371))) (.branch 95 (.branch 94 (.leaf 501370084) (.leaf 490971899)) (.branch 96 (.leaf 480802956) (.leaf 470857569)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 461130223) (.leaf 451615565)) (.branch 100 (.leaf 442308402) (.leaf 433203690))) (.branch 103 (.branch 102 (.leaf 424296533) (.leaf 415582176)) (.branch 104 (.leaf 407055999) (.leaf 398713513))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 390550357) (.leaf 382562290)) (.branch 108 (.leaf 374745190) (.leaf 367095051))) (.branch 111 (.branch 110 (.leaf 359607973) (.leaf 352280164)) (.branch 112 (.leaf 345107937) (.leaf 338087699)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 331215959) (.leaf 324489315)) (.branch 116 (.leaf 317904455) (.leaf 311458156))) (.branch 119 (.branch 118 (.leaf 305147277) (.leaf 298968759)) (.branch 120 (.leaf 292919624) (.leaf 286996967)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 740).prefactor = (930805814042343/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 740).cutoff/(generalMeanRows 740).c)).2 =
    (190178714291153/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 740).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 740).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 740).q*(generalMeanRows 740).c/2-2 = (197/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable218.value]
    have hcontinuation : (generalMeanRows 740).q*(generalMeanRows 740).cutoff/2-2 = (1964/945:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable237.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 740).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 740

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 740).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 740).criticalRate j.val*(generalMeanRows 740).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 740).c*(generalMeanRows 740).criticalPoint j.val)).2-
      (generalMeanRows 740).J/2-(generalMeanRows 740).error (generalMeanGrid j.val)+
      (generalMeanRows 740).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 740).c)).2-
      (generalMeanRows 740).J/2-(generalMeanRows 740).error 4 := by
  have he : (generalMeanRows 740).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 740) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 740)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0740

/-! Kernel-checked entropy margins for general spectral rectangle 741. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0741
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5037910262) (.branch 2 (.leaf 4868231783) (.leaf 4706046880))) (.branch 5 (.branch 4 (.leaf 4550931775) (.leaf 4402492525)) (.branch 6 (.leaf 4260362422) (.leaf 4124199669)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3993685295) (.leaf 3868521295)) (.branch 10 (.leaf 3748428949) (.leaf 3633147306))) (.branch 13 (.branch 12 (.leaf 3522431813) (.leaf 3416053077)) (.branch 14 (.leaf 3313795734) (.leaf 3215457421))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3120847843) (.branch 17 (.leaf 3029787914) (.leaf 2942108973))) (.branch 20 (.branch 19 (.leaf 2857652069) (.leaf 2776267299)) (.branch 21 (.leaf 2697813200) (.leaf 2622156193)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2549170066) (.leaf 2478735499)) (.branch 25 (.leaf 2410739622) (.leaf 2345075610))) (.branch 28 (.branch 27 (.leaf 2281642303) (.leaf 2220343859)) (.branch 29 (.leaf 2161089425) (.leaf 2103792839)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2048372345) (.branch 32 (.leaf 1994750332) (.leaf 1942853094))) (.branch 35 (.branch 34 (.leaf 1892610595) (.leaf 1843956262)) (.branch 36 (.leaf 1796826787) (.leaf 1751161935)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1706904378) (.leaf 1663999529)) (.branch 40 (.leaf 1622395390) (.leaf 1582042409))) (.branch 43 (.branch 42 (.leaf 1542893347) (.leaf 1504903151)) (.branch 44 (.leaf 1468028840) (.leaf 1432229391))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1397465633) (.branch 47 (.leaf 1363700154) (.leaf 1330897208))) (.branch 50 (.branch 49 (.leaf 1299022626) (.leaf 1268043735)) (.branch 51 (.leaf 1237929284) (.leaf 1208649367)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1180175360) (.leaf 1152479852)) (.branch 55 (.leaf 1125536589) (.leaf 1099320410))) (.branch 58 (.branch 57 (.leaf 1073807201) (.leaf 1048973838)) (.branch 59 (.leaf 1024798140) (.leaf 1001258826))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 978335467) (.branch 62 (.leaf 956008451) (.leaf 934258939))) (.branch 65 (.branch 64 (.leaf 913068832) (.leaf 892420736)) (.branch 66 (.leaf 872297926) (.leaf 852684320)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 833564446) (.leaf 814923415)) (.branch 70 (.leaf 796746894) (.leaf 779021085))) (.branch 73 (.branch 72 (.leaf 761732693) (.leaf 744868912)) (.branch 74 (.leaf 728417398) (.leaf 712366252))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 696703997) (.branch 77 (.leaf 681419565) (.leaf 666502274))) (.branch 80 (.branch 79 (.leaf 651941814) (.leaf 637728232)) (.branch 81 (.leaf 623851916) (.leaf 610303580)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 597074251) (.leaf 584155259)) (.branch 85 (.leaf 571538218) (.leaf 559215021))) (.branch 88 (.branch 87 (.leaf 547177826) (.leaf 535419044)) (.branch 89 (.leaf 523931333) (.leaf 512707582)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 501740909) (.branch 92 (.leaf 491024647) (.leaf 480552337))) (.branch 95 (.branch 94 (.leaf 470317722) (.leaf 460314736)) (.branch 96 (.leaf 450537499) (.leaf 440980310)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 431637638) (.leaf 422504120)) (.branch 100 (.leaf 413574551) (.leaf 404843878))) (.branch 103 (.branch 102 (.leaf 396307199) (.leaf 387959752)) (.branch 104 (.leaf 379796915) (.leaf 371814196))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 364007232) (.leaf 356371786)) (.branch 108 (.leaf 348903736) (.leaf 341599079))) (.branch 111 (.branch 110 (.leaf 334453920) (.leaf 327464474)) (.branch 112 (.leaf 320627059) (.leaf 313938093)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 307394091) (.leaf 300991663)) (.branch 116 (.leaf 294727508) (.leaf 288598415))) (.branch 119 (.branch 118 (.leaf 282601256) (.leaf 276732987)) (.branch 120 (.leaf 270990642) (.leaf 265371335)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 741).prefactor = (1167572519966327/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 741).cutoff/(generalMeanRows 741).c)).2 =
    (74606277698047/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 741).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 741).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 741).q*(generalMeanRows 741).c/2-2 = (1617/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable243.value]
    have hcontinuation : (generalMeanRows 741).q*(generalMeanRows 741).cutoff/2-2 = (1964/945:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable237.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 741).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 741

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 741).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 741).criticalRate j.val*(generalMeanRows 741).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 741).c*(generalMeanRows 741).criticalPoint j.val)).2-
      (generalMeanRows 741).J/2-(generalMeanRows 741).error (generalMeanGrid j.val)+
      (generalMeanRows 741).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 741).c)).2-
      (generalMeanRows 741).J/2-(generalMeanRows 741).error 4 := by
  have he : (generalMeanRows 741).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 741) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 741)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0741

/-! Kernel-checked entropy margins for general spectral rectangle 742. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0742
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5196026247) (.branch 2 (.leaf 5028219589) (.leaf 4867780854))) (.branch 5 (.branch 4 (.leaf 4714289550) (.leaf 4567354997)) (.branch 6 (.leaf 4426613717) (.leaf 4291727112)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4162379386) (.leaf 4038275672)) (.branch 10 (.leaf 3919140357) (.leaf 3804715564))) (.branch 13 (.branch 12 (.leaf 3694759776) (.leaf 3589046600)) (.branch 14 (.leaf 3487363628) (.leaf 3389511416))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3295302543) (.branch 17 (.leaf 3204560750) (.leaf 3117120163))) (.branch 20 (.branch 19 (.leaf 3032824564) (.leaf 2951526737)) (.branch 21 (.leaf 2873087858) (.leaf 2797376934)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2724270289) (.leaf 2653651086)) (.branch 25 (.leaf 2585408888) (.leaf 2519439248))) (.branch 28 (.branch 27 (.leaf 2455643332) (.leaf 2393927570)) (.branch 29 (.leaf 2334203330) (.leaf 2276386615)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2220397783) (.branch 32 (.leaf 2166161284) (.leaf 2113605418))) (.branch 35 (.branch 34 (.leaf 2062662107) (.leaf 2013266681)) (.branch 36 (.leaf 1965357685) (.leaf 1918876688)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1873768114) (.leaf 1829979077)) (.branch 40 (.leaf 1787459235) (.leaf 1746160642))) (.branch 43 (.branch 42 (.leaf 1706037617) (.leaf 1667046622)) (.branch 44 (.leaf 1629146141) (.leaf 1592296572))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1556460124) (.branch 47 (.leaf 1521600721) (.leaf 1487683906))) (.branch 50 (.branch 49 (.leaf 1454676764) (.leaf 1422547831)) (.branch 51 (.leaf 1391267028) (.leaf 1360805580)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1331135958) (.leaf 1302231809)) (.branch 55 (.leaf 1274067898) (.leaf 1246620052))) (.branch 58 (.branch 57 (.leaf 1219865106) (.leaf 1193780855)) (.branch 59 (.leaf 1168346004) (.leaf 1143540124))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1119343608) (.branch 62 (.leaf 1095737637) (.leaf 1072704134))) (.branch 65 (.branch 64 (.leaf 1050225734) (.leaf 1028285748)) (.branch 66 (.leaf 1006868133) (.leaf 985957457)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 965538877) (.leaf 945598105)) (.branch 70 (.leaf 926121389) (.leaf 907095483))) (.branch 73 (.branch 72 (.leaf 888507627) (.leaf 870345524)) (.branch 74 (.leaf 852597319) (.leaf 835251581))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 818297282) (.branch 77 (.leaf 801723782) (.leaf 785520809))) (.branch 80 (.branch 79 (.leaf 769678446) (.leaf 754187112)) (.branch 81 (.leaf 739037552) (.leaf 724220821)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 709728270) (.leaf 695551536)) (.branch 85 (.leaf 681682529) (.leaf 668113421))) (.branch 88 (.branch 87 (.leaf 654836632) (.leaf 641844827)) (.branch 89 (.leaf 629130901) (.leaf 616687969)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 604509363) (.branch 92 (.leaf 592588615) (.leaf 580919458))) (.branch 95 (.branch 94 (.leaf 569495814) (.leaf 558311783)) (.branch 96 (.leaf 547361645) (.leaf 536639846)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 526140995) (.leaf 515859855)) (.branch 100 (.leaf 505791344) (.leaf 495930519))) (.branch 103 (.branch 102 (.leaf 486272582) (.leaf 476812867)) (.branch 104 (.leaf 467546838) (.leaf 458470085))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 449578317) (.leaf 440867363)) (.branch 108 (.leaf 432333163) (.leaf 423971764))) (.branch 111 (.branch 110 (.leaf 415779320) (.leaf 407752088)) (.branch 112 (.leaf 399886420) (.leaf 392178765)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 384625663) (.leaf 377223745)) (.branch 116 (.leaf 369969724) (.leaf 362860400))) (.branch 119 (.branch 118 (.leaf 355892652) (.leaf 349063437)) (.branch 120 (.leaf 342369788) (.leaf 335808811)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 742).prefactor = (4626872331257389/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 742).cutoff/(generalMeanRows 742).c)).2 =
    (403540764037963/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 742).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 742).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 742).q*(generalMeanRows 742).c/2-2 = (747/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable220.value]
    have hcontinuation : (generalMeanRows 742).q*(generalMeanRows 742).cutoff/2-2 = (15838/7497:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable242.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 742).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 742

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 742).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 742).criticalRate j.val*(generalMeanRows 742).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 742).c*(generalMeanRows 742).criticalPoint j.val)).2-
      (generalMeanRows 742).J/2-(generalMeanRows 742).error (generalMeanGrid j.val)+
      (generalMeanRows 742).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 742).c)).2-
      (generalMeanRows 742).J/2-(generalMeanRows 742).error 4 := by
  have he : (generalMeanRows 742).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 742) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 742)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0742

/-! Kernel-checked entropy margins for general spectral rectangle 743. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0743
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5301714740) (.branch 2 (.leaf 5133011532) (.leaf 4971690534))) (.branch 5 (.branch 4 (.leaf 4817329967) (.leaf 4669537982)) (.branch 6 (.leaf 4527950044) (.leaf 4392226599)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4262050984) (.leaf 4137127548)) (.branch 10 (.leaf 4017179972) (.leaf 3901949738))) (.branch 13 (.branch 12 (.leaf 3791194755) (.leaf 3684688111)) (.branch 14 (.leaf 3582216935) (.leaf 3483581366))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3388593610) (.branch 17 (.leaf 3297077078) (.leaf 3208865601))) (.branch 20 (.branch 19 (.leaf 3123802701) (.leaf 3041740935)) (.branch 21 (.leaf 2962541277) (.leaf 2886072561)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2812210961) (.leaf 2740839513)) (.branch 25 (.leaf 2671847671) (.leaf 2605130899))) (.branch 28 (.branch 27 (.leaf 2540590290) (.leaf 2478132217)) (.branch 29 (.leaf 2417668003) (.leaf 2359113621)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2302389409) (.branch 32 (.leaf 2247419807) (.leaf 2194133116))) (.branch 35 (.branch 34 (.leaf 2142461265) (.leaf 2092339601)) (.branch 36 (.leaf 2043706691) (.leaf 1996504131)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1950676381) (.leaf 1906170594)) (.branch 40 (.leaf 1862936468) (.leaf 1820926106))) (.branch 43 (.branch 42 (.leaf 1780093876) (.leaf 1740396290)) (.branch 44 (.leaf 1701791889) (.leaf 1664241127))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1627706270) (.branch 47 (.leaf 1592151299) (.leaf 1557541821))) (.branch 50 (.branch 49 (.leaf 1523844978) (.leaf 1491029368)) (.branch 51 (.leaf 1459064973) (.leaf 1427923079)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1397576217) (.leaf 1367998093)) (.branch 55 (.leaf 1339163534) (.leaf 1311048423))) (.branch 58 (.branch 57 (.leaf 1283629656) (.leaf 1256885082)) (.branch 59 (.leaf 1230793462) (.leaf 1205334423))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1180488411) (.branch 62 (.leaf 1156236657) (.leaf 1132561136))) (.branch 65 (.branch 64 (.leaf 1109444532) (.leaf 1086870203)) (.branch 66 (.leaf 1064822152) (.leaf 1043284991)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1022243920) (.leaf 1001684693)) (.branch 70 (.leaf 981593595) (.leaf 961957418))) (.branch 73 (.branch 72 (.leaf 942763439) (.leaf 923999395)) (.branch 74 (.leaf 905653463) (.leaf 887714244))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 870170737) (.branch 77 (.leaf 853012331) (.leaf 836228779))) (.branch 80 (.branch 79 (.leaf 819810188) (.leaf 803746999)) (.branch 81 (.leaf 788029979) (.leaf 772650201)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 757599034) (.leaf 742868132)) (.branch 85 (.leaf 728449417) (.leaf 714335074))) (.branch 88 (.branch 87 (.leaf 700517537) (.leaf 686989479)) (.branch 89 (.leaf 673743804) (.leaf 660773634)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 648072305) (.branch 92 (.leaf 635633356) (.leaf 623450522))) (.branch 95 (.branch 94 (.leaf 611517725) (.leaf 599829068)) (.branch 96 (.leaf 588378829) (.leaf 577161451)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 566171540) (.leaf 555403857)) (.branch 100 (.leaf 544853310) (.leaf 534514955))) (.branch 103 (.branch 102 (.leaf 524383982) (.leaf 514455717)) (.branch 104 (.leaf 504725615) (.leaf 495189256))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 485842337) (.leaf 476680674)) (.branch 108 (.leaf 467700193) (.leaf 458896929))) (.branch 111 (.branch 110 (.leaf 450267020) (.leaf 441806705)) (.branch 112 (.leaf 433512322) (.leaf 425380302)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 417407168) (.leaf 409589529)) (.branch 116 (.leaf 401924082) (.leaf 394407605))) (.branch 119 (.branch 118 (.leaf 387036957) (.leaf 379809074)) (.branch 120 (.leaf 372720967) (.leaf 365769719)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 743).prefactor = (464263872937873/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 743).cutoff/(generalMeanRows 743).c)).2 =
    (411031435767121/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 743).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 743).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 743).q*(generalMeanRows 743).c/2-2 = (1453/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable239.value]
    have hcontinuation : (generalMeanRows 743).q*(generalMeanRows 743).cutoff/2-2 = (15838/7497:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable242.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 743).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 743

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 743).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 743).criticalRate j.val*(generalMeanRows 743).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 743).c*(generalMeanRows 743).criticalPoint j.val)).2-
      (generalMeanRows 743).J/2-(generalMeanRows 743).error (generalMeanGrid j.val)+
      (generalMeanRows 743).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 743).c)).2-
      (generalMeanRows 743).J/2-(generalMeanRows 743).error 4 := by
  have he : (generalMeanRows 743).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 743) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 743)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0743

/-! Kernel-checked entropy margins for general spectral rectangle 744. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0744
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5147604950) (.branch 2 (.leaf 4978952373) (.leaf 4817718276))) (.branch 5 (.branch 4 (.leaf 4663480633) (.leaf 4515847270)) (.branch 6 (.leaf 4374453253) (.leaf 4238958561)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4109046008) (.leaf 3984419371)) (.branch 10 (.leaf 3864801711) (.leaf 3749933850))) (.branch 13 (.branch 12 (.leaf 3639573006) (.leaf 3533491540)) (.branch 14 (.leaf 3431475835) (.leaf 3333325257))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3238851226) (.branch 17 (.leaf 3147876349) (.leaf 3060233642))) (.branch 20 (.branch 19 (.leaf 2975765806) (.leaf 2894324566)) (.branch 21 (.leaf 2815770067) (.leaf 2739970307)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2666800628) (.leaf 2596143234)) (.branch 25 (.leaf 2527886751) (.leaf 2461925821))) (.branch 28 (.branch 27 (.leaf 2398160723) (.leaf 2336497021)) (.branch 29 (.leaf 2276845241) (.leaf 2219120566)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2163242556) (.branch 32 (.leaf 2109134886) (.leaf 2056725101))) (.branch 35 (.branch 34 (.leaf 2005944388) (.leaf 1956727366)) (.branch 36 (.leaf 1909011886) (.leaf 1862738846)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1817852016) (.leaf 1774297877)) (.branch 40 (.leaf 1732025472) (.leaf 1690986259))) (.branch 43 (.branch 42 (.leaf 1651133980) (.leaf 1612424534)) (.branch 44 (.leaf 1574815863) (.leaf 1538267840))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1502742163) (.branch 47 (.leaf 1468202263) (.leaf 1434613207))) (.branch 50 (.branch 49 (.leaf 1401941615) (.leaf 1370155579)) (.branch 51 (.leaf 1339224584) (.leaf 1309119441)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1279812215) (.leaf 1251276162)) (.branch 55 (.leaf 1223485670) (.leaf 1196416203))) (.branch 58 (.branch 57 (.leaf 1170044245) (.leaf 1144347250)) (.branch 59 (.leaf 1119303595) (.leaf 1094892536))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1071094163) (.branch 62 (.leaf 1047889361) (.leaf 1025259771))) (.branch 65 (.branch 64 (.leaf 1003187755) (.leaf 981656362)) (.branch 66 (.leaf 960649296) (.leaf 940150881)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 920146041) (.leaf 900620263)) (.branch 70 (.leaf 881559577) (.leaf 862950529))) (.branch 73 (.branch 72 (.leaf 844780160) (.leaf 827035981)) (.branch 74 (.leaf 809705952) (.leaf 792778466))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 776242326) (.branch 77 (.leaf 760086727) (.leaf 744301242))) (.branch 80 (.branch 79 (.leaf 728875804) (.leaf 713800691)) (.branch 81 (.leaf 699066509) (.leaf 684664183)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 670584940) (.leaf 656820296)) (.branch 85 (.leaf 643362046) (.leaf 630202254))) (.branch 88 (.branch 87 (.leaf 617333237) (.leaf 604747561)) (.branch 89 (.leaf 592438024) (.leaf 580397654)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 568619696) (.branch 92 (.leaf 557097604) (.leaf 545825031))) (.branch 95 (.branch 94 (.leaf 534795825) (.leaf 524004021)) (.branch 96 (.leaf 513443831) (.leaf 503109640)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 492995998) (.leaf 483097615)) (.branch 100 (.leaf 473409354) (.leaf 463926227))) (.branch 103 (.branch 102 (.leaf 454643388) (.leaf 445556128)) (.branch 104 (.leaf 436659873) (.leaf 427950175))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 419422709) (.leaf 411073271)) (.branch 108 (.leaf 402897770) (.leaf 394892229))) (.branch 111 (.branch 110 (.leaf 387052776) (.leaf 379375642)) (.branch 112 (.leaf 371857162) (.leaf 364493765)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 357281974) (.leaf 350218403)) (.branch 116 (.leaf 343299755) (.leaf 336522816))) (.branch 119 (.branch 118 (.leaf 329884457) (.leaf 323381624)) (.branch 120 (.leaf 317011346) (.leaf 310770723)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 744).prefactor = (4646410311610061/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 744).cutoff/(generalMeanRows 744).c)).2 =
    (49163572616173/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 744).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 744).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 744).q*(generalMeanRows 744).c/2-2 = (307/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable081.value]
    have hcontinuation : (generalMeanRows 744).q*(generalMeanRows 744).cutoff/2-2 = (7898/3759:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable241.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 744).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 744

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 744).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 744).criticalRate j.val*(generalMeanRows 744).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 744).c*(generalMeanRows 744).criticalPoint j.val)).2-
      (generalMeanRows 744).J/2-(generalMeanRows 744).error (generalMeanGrid j.val)+
      (generalMeanRows 744).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 744).c)).2-
      (generalMeanRows 744).J/2-(generalMeanRows 744).error 4 := by
  have he : (generalMeanRows 744).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 744) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 744)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0744

/-! Kernel-checked entropy margins for general spectral rectangle 745. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0745
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5165291861) (.branch 2 (.leaf 4996059802) (.leaf 4834271713))) (.branch 5 (.branch 4 (.leaf 4679504118) (.leaf 4531363494)) (.branch 6 (.leaf 4389483653) (.leaf 4253523408)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4123164482) (.leaf 3998109635)) (.branch 10 (.leaf 3878080975) (.leaf 3762818434))) (.branch 13 (.branch 12 (.leaf 3652078395) (.leaf 3545632439)) (.branch 14 (.leaf 3443266212) (.leaf 3344778395))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3249979755) (.branch 17 (.leaf 3158692293) (.leaf 3070748450))) (.branch 20 (.branch 19 (.leaf 2985990387) (.leaf 2904269319)) (.branch 21 (.leaf 2825444911) (.leaf 2749384707)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2675963621) (.leaf 2605063451)) (.branch 25 (.leaf 2536572442) (.leaf 2470384874))) (.branch 28 (.branch 27 (.leaf 2406400682) (.leaf 2344525107)) (.branch 29 (.leaf 2284668367) (.leaf 2226745353)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2170675349) (.branch 32 (.leaf 2116381767) (.leaf 2063791904))) (.branch 35 (.branch 34 (.leaf 2012836711) (.leaf 1963450583)) (.branch 36 (.leaf 1915571155) (.leaf 1869139123)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1824098063) (.leaf 1780394275)) (.branch 40 (.leaf 1737976625) (.leaf 1696796403))) (.branch 43 (.branch 42 (.leaf 1656807193) (.leaf 1617964743)) (.branch 44 (.leaf 1580226851) (.leaf 1543553251))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1507905510) (.branch 47 (.leaf 1473246932) (.leaf 1439542466))) (.branch 50 (.branch 49 (.leaf 1406758616) (.leaf 1374863364)) (.branch 51 (.leaf 1343826092) (.leaf 1313617509)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1284209585) (.leaf 1255575484)) (.branch 55 (.leaf 1227689505) (.leaf 1200527029))) (.branch 58 (.branch 57 (.leaf 1174064458) (.leaf 1148279169)) (.branch 59 (.leaf 1123149466) (.leaf 1098654532))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1074774389) (.branch 62 (.leaf 1051489856) (.leaf 1028782511))) (.branch 65 (.branch 64 (.leaf 1006634657) (.leaf 985029284)) (.branch 66 (.leaf 963950038) (.leaf 943381192)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 923307616) (.leaf 903714748)) (.branch 70 (.leaf 884588571) (.leaf 865915584))) (.branch 73 (.branch 72 (.leaf 847682782) (.leaf 829877635)) (.branch 74 (.leaf 812488061) (.leaf 795502413))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 778909455) (.branch 77 (.leaf 762698346) (.leaf 746858623))) (.branch 80 (.branch 79 (.leaf 731380185) (.leaf 716253274)) (.branch 81 (.leaf 701468466) (.leaf 687016655)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 672889036) (.leaf 659077097)) (.branch 85 (.leaf 645572606) (.leaf 632367597))) (.branch 88 (.branch 87 (.leaf 619454363) (.leaf 606825443)) (.branch 89 (.leaf 594473611) (.leaf 582391871)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 570573445) (.branch 92 (.leaf 559011763) (.leaf 547700458))) (.branch 95 (.branch 94 (.leaf 536633357) (.leaf 525804473)) (.branch 96 (.leaf 515207999) (.leaf 504838300)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 494689908) (.leaf 484757514)) (.branch 100 (.leaf 475035965) (.leaf 465520254))) (.branch 103 (.branch 102 (.leaf 456205519) (.leaf 447087037)) (.branch 104 (.leaf 438160215) (.leaf 429420590))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 420863824) (.leaf 412485698)) (.branch 108 (.leaf 404282107) (.leaf 396249059))) (.branch 111 (.branch 110 (.leaf 388382669) (.leaf 380679158)) (.branch 112 (.leaf 373134845) (.leaf 365746147)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 358509577) (.leaf 351421736)) (.branch 116 (.leaf 344479316) (.leaf 337679092))) (.branch 119 (.branch 118 (.leaf 331017923) (.leaf 324492747)) (.branch 120 (.leaf 318100581) (.leaf 311838515)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 745).prefactor = (582796892885799/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 745).cutoff/(generalMeanRows 745).c)).2 =
    (49163572616173/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 745).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 745).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 745).q*(generalMeanRows 745).c/2-2 = (307/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable081.value]
    have hcontinuation : (generalMeanRows 745).q*(generalMeanRows 745).cutoff/2-2 = (7898/3759:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable241.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 745).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 745

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 745).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 745).criticalRate j.val*(generalMeanRows 745).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 745).c*(generalMeanRows 745).criticalPoint j.val)).2-
      (generalMeanRows 745).J/2-(generalMeanRows 745).error (generalMeanGrid j.val)+
      (generalMeanRows 745).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 745).c)).2-
      (generalMeanRows 745).J/2-(generalMeanRows 745).error 4 := by
  have he : (generalMeanRows 745).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 745) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 745)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0745

/-! Kernel-checked entropy margins for general spectral rectangle 746. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0746
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5115556521) (.branch 2 (.leaf 4945559692) (.leaf 4783068114))) (.branch 5 (.branch 4 (.leaf 4627655195) (.leaf 4478924484)) (.branch 6 (.leaf 4336507041) (.leaf 4200059085)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4069259896) (.leaf 3943809926)) (.branch 10 (.leaf 3823429102) (.leaf 3707855292))) (.branch 13 (.branch 12 (.leaf 3596842923) (.leaf 3490161721)) (.branch 14 (.leaf 3387595573) (.leaf 3288941486))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3194008638) (.branch 17 (.leaf 3102617516) (.leaf 3014599119))) (.branch 20 (.branch 19 (.leaf 2929794235) (.leaf 2848052770)) (.branch 21 (.leaf 2769233137) (.leaf 2693201689)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2619832198) (.leaf 2549005373)) (.branch 25 (.leaf 2480608417) (.leaf 2414534612))) (.branch 28 (.branch 27 (.leaf 2350682939) (.leaf 2288957726)) (.branch 29 (.leaf 2229268313) (.leaf 2171528755)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2115657530) (.branch 32 (.leaf 2061577281) (.leaf 2009214563))) (.branch 35 (.branch 34 (.leaf 1958499618) (.leaf 1909366161)) (.branch 36 (.leaf 1861751174) (.leaf 1815594724)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1770839787) (.leaf 1727432082)) (.branch 40 (.leaf 1685319919) (.leaf 1644454057))) (.branch 43 (.branch 42 (.leaf 1604787566) (.leaf 1566275701)) (.branch 44 (.leaf 1528875785) (.leaf 1492547099))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1457250772) (.branch 47 (.leaf 1422949688) (.leaf 1389608391))) (.branch 50 (.branch 49 (.leaf 1357192997) (.leaf 1325671116)) (.branch 51 (.leaf 1295011771) (.leaf 1265185325)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1236163416) (.leaf 1207918892)) (.branch 55 (.leaf 1180425745) (.leaf 1153659062))) (.branch 58 (.branch 57 (.leaf 1127594961) (.leaf 1102210551)) (.branch 59 (.leaf 1077483871) (.leaf 1053393857))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1029920290) (.branch 62 (.leaf 1007043757) (.leaf 984745615))) (.branch 65 (.branch 64 (.leaf 963007955) (.leaf 941813561)) (.branch 66 (.leaf 921145885) (.leaf 900989011)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 881327630) (.leaf 862147006)) (.branch 70 (.leaf 843432958) (.leaf 825171825))) (.branch 73 (.branch 72 (.leaf 807350452) (.leaf 789956162)) (.branch 74 (.leaf 772976736) (.leaf 756400391))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 740215766) (.branch 77 (.leaf 724411898) (.leaf 708978207))) (.branch 80 (.branch 79 (.leaf 693904481) (.leaf 679180858)) (.branch 81 (.leaf 664797812) (.leaf 650746139)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 637016945) (.leaf 623601629)) (.branch 85 (.leaf 610491877) (.leaf 597679643))) (.branch 88 (.branch 87 (.leaf 585157147) (.leaf 572916854)) (.branch 89 (.leaf 560951473) (.leaf 549253944)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 537817427) (.branch 92 (.leaf 526635296) (.leaf 515701130))) (.branch 95 (.branch 94 (.leaf 505008705) (.leaf 494551988)) (.branch 96 (.leaf 484325124) (.leaf 474322439)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 464538424) (.leaf 454967734)) (.branch 100 (.leaf 445605180) (.leaf 436445726))) (.branch 103 (.branch 102 (.leaf 427484478) (.leaf 418716686)) (.branch 104 (.leaf 410137733) (.leaf 401743133))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 393528527) (.leaf 385489675)) (.branch 108 (.leaf 377622457) (.leaf 369922865))) (.branch 111 (.branch 110 (.leaf 362387001) (.leaf 355011072)) (.branch 112 (.leaf 347791388) (.leaf 340724357)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 333806485) (.leaf 327034367)) (.branch 116 (.leaf 320404689) (.leaf 313914226))) (.branch 119 (.branch 118 (.leaf 307559832) (.leaf 301338446)) (.branch 120 (.leaf 295247084) (.leaf 289282839)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 746).prefactor = (4694469557583017/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 746).cutoff/(generalMeanRows 746).c)).2 =
    (4824105920397/12500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 746).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 746).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 746).q*(generalMeanRows 746).c/2-2 = (197/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable218.value]
    have hcontinuation : (generalMeanRows 746).q*(generalMeanRows 746).cutoff/2-2 = (7898/3759:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable241.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 746).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 746

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 746).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 746).criticalRate j.val*(generalMeanRows 746).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 746).c*(generalMeanRows 746).criticalPoint j.val)).2-
      (generalMeanRows 746).J/2-(generalMeanRows 746).error (generalMeanGrid j.val)+
      (generalMeanRows 746).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 746).c)).2-
      (generalMeanRows 746).J/2-(generalMeanRows 746).error 4 := by
  have he : (generalMeanRows 746).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 746) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 746)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0746

/-! Kernel-checked entropy margins for general spectral rectangle 747. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0747
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5100775034) (.branch 2 (.leaf 4931301422) (.leaf 4769296904))) (.branch 5 (.branch 4 (.leaf 4614337865) (.leaf 4466030585)) (.branch 6 (.leaf 4324008626) (.leaf 4187930501)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4057477598) (.leaf 3932352297)) (.branch 10 (.leaf 3812276300) (.leaf 3696989101))) (.branch 13 (.branch 12 (.leaf 3586246620) (.leaf 3479819952)) (.branch 14 (.leaf 3377494241) (.leaf 3279067648))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3184350409) (.branch 17 (.leaf 3093163983) (.leaf 3005340260))) (.branch 20 (.branch 19 (.leaf 2920720844) (.leaf 2839156390)) (.branch 21 (.leaf 2760505997) (.leaf 2684636647)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2611422689) (.leaf 2540745358)) (.branch 25 (.leaf 2472492341) (.leaf 2406557360))) (.branch 28 (.branch 27 (.leaf 2342839802) (.leaf 2281244362)) (.branch 29 (.leaf 2221680718) (.leaf 2164063232)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2108310664) (.branch 32 (.leaf 2054345910) (.leaf 2002095762))) (.branch 35 (.branch 34 (.leaf 1951490672) (.leaf 1902464546)) (.branch 36 (.leaf 1854954545) (.leaf 1808900894)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1764246712) (.leaf 1720937851)) (.branch 40 (.leaf 1678922740) (.leaf 1638152243))) (.branch 43 (.branch 42 (.leaf 1598579527) (.leaf 1560159937)) (.branch 44 (.leaf 1522850873) (.leaf 1486611687))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1451403572) (.branch 47 (.leaf 1417189469) (.leaf 1383933974))) (.branch 50 (.branch 49 (.leaf 1351603250) (.leaf 1320164945)) (.branch 51 (.leaf 1289588121) (.leaf 1259843174)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1230901770) (.leaf 1202736783)) (.branch 55 (.leaf 1175322229) (.leaf 1148633214))) (.branch 58 (.branch 57 (.leaf 1122645875) (.leaf 1097337336)) (.branch 59 (.leaf 1072685651) (.leaf 1048669767))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1025269477) (.branch 62 (.leaf 1002465378) (.leaf 980238835))) (.branch 65 (.branch 64 (.leaf 958571945) (.leaf 937447500)) (.branch 66 (.leaf 916848959) (.leaf 896760410)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 877166548) (.leaf 858052644)) (.branch 70 (.leaf 839404517) (.leaf 821208512))) (.branch 73 (.branch 72 (.leaf 803451478) (.leaf 786120739)) (.branch 74 (.leaf 769204081) (.leaf 752689723))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 736566307) (.branch 77 (.leaf 720822873) (.leaf 705448844))) (.branch 80 (.branch 79 (.leaf 690434011) (.leaf 675768514)) (.branch 81 (.leaf 661442832) (.leaf 647447764)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 633774417) (.leaf 620414197)) (.branch 85 (.leaf 607358790) (.leaf 594600157))) (.branch 88 (.branch 87 (.leaf 582130519) (.leaf 569942347)) (.branch 89 (.leaf 558028354) (.leaf 546381483)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 534994901) (.branch 92 (.leaf 523861984) (.leaf 512976318))) (.branch 95 (.branch 94 (.leaf 502331684) (.leaf 491922051)) (.branch 96 (.leaf 481741574) (.leaf 471784581)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 462045569) (.leaf 452519200)) (.branch 100 (.leaf 443200290) (.leaf 434083809))) (.branch 103 (.branch 102 (.leaf 425164870) (.leaf 416438728)) (.branch 104 (.leaf 407900772) (.leaf 399546524))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 391371629) (.leaf 383371857)) (.branch 108 (.leaf 375543091) (.leaf 367881332))) (.branch 111 (.branch 110 (.leaf 360382688) (.leaf 353043373)) (.branch 112 (.leaf 345859703) (.leaf 338828095)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 331945060) (.leaf 325207200)) (.branch 116 (.leaf 318611210) (.leaf 312153870))) (.branch 119 (.branch 118 (.leaf 305832041) (.leaf 299642671)) (.branch 120 (.leaf 293582781) (.leaf 287649472)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 747).prefactor = (186652733779087/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 747).cutoff/(generalMeanRows 747).c)).2 =
    (47892383943023/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 747).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 747).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 747).q*(generalMeanRows 747).c/2-2 = (197/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable218.value]
    have hcontinuation : (generalMeanRows 747).q*(generalMeanRows 747).cutoff/2-2 = (15754/7539:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable244.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 747).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 747

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 747).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 747).criticalRate j.val*(generalMeanRows 747).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 747).c*(generalMeanRows 747).criticalPoint j.val)).2-
      (generalMeanRows 747).J/2-(generalMeanRows 747).error (generalMeanGrid j.val)+
      (generalMeanRows 747).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 747).c)).2-
      (generalMeanRows 747).J/2-(generalMeanRows 747).error 4 := by
  have he : (generalMeanRows 747).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 747) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 747)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0747

/-! Kernel-checked entropy margins for general spectral rectangle 748. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0748
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5035108532) (.branch 2 (.leaf 4865481173) (.leaf 4703358308))) (.branch 5 (.branch 4 (.leaf 4548314625) (.leaf 4399954794)) (.branch 6 (.leaf 4257910853) (.leaf 4121839871)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3991421855) (.leaf 3866357879)) (.branch 10 (.leaf 3746368395) (.leaf 3631191708))) (.branch 13 (.branch 12 (.leaf 3520582600) (.leaf 3414311083)) (.branch 14 (.leaf 3312161261) (.leaf 3213930301))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3119427488) (.branch 17 (.leaf 3028473368) (.leaf 2940898956))) (.branch 20 (.branch 19 (.leaf 2856545018) (.leaf 2775261403)) (.branch 21 (.leaf 2696906437) (.leaf 2621346359)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2548454802) (.leaf 2478112317)) (.branch 25 (.leaf 2410205929) (.leaf 2344628725))) (.branch 28 (.branch 27 (.leaf 2281279482) (.leaf 2220062305)) (.branch 29 (.leaf 2160886308) (.leaf 2103665307)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2048317537) (.branch 32 (.leaf 1994765390) (.leaf 1942935169))) (.branch 35 (.branch 34 (.leaf 1892756860) (.leaf 1844163918)) (.branch 36 (.leaf 1797093066) (.leaf 1751484113)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1707279776) (.leaf 1664425516)) (.branch 40 (.leaf 1622869388) (.leaf 1582561898))) (.branch 43 (.branch 42 (.leaf 1543455865) (.leaf 1505506300)) (.branch 44 (.leaf 1468670282) (.leaf 1432906854))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1398176910) (.branch 47 (.leaf 1364443107) (.leaf 1331669762))) (.branch 50 (.branch 49 (.leaf 1299822775) (.leaf 1268869539)) (.branch 51 (.leaf 1238778869) (.leaf 1209520927)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1181067154) (.leaf 1153390203)) (.branch 55 (.leaf 1126463882) (.leaf 1100263097))) (.branch 58 (.branch 57 (.leaf 1074763794) (.leaf 1049942908)) (.branch 59 (.leaf 1025778320) (.leaf 1002248805))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 979333992) (.branch 62 (.leaf 957014324) (.leaf 935271017))) (.branch 65 (.branch 64 (.leaf 914086023) (.leaf 893442000)) (.branch 66 (.leaf 873322272) (.leaf 853710807)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 834592177) (.leaf 815951540)) (.branch 70 (.leaf 797774608) (.leaf 780047622))) (.branch 73 (.branch 72 (.leaf 762757331) (.leaf 745890967)) (.branch 74 (.leaf 729436225) (.leaf 713381242))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 697714578) (.branch 77 (.leaf 682425198) (.leaf 667502452))) (.branch 80 (.branch 79 (.leaf 652936064) (.leaf 638716110)) (.branch 81 (.leaf 624833006) (.leaf 611277495)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 598040633) (.leaf 585113772)) (.branch 85 (.leaf 572488553) (.leaf 560156892))) (.branch 88 (.branch 87 (.leaf 548110970) (.leaf 536343219)) (.branch 89 (.leaf 524846317) (.leaf 513613175)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 502636928) (.branch 92 (.leaf 491910927) (.leaf 481428731))) (.branch 95 (.branch 94 (.leaf 471184098) (.leaf 461170979)) (.branch 96 (.leaf 451383507) (.leaf 441815996)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 432462929) (.leaf 423318954)) (.branch 100 (.leaf 414378879) (.leaf 405637663))) (.branch 103 (.branch 102 (.leaf 397090413) (.leaf 388732378)) (.branch 104 (.leaf 380558946) (.leaf 372565633))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 364748087) (.leaf 357102076)) (.branch 108 (.leaf 349623487) (.leaf 342308324))) (.branch 111 (.branch 110 (.leaf 335152699) (.leaf 328152834)) (.branch 112 (.leaf 321305050) (.leaf 314605773)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 308051523) (.leaf 301638914)) (.branch 116 (.leaf 295364650) (.leaf 289225523))) (.branch 119 (.branch 118 (.leaf 283218411) (.leaf 277340272)) (.branch 120 (.leaf 271588143) (.leaf 265959141)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 748).prefactor = (4682485940520311/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 748).cutoff/(generalMeanRows 748).c)).2 =
    (375813031452109/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 748).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 748).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 748).q*(generalMeanRows 748).c/2-2 = (1617/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable243.value]
    have hcontinuation : (generalMeanRows 748).q*(generalMeanRows 748).cutoff/2-2 = (15754/7539:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable244.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 748).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 748

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 748).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 748).criticalRate j.val*(generalMeanRows 748).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 748).c*(generalMeanRows 748).criticalPoint j.val)).2-
      (generalMeanRows 748).J/2-(generalMeanRows 748).error (generalMeanGrid j.val)+
      (generalMeanRows 748).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 748).c)).2-
      (generalMeanRows 748).J/2-(generalMeanRows 748).error 4 := by
  have he : (generalMeanRows 748).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 748) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 748)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0748

/-! Kernel-checked entropy margins for general spectral rectangle 749. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0749
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5055512538) (.branch 2 (.leaf 4885241209) (.leaf 4722489638))) (.branch 5 (.branch 4 (.leaf 4566832566) (.leaf 4417874675)) (.branch 6 (.leaf 4275247975) (.leaf 4138609474)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4007639087) (.leaf 3882037769)) (.branch 10 (.leaf 3761525825) (.leaf 3645841391))) (.branch 13 (.branch 12 (.leaf 3534739063) (.leaf 3427988643)) (.branch 14 (.leaf 3325374017) (.leaf 3226692114))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3131751973) (.branch 17 (.leaf 3040373883) (.leaf 2952388595))) (.branch 20 (.branch 19 (.leaf 2867636602) (.leaf 2785967476)) (.branch 21 (.leaf 2707239262) (.leaf 2631317912)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2558076775) (.leaf 2487396112)) (.branch 25 (.leaf 2419162660) (.leaf 2353269220))) (.branch 28 (.branch 27 (.leaf 2289614279) (.leaf 2228101660)) (.branch 29 (.leaf 2168640193) (.leaf 2111143415)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2055529284) (.branch 32 (.leaf 2001719918) (.leaf 1949641353))) (.branch 35 (.branch 34 (.leaf 1899223308) (.leaf 1850398979)) (.branch 36 (.leaf 1803104834) (.leaf 1757280431)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1712868240) (.leaf 1669813484)) (.branch 40 (.leaf 1628063981) (.leaf 1587570008))) (.branch 43 (.branch 42 (.leaf 1548284160) (.leaf 1510161228)) (.branch 44 (.leaf 1473158080) (.leaf 1437233548))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1402348327) (.branch 47 (.leaf 1368464873) (.leaf 1335547315))) (.branch 50 (.branch 49 (.leaf 1303561364) (.leaf 1272474235)) (.branch 51 (.leaf 1242254564) (.leaf 1212872344)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1184298850) (.leaf 1156506575)) (.branch 55 (.leaf 1129469173) (.leaf 1103161396))) (.branch 58 (.branch 57 (.leaf 1077559045) (.leaf 1052638915)) (.branch 59 (.leaf 1028378748) (.leaf 1004757188))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 981753736) (.branch 62 (.leaf 959348710) (.leaf 937523206))) (.branch 65 (.branch 64 (.leaf 916259062) (.leaf 895538822)) (.branch 66 (.leaf 875345704) (.leaf 855663568)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 836476890) (.leaf 817770728)) (.branch 70 (.leaf 799530699) (.leaf 781742956))) (.branch 73 (.branch 72 (.leaf 764394159) (.leaf 747471457)) (.branch 74 (.leaf 730962462) (.leaf 714855234))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 699138256) (.branch 77 (.leaf 683800421) (.leaf 668831009))) (.branch 80 (.branch 79 (.leaf 654219675) (.leaf 639956432)) (.branch 81 (.leaf 626031632) (.leaf 612435958)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 599160407) (.leaf 586196276)) (.branch 85 (.leaf 573535152) (.leaf 561168898))) (.branch 88 (.branch 87 (.leaf 549089645) (.leaf 537289779)) (.branch 89 (.leaf 525761930) (.leaf 514498964)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 503493974) (.branch 92 (.leaf 492740269) (.leaf 482231370))) (.branch 95 (.branch 94 (.leaf 471960995) (.leaf 461923059)) (.branch 96 (.leaf 452111661) (.leaf 442521079)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 433145765) (.leaf 423980335)) (.branch 100 (.leaf 415019565) (.leaf 406258388))) (.branch 103 (.branch 102 (.leaf 397691882) (.leaf 389315270)) (.branch 104 (.leaf 381123911) (.leaf 373113301))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 365279061) (.leaf 357616936)) (.branch 108 (.leaf 350122793) (.leaf 342792614))) (.branch 111 (.branch 110 (.leaf 335622490) (.leaf 328608623)) (.branch 112 (.leaf 321747318) (.leaf 315034981)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 308468115) (.leaf 302043317)) (.branch 116 (.leaf 295757275) (.leaf 289606767))) (.branch 119 (.branch 118 (.leaf 283588654) (.leaf 277699882)) (.branch 120 (.leaf 271937474) (.leaf 266298533)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 749).prefactor = (4686607904899937/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 749).cutoff/(generalMeanRows 749).c)).2 =
    (74606277698047/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 749).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 749).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 749).q*(generalMeanRows 749).c/2-2 = (1617/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable243.value]
    have hcontinuation : (generalMeanRows 749).q*(generalMeanRows 749).cutoff/2-2 = (1964/945:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable237.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 749).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 749

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 749).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 749).criticalRate j.val*(generalMeanRows 749).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 749).c*(generalMeanRows 749).criticalPoint j.val)).2-
      (generalMeanRows 749).J/2-(generalMeanRows 749).error (generalMeanGrid j.val)+
      (generalMeanRows 749).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 749).c)).2-
      (generalMeanRows 749).J/2-(generalMeanRows 749).error 4 := by
  have he : (generalMeanRows 749).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 749) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 749)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0749

/-! Kernel-checked entropy margins for general spectral rectangle 750. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0750
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4991173169) (.branch 2 (.leaf 4820775105) (.leaf 4657932120))) (.branch 5 (.branch 4 (.leaf 4502217211) (.leaf 4353233408)) (.branch 6 (.leaf 4210611158) (.leaf 4074005985)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3943096396) (.leaf 3817582002)) (.branch 10 (.leaf 3697181832) (.leaf 3581632807))) (.branch 13 (.branch 12 (.leaf 3470688360) (.leaf 3364117186)) (.branch 14 (.leaf 3261702111) (.leaf 3163239052))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3068536080) (.branch 17 (.leaf 2977412554) (.leaf 2889698338))) (.branch 20 (.branch 19 (.leaf 2805233072) (.leaf 2723865513)) (.branch 21 (.leaf 2645452920) (.leaf 2569860495)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2496960864) (.leaf 2426633595)) (.branch 25 (.leaf 2358764759) (.leaf 2293246518))) (.branch 28 (.branch 27 (.leaf 2229976743) (.leaf 2168858666)) (.branch 29 (.leaf 2109800549) (.leaf 2052715382)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1997520599) (.branch 32 (.leaf 1944137812) (.leaf 1892492570))) (.branch 35 (.branch 34 (.leaf 1842514126) (.leaf 1794135226)) (.branch 36 (.leaf 1747291906) (.leaf 1701923307)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1657971501) (.leaf 1615381323)) (.branch 40 (.leaf 1574100225) (.leaf 1534078126))) (.branch 43 (.branch 42 (.leaf 1495267280) (.leaf 1457622149)) (.branch 44 (.leaf 1421099284) (.leaf 1385657215))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1351256344) (.branch 47 (.leaf 1317858848) (.leaf 1285428586))) (.branch 50 (.branch 49 (.leaf 1253931010) (.leaf 1223333086)) (.branch 51 (.leaf 1193603216) (.leaf 1164711160)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1136627976) (.leaf 1109325946)) (.branch 55 (.leaf 1082778523) (.leaf 1056960266))) (.branch 58 (.branch 57 (.leaf 1031846791) (.leaf 1007414716)) (.branch 59 (.leaf 983641614) (.leaf 960505966))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 937987120) (.branch 62 (.leaf 916065245) (.leaf 894721295))) (.branch 65 (.branch 64 (.leaf 873936974) (.leaf 853694697)) (.branch 66 (.leaf 833977559) (.leaf 814769305)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 796054297) (.leaf 777817490)) (.branch 70 (.leaf 760044399) (.leaf 742721082))) (.branch 73 (.branch 72 (.leaf 725834108) (.leaf 709370540)) (.branch 74 (.leaf 693317910) (.leaf 677664201))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 662397824) (.branch 77 (.leaf 647507602) (.leaf 632982753))) (.branch 80 (.branch 79 (.leaf 618812870) (.leaf 604987909)) (.branch 81 (.leaf 591498171) (.leaf 578334287)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 565487209) (.leaf 552948190)) (.branch 85 (.leaf 540708778) (.leaf 528760799))) (.branch 88 (.branch 87 (.leaf 517096350) (.leaf 505707786)) (.branch 89 (.leaf 494587707) (.leaf 483728955)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 473124598) (.branch 92 (.leaf 462767927) (.leaf 452652440))) (.branch 95 (.branch 94 (.leaf 442771842) (.leaf 433120032)) (.branch 96 (.leaf 423691098) (.leaf 414479307)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 405479103) (.leaf 396685095)) (.branch 100 (.leaf 388092056) (.leaf 379694915))) (.branch 103 (.branch 102 (.leaf 371488748) (.leaf 363468779)) (.branch 104 (.leaf 355630370) (.leaf 347969018))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 340480350) (.leaf 333160117)) (.branch 108 (.leaf 326004193) (.leaf 319008567))) (.branch 111 (.branch 110 (.leaf 312169343) (.leaf 305482731)) (.branch 112 (.leaf 298945048) (.leaf 292552714)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 286302244) (.leaf 280190251)) (.branch 116 (.leaf 274213440) (.leaf 268368603))) (.branch 119 (.branch 118 (.leaf 262652619) (.leaf 257062452)) (.branch 120 (.leaf 251595144) (.leaf 246247818)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 750).prefactor = (2351491371913243/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 750).cutoff/(generalMeanRows 750).c)).2 =
    (5714978580643/15625000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 750).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 750).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 750).q*(generalMeanRows 750).c/2-2 = (829/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable068.value]
    have hcontinuation : (generalMeanRows 750).q*(generalMeanRows 750).cutoff/2-2 = (1964/945:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable237.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 750).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 750

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 750).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 750).criticalRate j.val*(generalMeanRows 750).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 750).c*(generalMeanRows 750).criticalPoint j.val)).2-
      (generalMeanRows 750).J/2-(generalMeanRows 750).error (generalMeanGrid j.val)+
      (generalMeanRows 750).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 750).c)).2-
      (generalMeanRows 750).J/2-(generalMeanRows 750).error 4 := by
  have he : (generalMeanRows 750).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 750) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 750)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0750

/-! Kernel-checked entropy margins for general spectral rectangle 751. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0751
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4945274834) (.branch 2 (.leaf 4774185171) (.leaf 4610712054))) (.branch 5 (.branch 4 (.leaf 4454425207) (.leaf 4304924593)) (.branch 6 (.leaf 4161837773) (.leaf 4024817554)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3893539885) (.leaf 3767701964)) (.branch 10 (.leaf 3647020539) (.leaf 3531230374))) (.branch 13 (.branch 12 (.leaf 3420082863) (.leaf 3313344768)) (.branch 14 (.leaf 3210797080) (.leaf 3112233979))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3017461882) (.branch 17 (.leaf 2926298580) (.leaf 2838572443))) (.branch 20 (.branch 19 (.leaf 2754121690) (.leaf 2672793725)) (.branch 21 (.leaf 2594444519) (.leaf 2518938046)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2446145759) (.leaf 2375946109)) (.branch 25 (.leaf 2308224101) (.leaf 2242870876))) (.branch 28 (.branch 27 (.leaf 2179783334) (.leaf 2118863776)) (.branch 29 (.leaf 2060019576) (.leaf 2003162874)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1948210291) (.branch 32 (.leaf 1895082662) (.leaf 1843704793))) (.branch 35 (.branch 34 (.leaf 1794005225) (.leaf 1745916022)) (.branch 36 (.leaf 1699372569) (.leaf 1654313382)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1610679935) (.leaf 1568416492)) (.branch 40 (.leaf 1527469955) (.leaf 1487789719))) (.branch 43 (.branch 42 (.leaf 1449327535) (.leaf 1412037383)) (.branch 44 (.leaf 1375875353) (.leaf 1340799533))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1306769901) (.branch 47 (.leaf 1273748230) (.leaf 1241697989))) (.branch 50 (.branch 49 (.leaf 1210584260) (.leaf 1180373653)) (.branch 51 (.leaf 1151034227) (.leaf 1122535418)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1094847970) (.leaf 1067943867)) (.branch 55 (.leaf 1041796275) (.leaf 1016379481))) (.branch 58 (.branch 57 (.leaf 991668838) (.leaf 967640713)) (.branch 59 (.leaf 944272441) (.leaf 921542274))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 899429340) (.branch 62 (.leaf 877913600) (.leaf 856975809))) (.branch 65 (.branch 64 (.leaf 836597480) (.leaf 816760846)) (.branch 66 (.leaf 797448830) (.leaf 778645011)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 760333593) (.leaf 742499381)) (.branch 70 (.leaf 725127749) (.leaf 708204617))) (.branch 73 (.branch 72 (.leaf 691716426) (.leaf 675650115)) (.branch 74 (.leaf 659993101) (.leaf 644733255))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 629858883) (.branch 77 (.leaf 615358710) (.leaf 601221858))) (.branch 80 (.branch 79 (.leaf 587437832) (.leaf 573996503)) (.branch 81 (.leaf 560888094) (.leaf 548103160)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 535632582) (.leaf 523467549)) (.branch 85 (.leaf 511599544) (.leaf 500020337))) (.branch 88 (.branch 87 (.leaf 488721968) (.leaf 477696743)) (.branch 89 (.leaf 466937214) (.leaf 456436179)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 446186665) (.branch 92 (.leaf 436181923) (.leaf 426415420))) (.branch 95 (.branch 94 (.leaf 416880827) (.leaf 407572014)) (.branch 96 (.leaf 398483040) (.leaf 389608152)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 380941769) (.leaf 372478483)) (.branch 100 (.leaf 364213048) (.leaf 356140378))) (.branch 103 (.branch 102 (.leaf 348255538) (.leaf 340553739)) (.branch 104 (.leaf 333030336) (.leaf 325680816))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 318500802) (.leaf 311486042)) (.branch 108 (.leaf 304632407) (.leaf 297935886))) (.branch 111 (.branch 110 (.leaf 291392581) (.leaf 284998708)) (.branch 112 (.leaf 278750585) (.leaf 272644637)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 266677386) (.leaf 260845452)) (.branch 116 (.leaf 255145547) (.leaf 249574474))) (.branch 119 (.branch 118 (.leaf 244129121) (.leaf 238806464)) (.branch 120 (.leaf 233603558) (.leaf 228517537)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 751).prefactor = (591988032608661/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 751).cutoff/(generalMeanRows 751).c)).2 =
    (179269190593833/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 751).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 751).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 751).q*(generalMeanRows 751).c/2-2 = (1699/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable222.value]
    have hcontinuation : (generalMeanRows 751).q*(generalMeanRows 751).cutoff/2-2 = (1964/945:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable237.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 751).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 751

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 751).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 751).criticalRate j.val*(generalMeanRows 751).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 751).c*(generalMeanRows 751).criticalPoint j.val)).2-
      (generalMeanRows 751).J/2-(generalMeanRows 751).error (generalMeanGrid j.val)+
      (generalMeanRows 751).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 751).c)).2-
      (generalMeanRows 751).J/2-(generalMeanRows 751).error 4 := by
  have he : (generalMeanRows 751).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 751) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 751)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0751

/-! Kernel-checked entropy margins for general spectral rectangle 752. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0752
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5275739943) (.branch 2 (.leaf 5101656097) (.leaf 4935265674))) (.branch 5 (.branch 4 (.leaf 4776130194) (.leaf 4623842193)) (.branch 6 (.leaf 4478022521) (.leaf 4338317922)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4204398871) (.leaf 4075957633)) (.branch 10 (.leaf 3952706513) (.leaf 3834376282))) (.branch 13 (.branch 12 (.leaf 3720714748) (.leaf 3611485467)) (.branch 14 (.leaf 3506466563) (.leaf 3405449660))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3308238909) (.branch 17 (.leaf 3214650093) (.leaf 3124509813))) (.branch 20 (.branch 19 (.leaf 3037654738) (.leaf 2953930921)) (.branch 21 (.leaf 2873193161) (.leaf 2795304425)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2720135314) (.leaf 2647563559)) (.branch 25 (.leaf 2577473570) (.leaf 2509756008))) (.branch 28 (.branch 27 (.leaf 2444307395) (.leaf 2381029745)) (.branch 29 (.leaf 2319830229) (.leaf 2260620861)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2203318202) (.branch 32 (.leaf 2147843090) (.leaf 2094120384))) (.branch 35 (.branch 34 (.leaf 2042078733) (.leaf 1991650346)) (.branch 36 (.leaf 1942770795) (.leaf 1895378815)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1849416129) (.leaf 1804827274)) (.branch 40 (.leaf 1761559450) (.leaf 1719562364))) (.branch 43 (.branch 42 (.leaf 1678788099) (.leaf 1639190977)) (.branch 44 (.leaf 1600727443) (.leaf 1563355945))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1527036832) (.branch 47 (.leaf 1491732246) (.leaf 1457406033))) (.branch 50 (.branch 49 (.leaf 1424023649) (.leaf 1391552081)) (.branch 51 (.leaf 1359959760) (.leaf 1329216494)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1299293393) (.leaf 1270162804)) (.branch 55 (.leaf 1241798248) (.leaf 1214174363))) (.branch 58 (.branch 57 (.leaf 1187266845) (.leaf 1161052397)) (.branch 59 (.leaf 1135508681) (.leaf 1110614268))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1086348596) (.branch 62 (.leaf 1062691927) (.leaf 1039625308))) (.branch 65 (.branch 64 (.leaf 1017130533) (.leaf 995190108)) (.branch 66 (.leaf 973787217) (.leaf 952905690)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 932529975) (.leaf 912645108)) (.branch 70 (.leaf 893236683) (.leaf 874290832))) (.branch 73 (.branch 72 (.leaf 855794198) (.leaf 837733911)) (.branch 74 (.leaf 820097568) (.leaf 802873211))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 786049310) (.branch 77 (.leaf 769614739) (.leaf 753558763))) (.branch 80 (.branch 79 (.leaf 737871021) (.leaf 722541507)) (.branch 81 (.leaf 707560557) (.leaf 692918835)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 678607318) (.leaf 664617281)) (.branch 85 (.leaf 650940290) (.leaf 637568186))) (.branch 88 (.branch 87 (.leaf 624493075) (.leaf 611707315)) (.branch 89 (.leaf 599203511) (.leaf 586974501)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 575013346) (.branch 92 (.leaf 563313325) (.leaf 551867924))) (.branch 95 (.branch 94 (.leaf 540670830) (.leaf 529715918)) (.branch 96 (.leaf 518997252) (.leaf 508509072)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 498245787) (.leaf 488201972)) (.branch 100 (.leaf 478372363) (.leaf 468751844))) (.branch 103 (.branch 102 (.leaf 459335450) (.leaf 450118355)) (.branch 104 (.leaf 441095872) (.leaf 432263444))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 423616643) (.leaf 415151163)) (.branch 108 (.leaf 406862816) (.leaf 398747529))) (.branch 111 (.branch 110 (.leaf 390801340) (.leaf 383020393)) (.branch 112 (.leaf 375400936) (.leaf 367939315)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 360631976) (.leaf 353475454)) (.branch 116 (.leaf 346466378) (.leaf 339601463))) (.branch 119 (.branch 118 (.leaf 332877507) (.leaf 326291393)) (.branch 120 (.leaf 319840081) (.leaf 313520609)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 752).prefactor = (958757930237053/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 752).cutoff/(generalMeanRows 752).c)).2 =
    (392187457384243/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 752).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 752).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 752).q*(generalMeanRows 752).c/2-2 = (6161/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable180.value]
    have hcontinuation : (generalMeanRows 752).q*(generalMeanRows 752).cutoff/2-2 = (15986/7611:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable232.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 752).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 752

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 752).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 752).criticalRate j.val*(generalMeanRows 752).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 752).c*(generalMeanRows 752).criticalPoint j.val)).2-
      (generalMeanRows 752).J/2-(generalMeanRows 752).error (generalMeanGrid j.val)+
      (generalMeanRows 752).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 752).c)).2-
      (generalMeanRows 752).J/2-(generalMeanRows 752).error 4 := by
  have he : (generalMeanRows 752).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 752) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 752)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0752

/-! Kernel-checked entropy margins for general spectral rectangle 753. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0753
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5493155527) (.branch 2 (.leaf 5317130300) (.leaf 5148830447))) (.branch 5 (.branch 4 (.leaf 4987814765) (.leaf 4833673321)) (.branch 6 (.leaf 4686024727) (.leaf 4544513694)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4408808859) (.leaf 4278600819)) (.branch 10 (.leaf 4153600371) (.leaf 4033536922))) (.branch 13 (.branch 12 (.leaf 3918157050) (.leaf 3807223198)) (.branch 14 (.leaf 3700512491) (.leaf 3597815655))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3498936036) (.branch 17 (.leaf 3403688695) (.leaf 3311899593))) (.branch 20 (.branch 19 (.leaf 3223404828) (.leaf 3138049945)) (.branch 21 (.leaf 3055689300) (.leaf 2976185471)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2899408716) (.leaf 2825236474)) (.branch 25 (.leaf 2753552904) (.leaf 2684248452))) (.branch 28 (.branch 27 (.leaf 2617219463) (.leaf 2552367805)) (.branch 29 (.leaf 2489600532) (.leaf 2428829567)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2369971404) (.branch 32 (.leaf 2312946837) (.leaf 2257680702))) (.branch 35 (.branch 34 (.leaf 2204101637) (.leaf 2152141863)) (.branch 36 (.leaf 2101736973) (.leaf 2052825740)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2005349932) (.leaf 1959254146)) (.branch 40 (.leaf 1914485646) (.leaf 1870994215))) (.branch 43 (.branch 42 (.leaf 1828732014) (.leaf 1787653456)) (.branch 44 (.leaf 1747715073) (.leaf 1708875413))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1671094920) (.branch 47 (.leaf 1634335841) (.leaf 1598562124))) (.branch 50 (.branch 49 (.leaf 1563739332) (.leaf 1529834557)) (.branch 51 (.leaf 1496816337) (.leaf 1464654589)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1433320527) (.leaf 1402786605)) (.branch 55 (.leaf 1373026450) (.leaf 1344014802))) (.branch 58 (.branch 57 (.leaf 1315727460) (.leaf 1288141228)) (.branch 59 (.leaf 1261233864) (.leaf 1234984036))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1209371275) (.branch 62 (.leaf 1184375935) (.leaf 1159979150))) (.branch 65 (.branch 64 (.leaf 1136162799) (.leaf 1112909471)) (.branch 66 (.leaf 1090202429) (.leaf 1068025581)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1046363445) (.leaf 1025201128)) (.branch 70 (.leaf 1004524291) (.leaf 984319128))) (.branch 73 (.branch 72 (.leaf 964572344) (.leaf 945271123)) (.branch 74 (.leaf 926403117) (.leaf 907956418))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 889919541) (.branch 77 (.leaf 872281404) (.leaf 855031312))) (.branch 80 (.branch 79 (.leaf 838158941) (.leaf 821654319)) (.branch 81 (.leaf 805507811) (.leaf 789710109)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 774252212) (.leaf 759125419)) (.branch 85 (.leaf 744321313) (.leaf 729831749))) (.branch 88 (.branch 87 (.leaf 715648845) (.leaf 701764969)) (.branch 89 (.leaf 688172732) (.leaf 674864975)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 661834760) (.branch 92 (.leaf 649075366) (.leaf 636580273))) (.branch 95 (.branch 94 (.leaf 624343160) (.leaf 612357895)) (.branch 96 (.leaf 600618530) (.leaf 589119288)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 577854566) (.leaf 566818919)) (.branch 100 (.leaf 556007060) (.leaf 545413853))) (.branch 103 (.branch 102 (.leaf 535034306) (.leaf 524863569)) (.branch 104 (.leaf 514896923) (.leaf 505129784))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 495557689) (.leaf 486176299)) (.branch 108 (.leaf 476981390) (.leaf 467968852))) (.branch 111 (.branch 110 (.leaf 459134684) (.leaf 450474990)) (.branch 112 (.leaf 441985975) (.leaf 433663944)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 425505296) (.leaf 417506523)) (.branch 116 (.leaf 409664204) (.leaf 401975007))) (.branch 119 (.branch 118 (.leaf 394435682) (.leaf 387043060)) (.branch 120 (.leaf 379794050) (.leaf 372685637)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 753).prefactor = (603360695062631/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 753).cutoff/(generalMeanRows 753).c)).2 =
    (203641041803363/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 753).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 753).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 753).q*(generalMeanRows 753).c/2-2 = (5829/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable210.value]
    have hcontinuation : (generalMeanRows 753).q*(generalMeanRows 753).cutoff/2-2 = (15986/7611:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable232.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 753).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 753

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 753).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 753).criticalRate j.val*(generalMeanRows 753).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 753).c*(generalMeanRows 753).criticalPoint j.val)).2-
      (generalMeanRows 753).J/2-(generalMeanRows 753).error (generalMeanGrid j.val)+
      (generalMeanRows 753).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 753).c)).2-
      (generalMeanRows 753).J/2-(generalMeanRows 753).error 4 := by
  have he : (generalMeanRows 753).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 753) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 753)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0753

/-! Kernel-checked entropy margins for general spectral rectangle 754. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0754
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5098644306) (.branch 2 (.leaf 4923335422) (.leaf 4755835319))) (.branch 5 (.branch 4 (.leaf 4595701829) (.leaf 4442523896)) (.branch 6 (.leaf 4295918860) (.leaf 4155530034)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4021024543) (.leaf 3892091372)) (.branch 10 (.leaf 3768439621) (.leaf 3649796924))) (.branch 13 (.branch 12 (.leaf 3535908022) (.leaf 3426533468)) (.branch 14 (.leaf 3321448452) (.leaf 3220441727))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3123314637) (.branch 17 (.leaf 3029880224) (.leaf 2939962409))) (.branch 20 (.branch 19 (.leaf 2853395243) (.leaf 2770022222)) (.branch 21 (.leaf 2689695651) (.leaf 2612276064)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2537631685) (.leaf 2465637932)) (.branch 25 (.leaf 2396176958) (.leaf 2329137226))) (.branch 28 (.branch 27 (.leaf 2264413117) (.leaf 2201904560)) (.branch 29 (.leaf 2141516700) (.leaf 2083159575)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2026747828) (.branch 32 (.leaf 1972200433) (.leaf 1919440438))) (.branch 35 (.branch 34 (.leaf 1868394729) (.leaf 1818993808)) (.branch 36 (.leaf 1771171588) (.leaf 1724865194)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1680014788) (.leaf 1636563396)) (.branch 40 (.leaf 1594456748) (.leaf 1553643132))) (.branch 43 (.branch 42 (.leaf 1514073254) (.leaf 1475700106)) (.branch 44 (.leaf 1438478841) (.leaf 1402366661))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1367322709) (.branch 47 (.leaf 1333307960) (.leaf 1300285134))) (.branch 50 (.branch 49 (.leaf 1268218600) (.leaf 1237074290)) (.branch 51 (.leaf 1206819624) (.leaf 1177423430)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1148855872) (.leaf 1121088389)) (.branch 55 (.leaf 1094093624) (.leaf 1067845368))) (.branch 58 (.branch 57 (.leaf 1042318504) (.leaf 1017488952)) (.branch 59 (.leaf 993333618) (.leaf 969830349))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 946957884) (.branch 62 (.leaf 924695817) (.leaf 903024550))) (.branch 65 (.branch 64 (.leaf 881925260) (.leaf 861379859)) (.branch 66 (.leaf 841370963) (.leaf 821881856)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 802896465) (.leaf 784399324)) (.branch 70 (.leaf 766375549) (.leaf 748810815))) (.branch 73 (.branch 72 (.leaf 731691326) (.leaf 715003796)) (.branch 74 (.leaf 698735420) (.leaf 682873863))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 667407228) (.branch 77 (.leaf 652324046) (.leaf 637613254))) (.branch 80 (.branch 79 (.leaf 623264176) (.leaf 609266510)) (.branch 81 (.leaf 595610311) (.leaf 582285974)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 569284223) (.leaf 556596096)) (.branch 85 (.leaf 544212931) (.leaf 532126356))) (.branch 88 (.branch 87 (.leaf 520328275) (.leaf 508810859)) (.branch 89 (.leaf 497566534) (.leaf 486587971)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 475868078) (.branch 92 (.leaf 465399986) (.leaf 455177047))) (.branch 95 (.branch 94 (.leaf 445192821) (.leaf 435441069)) (.branch 96 (.leaf 425915746) (.leaf 416610992)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 407521128) (.leaf 398640646)) (.branch 100 (.leaf 389964206) (.leaf 381486626))) (.branch 103 (.branch 102 (.leaf 373202880) (.leaf 365108089)) (.branch 104 (.leaf 357197520) (.leaf 349466575))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 341910791) (.leaf 334525835)) (.branch 108 (.leaf 327307496) (.leaf 320251684))) (.branch 111 (.branch 110 (.leaf 313354423) (.leaf 306611852)) (.branch 112 (.leaf 300020216) (.leaf 293575864)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 287275246) (.leaf 281114911)) (.branch 116 (.leaf 275091501) (.leaf 269201750))) (.branch 119 (.branch 118 (.leaf 263442479) (.leaf 257810595)) (.branch 120 (.leaf 252303089) (.leaf 246917031)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 754).prefactor = (2418275023126507/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 754).cutoff/(generalMeanRows 754).c)).2 =
    (14573220115251/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 754).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 754).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 754).q*(generalMeanRows 754).c/2-2 = (6659/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable215.value]
    have hcontinuation : (generalMeanRows 754).q*(generalMeanRows 754).cutoff/2-2 = (7950/3827:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable231.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 754).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 754

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 754).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 754).criticalRate j.val*(generalMeanRows 754).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 754).c*(generalMeanRows 754).criticalPoint j.val)).2-
      (generalMeanRows 754).J/2-(generalMeanRows 754).error (generalMeanGrid j.val)+
      (generalMeanRows 754).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 754).c)).2-
      (generalMeanRows 754).J/2-(generalMeanRows 754).error 4 := by
  have he : (generalMeanRows 754).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 754) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 754)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0754

/-! Kernel-checked entropy margins for general spectral rectangle 755. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0755
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5305865244) (.branch 2 (.leaf 5128363158) (.leaf 4958706325))) (.branch 5 (.branch 4 (.leaf 4796449952) (.leaf 4641180604)) (.branch 6 (.leaf 4492513464) (.leaf 4350089888)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4213575224) (.leaf 4082656850)) (.branch 10 (.leaf 3957042405) (.leaf 3836458202))) (.branch 13 (.branch 12 (.leaf 3720647788) (.leaf 3609370632)) (.branch 14 (.leaf 3502400947) (.leaf 3399526606))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3300548161) (.branch 17 (.leaf 3205277936) (.leaf 3113539212))) (.branch 20 (.branch 19 (.leaf 3025165467) (.leaf 2939999681)) (.branch 21 (.leaf 2857893704) (.leaf 2778707662)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2702309418) (.leaf 2628574073)) (.branch 25 (.leaf 2557383501) (.leaf 2488625920))) (.branch 28 (.branch 27 (.leaf 2422195498) (.leaf 2357991985)) (.branch 29 (.leaf 2295920365) (.leaf 2235890548)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2177817064) (.branch 32 (.leaf 2121618796) (.leaf 2067218719))) (.branch 35 (.branch 34 (.leaf 2014543662) (.leaf 1963524083)) (.branch 36 (.leaf 1914093864) (.leaf 1866190112)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1819752979) (.leaf 1774725489)) (.branch 40 (.leaf 1731053381) (.leaf 1688684958))) (.branch 43 (.branch 42 (.leaf 1647570943) (.leaf 1607664354)) (.branch 44 (.leaf 1568920373) (.leaf 1531296235))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1494751116) (.branch 47 (.leaf 1459246030) (.leaf 1424743734))) (.branch 50 (.branch 49 (.leaf 1391208638) (.leaf 1358606716)) (.branch 51 (.leaf 1326905428) (.leaf 1296073641)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1266081563) (.leaf 1236900670)) (.branch 55 (.leaf 1208503644) (.leaf 1180864314))) (.branch 58 (.branch 57 (.leaf 1153957598) (.leaf 1127759450)) (.branch 59 (.leaf 1102246810) (.leaf 1077397552))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1053190447) (.branch 62 (.leaf 1029605112) (.leaf 1006621972))) (.branch 65 (.branch 64 (.leaf 984222226) (.leaf 962387804)) (.branch 66 (.leaf 941101337) (.leaf 920346124)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 900106099) (.leaf 880365805)) (.branch 70 (.leaf 861110365) (.leaf 842325453))) (.branch 73 (.branch 72 (.leaf 823997274) (.leaf 806112537)) (.branch 74 (.leaf 788658434) (.leaf 771622617))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 754993180) (.branch 77 (.leaf 738758639) (.leaf 722907913))) (.branch 80 (.branch 79 (.leaf 707430309) (.leaf 692315501)) (.branch 81 (.leaf 677553520) (.leaf 663134734)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 649049838) (.leaf 635289837)) (.branch 85 (.leaf 621846036) (.leaf 608710027))) (.branch 88 (.branch 87 (.leaf 595873674) (.leaf 583329109)) (.branch 89 (.leaf 571068714) (.leaf 559085115)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 547371173) (.branch 92 (.leaf 535919973) (.leaf 524724814))) (.branch 95 (.branch 94 (.leaf 513779204) (.leaf 503076850)) (.branch 96 (.leaf 492611652) (.leaf 482377693)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 472369234) (.leaf 462580708)) (.branch 100 (.leaf 453006712) (.leaf 443642002))) (.branch 103 (.branch 102 (.leaf 434481487) (.leaf 425520223)) (.branch 104 (.leaf 416753409) (.leaf 408176381))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 399784607) (.leaf 391573682)) (.branch 108 (.leaf 383539325) (.leaf 375677373))) (.branch 111 (.branch 110 (.leaf 367983781) (.leaf 360454610)) (.branch 112 (.leaf 353086032) (.leaf 345874322)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 338815854) (.leaf 331907101)) (.branch 116 (.leaf 325144627) (.leaf 318525088))) (.branch 119 (.branch 118 (.leaf 312045229) (.leaf 305701878)) (.branch 120 (.leaf 299491946) (.leaf 293412425)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 755).prefactor = (4870502885269041/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 755).cutoff/(generalMeanRows 755).c)).2 =
    (94772729616099/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 755).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 755).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 755).q*(generalMeanRows 755).c/2-2 = (6327/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable234.value]
    have hcontinuation : (generalMeanRows 755).q*(generalMeanRows 755).cutoff/2-2 = (7950/3827:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable231.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 755).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 755

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 755).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 755).criticalRate j.val*(generalMeanRows 755).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 755).c*(generalMeanRows 755).criticalPoint j.val)).2-
      (generalMeanRows 755).J/2-(generalMeanRows 755).error (generalMeanGrid j.val)+
      (generalMeanRows 755).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 755).c)).2-
      (generalMeanRows 755).J/2-(generalMeanRows 755).error 4 := by
  have he : (generalMeanRows 755).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 755) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 755)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0755

/-! Kernel-checked entropy margins for general spectral rectangle 756. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0756
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5336405834) (.branch 2 (.leaf 5153092512) (.leaf 4977936185))) (.branch 5 (.branch 4 (.leaf 4810475856) (.leaf 4650282912)) (.branch 6 (.leaf 4496958303) (.leaf 4350130019)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4209450834) (.leaf 4074596285)) (.branch 10 (.leaf 3945262847) (.leaf 3821166295))) (.branch 13 (.branch 12 (.leaf 3702040218) (.leaf 3587634667)) (.branch 14 (.leaf 3477714940) (.leaf 3372060463))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3270463776) (.branch 17 (.leaf 3172729604) (.leaf 3078674012))) (.branch 20 (.branch 19 (.leaf 2988123618) (.leaf 2900914887)) (.branch 21 (.leaf 2816893464) (.leaf 2735913573)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2657837459) (.leaf 2582534868)) (.branch 25 (.leaf 2509882570) (.leaf 2439763920))) (.branch 28 (.branch 27 (.leaf 2372068445) (.leaf 2306691467)) (.branch 29 (.leaf 2243533746) (.leaf 2182501156)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2123504375) (.branch 32 (.leaf 2066458606) (.leaf 2011283306))) (.branch 35 (.branch 34 (.leaf 1957901944) (.leaf 1906241765)) (.branch 36 (.leaf 1856233580) (.leaf 1807811557)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1760913038) (.leaf 1715478361)) (.branch 40 (.leaf 1671450693) (.leaf 1628775875))) (.branch 43 (.branch 42 (.leaf 1587402276) (.leaf 1547280660)) (.branch 44 (.leaf 1508364051) (.leaf 1470607618))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1433968561) (.branch 47 (.leaf 1398406000) (.leaf 1363880880))) (.branch 50 (.branch 49 (.leaf 1330355873) (.leaf 1297795292)) (.branch 51 (.leaf 1266165003) (.leaf 1235432352)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1205566083) (.leaf 1176536275)) (.branch 55 (.leaf 1148314270) (.leaf 1120872615))) (.branch 58 (.branch 57 (.leaf 1094184998) (.leaf 1068226198)) (.branch 59 (.leaf 1042972025) (.leaf 1018399278))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 994485691) (.branch 62 (.leaf 971209892) (.leaf 948551360))) (.branch 65 (.branch 64 (.leaf 926490384) (.leaf 905008026)) (.branch 66 (.leaf 884086086) (.leaf 863707066)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 843854138) (.leaf 824511116)) (.branch 70 (.leaf 805662423) (.leaf 787293067))) (.branch 73 (.branch 72 (.leaf 769388614) (.leaf 751935159)) (.branch 74 (.leaf 734919311) (.leaf 718328163))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 702149273) (.branch 77 (.leaf 686370647) (.leaf 670980715))) (.branch 80 (.branch 79 (.leaf 655968315) (.leaf 641322678)) (.branch 81 (.leaf 627033405) (.leaf 613090460)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 599484147) (.leaf 586205102)) (.branch 85 (.leaf 573244274) (.leaf 560592917))) (.branch 88 (.branch 87 (.leaf 548242575) (.leaf 536185071)) (.branch 89 (.leaf 524412494) (.leaf 512917193)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 501691762) (.branch 92 (.leaf 490729032) (.leaf 480022063))) (.branch 95 (.branch 94 (.leaf 469564133) (.leaf 459348734)) (.branch 96 (.leaf 449369555) (.leaf 439620485)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 430095599) (.leaf 420789153)) (.branch 100 (.leaf 411695575) (.leaf 402809464))) (.branch 103 (.branch 102 (.leaf 394125578) (.leaf 385638831)) (.branch 104 (.leaf 377344287) (.leaf 369237155))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 361312784) (.leaf 353566656)) (.branch 108 (.leaf 345994384) (.leaf 338591706))) (.branch 111 (.branch 110 (.leaf 331354481) (.leaf 324278684)) (.branch 112 (.leaf 317360404) (.leaf 310595840)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 303981293) (.leaf 297513169)) (.branch 116 (.leaf 291187971) (.leaf 285002297))) (.branch 119 (.branch 118 (.leaf 278952838) (.leaf 273036375)) (.branch 120 (.leaf 267249772) (.leaf 261589980)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 756).prefactor = (501967257060917/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 756).cutoff/(generalMeanRows 756).c)).2 =
    (361735217957953/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 756).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 756).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 756).q*(generalMeanRows 756).c/2-2 = (1649/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable204.value]
    have hcontinuation : (generalMeanRows 756).q*(generalMeanRows 756).cutoff/2-2 = (1334/649:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable228.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 756).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 756

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 756).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 756).criticalRate j.val*(generalMeanRows 756).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 756).c*(generalMeanRows 756).criticalPoint j.val)).2-
      (generalMeanRows 756).J/2-(generalMeanRows 756).error (generalMeanGrid j.val)+
      (generalMeanRows 756).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 756).c)).2-
      (generalMeanRows 756).J/2-(generalMeanRows 756).error 4 := by
  have he : (generalMeanRows 756).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 756) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 756)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0756

/-! Kernel-checked entropy margins for general spectral rectangle 757. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0757
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5101708684) (.branch 2 (.leaf 4932085954) (.leaf 4770003614))) (.branch 5 (.branch 4 (.leaf 4615029284) (.leaf 4466761300)) (.branch 6 (.leaf 4324826029) (.leaf 4188875475)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4058585137) (.leaf 3933652084)) (.branch 10 (.leaf 3813793218) (.leaf 3698743715))) (.branch 13 (.branch 12 (.leaf 3588255609) (.leaf 3482096507)) (.branch 14 (.leaf 3380048425) (.leaf 3281906726))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3187479154) (.branch 17 (.leaf 3096584944) (.leaf 3009054019))) (.branch 20 (.branch 19 (.leaf 2924726241) (.leaf 2843450733)) (.branch 21 (.leaf 2765085251) (.leaf 2689495606)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2616555131) (.leaf 2546144192)) (.branch 25 (.leaf 2478149730) (.leaf 2412464844))) (.branch 28 (.branch 27 (.leaf 2348988398) (.leaf 2287624661)) (.branch 29 (.leaf 2228282976) (.leaf 2170877441)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2115326625) (.branch 32 (.leaf 2061553295) (.leaf 2009484169))) (.branch 35 (.branch 34 (.leaf 1959049677) (.leaf 1910183747)) (.branch 36 (.leaf 1862823598) (.leaf 1816909552)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1772384853) (.leaf 1729195506)) (.branch 40 (.leaf 1687290115) (.leaf 1646619741))) (.branch 43 (.branch 42 (.leaf 1607137763) (.leaf 1568799752)) (.branch 44 (.leaf 1531563350) (.leaf 1495388156))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1460235622) (.branch 47 (.leaf 1426068952) (.leaf 1392853010))) (.branch 50 (.branch 49 (.leaf 1360554230) (.leaf 1329140535)) (.branch 51 (.leaf 1298581258) (.leaf 1268847071)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1239909913) (.leaf 1211742927)) (.branch 55 (.leaf 1184320398) (.leaf 1157617696))) (.branch 58 (.branch 57 (.leaf 1131611219) (.leaf 1106278345)) (.branch 59 (.leaf 1081597383) (.leaf 1057547524))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1034108802) (.branch 62 (.leaf 1011262049) (.leaf 988988860))) (.branch 65 (.branch 64 (.leaf 967271555) (.leaf 946093143)) (.branch 66 (.leaf 925437292) (.leaf 905288297)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 885631049) (.leaf 866451010)) (.branch 70 (.leaf 847734185) (.leaf 829467100))) (.branch 73 (.branch 72 (.leaf 811636773) (.leaf 794230696)) (.branch 74 (.leaf 777236813) (.leaf 760643500))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 744439545) (.branch 77 (.leaf 728614131) (.leaf 713156816))) (.branch 80 (.branch 79 (.leaf 698057523) (.leaf 683306517)) (.branch 81 (.leaf 668894396) (.leaf 654812072)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 641050765) (.leaf 627601982)) (.branch 85 (.leaf 614457510) (.leaf 601609404))) (.branch 88 (.branch 87 (.leaf 589049976) (.leaf 576771783)) (.branch 89 (.leaf 564767618) (.leaf 553030502)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 541553675) (.branch 92 (.leaf 530330583) (.leaf 519354877))) (.branch 95 (.branch 94 (.leaf 508620400) (.leaf 498121180)) (.branch 96 (.leaf 487851427) (.leaf 477805520)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 467978007) (.leaf 458363594)) (.branch 100 (.leaf 448957141) (.leaf 439753657))) (.branch 103 (.branch 102 (.leaf 430748293) (.leaf 421936340)) (.branch 104 (.leaf 413313219) (.leaf 404874482))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 396615803) (.leaf 388532976)) (.branch 108 (.leaf 380621910) (.leaf 372878626))) (.branch 111 (.branch 110 (.leaf 365299253) (.leaf 357880024)) (.branch 112 (.leaf 350617272) (.leaf 343507426)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 336547013) (.leaf 329732647)) (.branch 116 (.leaf 323061033) (.leaf 316528959))) (.branch 119 (.branch 118 (.leaf 310133297) (.leaf 303870998)) (.branch 120 (.leaf 297739093) (.leaf 291734684)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 757).prefactor = (592541284316151/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 757).cutoff/(generalMeanRows 757).c)).2 =
    (397164546898687/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 757).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 757).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 757).q*(generalMeanRows 757).c/2-2 = (197/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable218.value]
    have hcontinuation : (generalMeanRows 757).q*(generalMeanRows 757).cutoff/2-2 = (7982/3717:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable245.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 757).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 757

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 757).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 757).criticalRate j.val*(generalMeanRows 757).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 757).c*(generalMeanRows 757).criticalPoint j.val)).2-
      (generalMeanRows 757).J/2-(generalMeanRows 757).error (generalMeanGrid j.val)+
      (generalMeanRows 757).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 757).c)).2-
      (generalMeanRows 757).J/2-(generalMeanRows 757).error 4 := by
  have he : (generalMeanRows 757).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 757) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 757)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0757

/-! Kernel-checked entropy margins for general spectral rectangle 758. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0758
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5432265093) (.branch 2 (.leaf 5253082616) (.leaf 5081790450))) (.branch 5 (.branch 4 (.leaf 4917940885) (.leaf 4761117804)) (.branch 6 (.leaf 4610933921) (.leaf 4467028321)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4329064259) (.leaf 4196727183)) (.branch 10 (.leaf 4069722951) (.leaf 3947776233))) (.branch 13 (.branch 12 (.leaf 3830629057) (.leaf 3718039492)) (.branch 14 (.leaf 3609780454) (.leaf 3505638618))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3405413426) (.branch 17 (.leaf 3308916181) (.leaf 3215969214))) (.branch 20 (.branch 19 (.leaf 3126405125) (.leaf 3040066084)) (.branch 21 (.leaf 2956803189) (.leaf 2876475871)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2798951349) (.leaf 2724104128)) (.branch 25 (.leaf 2651815530) (.leaf 2581973265))) (.branch 28 (.branch 27 (.leaf 2514471026) (.leaf 2449208126)) (.branch 29 (.leaf 2386089146) (.leaf 2325023618)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2265925728) (.branch 32 (.leaf 2208714036) (.leaf 2153311221))) (.branch 35 (.branch 34 (.leaf 2099643835) (.leaf 2047642083)) (.branch 36 (.leaf 1997239610) (.leaf 1948373305)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1900983118) (.leaf 1855011886)) (.branch 40 (.leaf 1810405174) (.leaf 1767111123))) (.branch 43 (.branch 42 (.leaf 1725080309) (.leaf 1684265609)) (.branch 44 (.leaf 1644622080) (.leaf 1606106835))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1568678940) (.branch 47 (.leaf 1532299306) (.leaf 1496930596))) (.branch 50 (.branch 49 (.leaf 1462537127) (.leaf 1429084791)) (.branch 51 (.leaf 1396540970) (.leaf 1364874459)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1334055396) (.leaf 1304055192)) (.branch 55 (.leaf 1274846470) (.leaf 1246403000))) (.branch 58 (.branch 57 (.leaf 1218699647) (.leaf 1191712313)) (.branch 59 (.leaf 1165417888) (.leaf 1139794201))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1114819977) (.branch 62 (.leaf 1090474789) (.leaf 1066739023))) (.branch 65 (.branch 64 (.leaf 1043593836) (.leaf 1021021119)) (.branch 66 (.leaf 999003467) (.leaf 977524139)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 956567036) (.leaf 936116663)) (.branch 70 (.leaf 916158109) (.leaf 896677013))) (.branch 73 (.branch 72 (.leaf 877659546) (.leaf 859092382)) (.branch 74 (.leaf 840962680) (.leaf 823258058))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 805966576) (.branch 77 (.leaf 789076717) (.leaf 772577366))) (.branch 80 (.branch 79 (.leaf 756457795) (.leaf 740707645)) (.branch 81 (.leaf 725316912) (.leaf 710275930)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 695575358) (.leaf 681206168)) (.branch 85 (.leaf 667159627) (.leaf 653427293))) (.branch 88 (.branch 87 (.leaf 640000995) (.leaf 626872826)) (.branch 89 (.leaf 614035133) (.leaf 601480506)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 589201766) (.branch 92 (.leaf 577191962) (.leaf 565444354))) (.branch 95 (.branch 94 (.leaf 553952413) (.leaf 542709807)) (.branch 96 (.leaf 531710395) (.leaf 520948221)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 510417508) (.leaf 500112647)) (.branch 100 (.leaf 490028196) (.leaf 480158869))) (.branch 103 (.branch 102 (.leaf 470499534) (.leaf 461045207)) (.branch 104 (.leaf 451791044) (.leaf 442732339))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 433864519) (.leaf 425183135)) (.branch 108 (.leaf 416683864) (.leaf 408362502))) (.branch 111 (.branch 110 (.leaf 400214957) (.leaf 392237250)) (.branch 112 (.leaf 384425509) (.leaf 376775965)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 369284948) (.leaf 361948886)) (.branch 116 (.leaf 354764301) (.leaf 347727805))) (.branch 119 (.branch 118 (.leaf 340836097) (.leaf 334085962)) (.branch 120 (.leaf 327474267) (.leaf 320997958)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 758).prefactor = (2452347037511983/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 758).cutoff/(generalMeanRows 758).c)).2 =
    (77310727933197/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 758).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 758).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 758).q*(generalMeanRows 758).c/2-2 = (6161/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable180.value]
    have hcontinuation : (generalMeanRows 758).q*(generalMeanRows 758).cutoff/2-2 = (7950/3827:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable231.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 758).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 758

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 758).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 758).criticalRate j.val*(generalMeanRows 758).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 758).c*(generalMeanRows 758).criticalPoint j.val)).2-
      (generalMeanRows 758).J/2-(generalMeanRows 758).error (generalMeanGrid j.val)+
      (generalMeanRows 758).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 758).c)).2-
      (generalMeanRows 758).J/2-(generalMeanRows 758).error 4 := by
  have he : (generalMeanRows 758).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 758) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 758)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0758

/-! Kernel-checked entropy margins for general spectral rectangle 759. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0759
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5655899056) (.branch 2 (.leaf 5474693893) (.leaf 5301412828))) (.branch 5 (.branch 4 (.leaf 5135605335) (.leaf 4976852742)) (.branch 6 (.leaf 4824765442) (.leaf 4678980418)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4539159014) (.leaf 4404984945)) (.branch 10 (.leaf 4276162502) (.leaf 4152414935))) (.branch 13 (.branch 12 (.leaf 4033482987) (.leaf 3919123566)) (.branch 14 (.leaf 3809108542) (.leaf 3703223650))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3601267484) (.branch 17 (.leaf 3503050587) (.leaf 3408394613))) (.branch 20 (.branch 19 (.leaf 3317131557) (.leaf 3229103052)) (.branch 21 (.leaf 3144159718) (.leaf 3062160570)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2982972459) (.leaf 2906469571)) (.branch 25 (.leaf 2832532952) (.leaf 2761050076))) (.branch 28 (.branch 27 (.leaf 2691914438) (.leaf 2625025182)) (.branch 29 (.leaf 2560286754) (.leaf 2497608577)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2436904755) (.branch 32 (.leaf 2378093785) (.leaf 2321098306))) (.branch 35 (.branch 34 (.leaf 2265844850) (.leaf 2212263616)) (.branch 36 (.leaf 2160288258) (.leaf 2109855690)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2060905897) (.leaf 2013381762)) (.branch 40 (.leaf 1967228906) (.leaf 1922395535))) (.branch 43 (.branch 42 (.leaf 1878832295) (.leaf 1836492141)) (.branch 44 (.leaf 1795330212) (.leaf 1755303711))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1716371793) (.branch 47 (.leaf 1678495465) (.leaf 1641637484))) (.branch 50 (.branch 49 (.leaf 1605762270) (.leaf 1570835813)) (.branch 51 (.leaf 1536825595) (.leaf 1503700512)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1471430804) (.leaf 1439987984)) (.branch 55 (.leaf 1409344772) (.leaf 1379475039))) (.branch 58 (.branch 57 (.leaf 1350353746) (.leaf 1321956891)) (.branch 59 (.leaf 1294261458) (.leaf 1267245369))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1240887436) (.branch 62 (.leaf 1215167321) (.leaf 1190065493))) (.branch 65 (.branch 64 (.leaf 1165563191) (.leaf 1141642386)) (.branch 66 (.leaf 1118285748) (.leaf 1095476609)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1073198940) (.leaf 1051437312)) (.branch 70 (.leaf 1030176879) (.leaf 1009403339))) (.branch 73 (.branch 72 (.leaf 989102920) (.leaf 969262352)) (.branch 74 (.leaf 949868841) (.leaf 930910056))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 912374099) (.branch 77 (.leaf 894249493) (.leaf 876525162))) (.branch 80 (.branch 79 (.leaf 859190412) (.leaf 842234914)) (.branch 81 (.leaf 825648694) (.leaf 809422109)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 793545841) (.leaf 778010879)) (.branch 85 (.leaf 762808508) (.leaf 747930297))) (.branch 88 (.branch 87 (.leaf 733368085) (.leaf 719113973)) (.branch 89 (.leaf 705160311) (.leaf 691499691)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 678124934) (.branch 92 (.leaf 665029082) (.leaf 652205393))) (.branch 95 (.branch 94 (.leaf 639647325) (.leaf 627348536)) (.branch 96 (.leaf 615302872) (.leaf 603504361)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 591947206) (.leaf 580625779)) (.branch 100 (.leaf 569534614) (.leaf 558668402))) (.branch 103 (.branch 102 (.leaf 548021983) (.leaf 537590344)) (.branch 104 (.leaf 527368611) (.leaf 517352046))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 507536039) (.leaf 497916108)) (.branch 108 (.leaf 488487892) (.leaf 479247146))) (.branch 111 (.branch 110 (.leaf 470189739) (.leaf 461311649)) (.branch 112 (.leaf 452608960) (.leaf 444077857)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 435714625) (.leaf 427515645)) (.branch 116 (.leaf 419477388) (.leaf 411596416))) (.branch 119 (.branch 118 (.leaf 403869377) (.leaf 396293005)) (.branch 120 (.leaf 388864112) (.leaf 381579590)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 759).prefactor = (4939125288752673/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 759).cutoff/(generalMeanRows 759).c)).2 =
    (401648265888471/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 759).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 759).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 759).q*(generalMeanRows 759).c/2-2 = (5829/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable210.value]
    have hcontinuation : (generalMeanRows 759).q*(generalMeanRows 759).cutoff/2-2 = (7950/3827:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable231.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 759).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 759

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 759).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 759).criticalRate j.val*(generalMeanRows 759).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 759).c*(generalMeanRows 759).criticalPoint j.val)).2-
      (generalMeanRows 759).J/2-(generalMeanRows 759).error (generalMeanGrid j.val)+
      (generalMeanRows 759).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 759).c)).2-
      (generalMeanRows 759).J/2-(generalMeanRows 759).error 4 := by
  have he : (generalMeanRows 759).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 759) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 759)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0759

/-! Kernel-checked entropy margins for general spectral rectangle 760. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0760
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5324389597) (.branch 2 (.leaf 5152451078) (.leaf 4988048796))) (.branch 5 (.branch 4 (.leaf 4830753603) (.leaf 4680166737)) (.branch 6 (.leaf 4535917162) (.leaf 4397659201)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4265070416) (.leaf 4137849708)) (.branch 10 (.leaf 4015715598) (.leaf 3898404690))) (.branch 13 (.branch 12 (.leaf 3785670268) (.leaf 3677281028)) (.branch 14 (.leaf 3573019933) (.leaf 3472683161))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3376079147) (.branch 17 (.leaf 3283027715) (.leaf 3193359275))) (.branch 20 (.branch 19 (.leaf 3106914092) (.leaf 3023541609)) (.branch 21 (.leaf 2943099833) (.leaf 2865454762)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2790479859) (.leaf 2718055567)) (.branch 25 (.leaf 2648068862) (.leaf 2580412833))) (.branch 28 (.branch 27 (.leaf 2514986304) (.leaf 2451693469)) (.branch 29 (.leaf 2390443569) (.leaf 2331150575)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2273732911) (.branch 32 (.leaf 2218113180) (.leaf 2164217917))) (.branch 35 (.branch 34 (.leaf 2111977362) (.leaf 2061325238)) (.branch 36 (.leaf 2012198550) (.leaf 1964537401)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1918284810) (.leaf 1873386549)) (.branch 40 (.leaf 1829790991) (.leaf 1787448960))) (.branch 43 (.branch 42 (.leaf 1746313601) (.leaf 1706340246)) (.branch 44 (.leaf 1667486302) (.leaf 1629711134))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1592975961) (.branch 47 (.leaf 1557243755) (.leaf 1522479154))) (.branch 50 (.branch 49 (.leaf 1488648367) (.leaf 1455719095)) (.branch 51 (.leaf 1423660455) (.leaf 1392442905)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1362038174) (.leaf 1332419200)) (.branch 55 (.leaf 1303560067) (.leaf 1275435948))) (.branch 58 (.branch 57 (.leaf 1248023051) (.leaf 1221298565)) (.branch 59 (.leaf 1195240615) (.leaf 1169828215))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1145041222) (.branch 62 (.leaf 1120860301) (.leaf 1097266879))) (.branch 65 (.branch 64 (.leaf 1074243115) (.leaf 1051771860)) (.branch 66 (.leaf 1029836628) (.leaf 1008421565)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 987511416) (.leaf 967091500)) (.branch 70 (.leaf 947147684) (.leaf 927666358))) (.branch 73 (.branch 72 (.leaf 908634408) (.leaf 890039198)) (.branch 74 (.leaf 871868545) (.leaf 854110704))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 836754341) (.branch 77 (.leaf 819788522) (.leaf 803202692))) (.branch 80 (.branch 79 (.leaf 786986661) (.leaf 771130584)) (.branch 81 (.leaf 755624951) (.leaf 740460572)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 725628559) (.leaf 711120322)) (.branch 85 (.leaf 696927547) (.leaf 683042191))) (.branch 88 (.branch 87 (.leaf 669456471) (.leaf 656162849)) (.branch 89 (.leaf 643154027) (.leaf 630422934)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 617962718) (.branch 92 (.leaf 605766740) (.leaf 593828561))) (.branch 95 (.branch 94 (.leaf 582141939) (.leaf 570700817)) (.branch 96 (.leaf 559499320) (.leaf 548531745)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 537792557) (.leaf 527276381)) (.branch 100 (.leaf 516977997) (.leaf 506892333))) (.branch 103 (.branch 102 (.leaf 497014463) (.leaf 487339597)) (.branch 104 (.leaf 477863081) (.leaf 468580387))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 459487115) (.leaf 450578981)) (.branch 108 (.leaf 441851821) (.leaf 433301580))) (.branch 111 (.branch 110 (.leaf 424924311) (.leaf 416716174)) (.branch 112 (.leaf 408673427) (.leaf 400792429)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 393069630) (.leaf 385501573)) (.branch 116 (.leaf 378084891) (.leaf 370816299))) (.branch 119 (.branch 118 (.leaf 363692599) (.leaf 356710670)) (.branch 120 (.leaf 349867471) (.leaf 343160033)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 760).prefactor = (2363392450278567/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 760).cutoff/(generalMeanRows 760).c)).2 =
    (400743559416903/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 760).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 760).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 760).q*(generalMeanRows 760).c/2-2 = (747/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable220.value]
    have hcontinuation : (generalMeanRows 760).q*(generalMeanRows 760).cutoff/2-2 = (7898/3759:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable241.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 760).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 760

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 760).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 760).criticalRate j.val*(generalMeanRows 760).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 760).c*(generalMeanRows 760).criticalPoint j.val)).2-
      (generalMeanRows 760).J/2-(generalMeanRows 760).error (generalMeanGrid j.val)+
      (generalMeanRows 760).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 760).c)).2-
      (generalMeanRows 760).J/2-(generalMeanRows 760).error 4 := by
  have he : (generalMeanRows 760).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 760) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 760)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0760

/-! Kernel-checked entropy margins for general spectral rectangle 761. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0761
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5451304117) (.branch 2 (.leaf 5277847222) (.leaf 5111967361))) (.branch 5 (.branch 4 (.leaf 4953232588) (.leaf 4801241565)) (.branch 6 (.leaf 4655620890) (.leaf 4516022713)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4382122593) (.leaf 4253617585)) (.branch 10 (.leaf 4130224514) (.leaf 4011678417))) (.branch 13 (.branch 12 (.leaf 3897731133) (.leaf 3788150030)) (.branch 14 (.leaf 3682716841) (.leaf 3581226612))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3483486733) (.branch 17 (.leaf 3389316065) (.leaf 3298544128))) (.branch 20 (.branch 19 (.leaf 3211010365) (.leaf 3126563466)) (.branch 21 (.leaf 3045060738) (.leaf 2966367536)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2890356730) (.leaf 2816908217)) (.branch 25 (.leaf 2745908470) (.leaf 2677250115))) (.branch 28 (.branch 27 (.leaf 2610831548) (.leaf 2546556573)) (.branch 29 (.leaf 2484334067) (.leaf 2424077675)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2365705512) (.branch 32 (.leaf 2309139903) (.leaf 2254307128))) (.branch 35 (.branch 34 (.leaf 2201137191) (.leaf 2149563601)) (.branch 36 (.leaf 2099523167) (.leaf 2050955811)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2003804389) (.leaf 1958014524)) (.branch 40 (.leaf 1913534450) (.leaf 1870314868))) (.branch 43 (.branch 42 (.leaf 1828308810) (.leaf 1787471507)) (.branch 44 (.leaf 1747760271) (.leaf 1709134384))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1671554986) (.branch 47 (.leaf 1634984983) (.leaf 1599388948))) (.branch 50 (.branch 49 (.leaf 1564733035) (.leaf 1530984895)) (.branch 51 (.leaf 1498113598) (.leaf 1466089560)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1434884475) (.leaf 1404471247)) (.branch 55 (.leaf 1374823931) (.leaf 1345917671))) (.branch 58 (.branch 57 (.leaf 1317728652) (.leaf 1290234042)) (.branch 59 (.leaf 1263411946) (.leaf 1237241360))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1211702125) (.branch 62 (.leaf 1186774891) (.leaf 1162441072))) (.branch 65 (.branch 64 (.leaf 1138682814) (.leaf 1115482958)) (.branch 66 (.leaf 1092825006) (.leaf 1070693093)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1049071955) (.leaf 1027946903)) (.branch 70 (.leaf 1007303792) (.leaf 987129004))) (.branch 73 (.branch 72 (.leaf 967409415) (.leaf 948132381)) (.branch 74 (.leaf 929285709) (.leaf 910857643))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 892836841) (.branch 77 (.leaf 875212358) (.leaf 857973628))) (.branch 80 (.branch 79 (.leaf 841110449) (.leaf 824612967)) (.branch 81 (.leaf 808471657) (.leaf 792677318)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 777221049) (.leaf 762094244)) (.branch 85 (.leaf 747288577) (.leaf 732795989))) (.branch 88 (.branch 87 (.leaf 718608681) (.leaf 704719100)) (.branch 89 (.leaf 691119929) (.leaf 677804081)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 664764685) (.branch 92 (.leaf 651995084) (.leaf 639488819))) (.branch 95 (.branch 94 (.leaf 627239627) (.leaf 615241431)) (.branch 96 (.leaf 603488334) (.leaf 591974612)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 580694706) (.leaf 569643218)) (.branch 100 (.leaf 558814903) (.leaf 548204668))) (.branch 103 (.branch 102 (.leaf 537807558) (.leaf 527618759)) (.branch 104 (.leaf 517633591) (.leaf 507847499))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 498256055) (.leaf 488854949)) (.branch 108 (.leaf 479639986) (.leaf 470607084))) (.branch 111 (.branch 110 (.leaf 461752267) (.leaf 453071664)) (.branch 112 (.leaf 444561505) (.leaf 436218116)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 428037918) (.leaf 420017422)) (.branch 116 (.leaf 412153229) (.leaf 404442023))) (.branch 119 (.branch 118 (.leaf 396880572) (.leaf 389465724)) (.branch 120 (.leaf 382194403) (.leaf 375063609)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 761).prefactor = (4759322692815191/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 761).cutoff/(generalMeanRows 761).c)).2 =
    (408234231146061/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 761).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 761).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 761).q*(generalMeanRows 761).c/2-2 = (1453/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable239.value]
    have hcontinuation : (generalMeanRows 761).q*(generalMeanRows 761).cutoff/2-2 = (7898/3759:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable241.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 761).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 761

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 761).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 761).criticalRate j.val*(generalMeanRows 761).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 761).c*(generalMeanRows 761).criticalPoint j.val)).2-
      (generalMeanRows 761).J/2-(generalMeanRows 761).error (generalMeanGrid j.val)+
      (generalMeanRows 761).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 761).c)).2-
      (generalMeanRows 761).J/2-(generalMeanRows 761).error 4 := by
  have he : (generalMeanRows 761).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 761) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 761)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0761

/-! Kernel-checked entropy margins for general spectral rectangle 762. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0762
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5061295524) (.branch 2 (.leaf 4888503491) (.leaf 4723372681))) (.branch 5 (.branch 4 (.leaf 4565470090) (.leaf 4414393173)) (.branch 6 (.leaf 4269767185) (.leaf 4131242808)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3998494034) (.leaf 3871216254)) (.branch 10 (.leaf 3749124550) (.leaf 3631952145))) (.branch 13 (.branch 12 (.leaf 3519449008) (.leaf 3411380587)) (.branch 14 (.leaf 3307526655) (.leaf 3207680261))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3111646781) (.branch 17 (.leaf 3019243037) (.leaf 2930296500))) (.branch 20 (.branch 19 (.leaf 2844644558) (.leaf 2762133843)) (.branch 21 (.leaf 2682619610) (.leaf 2605965167)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2532041349) (.leaf 2460726033)) (.branch 25 (.leaf 2391903690) (.leaf 2325464964))) (.branch 28 (.branch 27 (.leaf 2261306295) (.leaf 2199329554)) (.branch 29 (.leaf 2139441714) (.leaf 2081554542)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2025584311) (.branch 32 (.leaf 1971451535) (.leaf 1919080715))) (.branch 35 (.branch 34 (.leaf 1868400110) (.leaf 1819341522)) (.branch 36 (.leaf 1771840087) (.leaf 1725834093)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1681264795) (.leaf 1638076257)) (.branch 40 (.leaf 1596215189) (.leaf 1555630809))) (.branch 43 (.branch 42 (.leaf 1516274699) (.leaf 1478100681)) (.branch 44 (.leaf 1441064696) (.leaf 1405124692))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1370240514) (.branch 47 (.leaf 1336373807) (.leaf 1303487923))) (.branch 50 (.branch 49 (.leaf 1271547829) (.leaf 1240520027)) (.branch 51 (.leaf 1210372473) (.leaf 1181074505)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1152596773) (.leaf 1124911169)) (.branch 55 (.leaf 1097990774) (.leaf 1071809789))) (.branch 58 (.branch 57 (.leaf 1046343488) (.leaf 1021568160)) (.branch 59 (.leaf 997461063) (.leaf 974000377))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 951165157) (.branch 62 (.leaf 928935296) (.leaf 907291479))) (.branch 65 (.branch 64 (.leaf 886215153) (.leaf 865688487)) (.branch 66 (.leaf 845694338) (.leaf 826216222)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 807238282) (.leaf 788745260)) (.branch 70 (.leaf 770722470) (.leaf 753155773))) (.branch 73 (.branch 72 (.leaf 736031549) (.leaf 719336680)) (.branch 74 (.leaf 703058523) (.leaf 687184891))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 671704032) (.branch 77 (.leaf 656604613) (.leaf 641875701))) (.branch 80 (.branch 79 (.leaf 627506741) (.leaf 613487550)) (.branch 81 (.leaf 599808290) (.leaf 586459464)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 573431893) (.leaf 560716710)) (.branch 85 (.leaf 548305343) (.leaf 536189504))) (.branch 88 (.branch 87 (.leaf 524361178) (.leaf 512812612)) (.branch 89 (.leaf 501536305) (.leaf 490524995)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 479771655) (.branch 92 (.leaf 469269480) (.leaf 459011878))) (.branch 95 (.branch 94 (.leaf 448992465) (.leaf 439205054)) (.branch 96 (.leaf 429643650) (.leaf 420302440)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 411175789) (.leaf 402258232)) (.branch 100 (.leaf 393544468) (.leaf 385029352))) (.branch 103 (.branch 102 (.leaf 376707895) (.leaf 368575251)) (.branch 104 (.leaf 360626718) (.leaf 352857730))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 345263851) (.leaf 337840775)) (.branch 108 (.leaf 330584315) (.leaf 323490406))) (.branch 111 (.branch 110 (.leaf 316555095) (.leaf 309774541)) (.branch 112 (.leaf 303145009) (.leaf 296662867)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 290324582) (.leaf 284126721)) (.branch 116 (.leaf 278065939) (.leaf 272138987))) (.branch 119 (.branch 118 (.leaf 266342698) (.leaf 260673993)) (.branch 120 (.leaf 255129873) (.leaf 249707420)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 762).prefactor = (2384528116498167/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 762).cutoff/(generalMeanRows 762).c)).2 =
    (5714978580643/15625000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 762).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 762).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 762).q*(generalMeanRows 762).c/2-2 = (829/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable068.value]
    have hcontinuation : (generalMeanRows 762).q*(generalMeanRows 762).cutoff/2-2 = (1964/945:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable237.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 762).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 762

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 762).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 762).criticalRate j.val*(generalMeanRows 762).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 762).c*(generalMeanRows 762).criticalPoint j.val)).2-
      (generalMeanRows 762).J/2-(generalMeanRows 762).error (generalMeanGrid j.val)+
      (generalMeanRows 762).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 762).c)).2-
      (generalMeanRows 762).J/2-(generalMeanRows 762).error 4 := by
  have he : (generalMeanRows 762).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 762) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 762)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0762

/-! Kernel-checked entropy margins for general spectral rectangle 763. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0763
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5266005898) (.branch 2 (.leaf 5091079806) (.leaf 4923849574))) (.branch 5 (.branch 4 (.leaf 4763879671) (.leaf 4610765262)) (.branch 6 (.leaf 4464129528) (.leaf 4323621271)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4188912778) (.leaf 4059697898)) (.branch 10 (.leaf 3935690318) (.leaf 3816621998))) (.branch 13 (.branch 12 (.leaf 3702241766) (.leaf 3592314039)) (.branch 14 (.leaf 3486617661) (.leaf 3384944846))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3287100216) (.branch 17 (.leaf 3192899919) (.leaf 3102170823))) (.branch 20 (.branch 19 (.leaf 3014749776) (.leaf 2930482928)) (.branch 21 (.leaf 2849225108) (.leaf 2770839245)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2695195842) (.leaf 2622172483)) (.branch 25 (.leaf 2551653384) (.leaf 2483528969))) (.branch 28 (.branch 27 (.leaf 2417695486) (.leaf 2354054644)) (.branch 29 (.leaf 2292513279) (.leaf 2232983044)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2175380119) (.branch 32 (.leaf 2119624941) (.leaf 2065641955))) (.branch 35 (.branch 34 (.leaf 2013359378) (.leaf 1962708980)) (.branch 36 (.leaf 1913625882) (.leaf 1866048363)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1819917683) (.leaf 1775177914)) (.branch 40 (.leaf 1731775788) (.leaf 1689660544))) (.branch 43 (.branch 42 (.leaf 1648783795) (.leaf 1609099398)) (.branch 44 (.leaf 1570563331) (.leaf 1533133582))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1496770040) (.branch 47 (.leaf 1461434397) (.leaf 1427090050))) (.branch 50 (.branch 49 (.leaf 1393702014) (.leaf 1361236838)) (.branch 51 (.leaf 1329662528) (.leaf 1298948467)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1269065353) (.leaf 1239985125)) (.branch 55 (.leaf 1211680907) (.leaf 1184126945))) (.branch 58 (.branch 57 (.leaf 1157298553) (.leaf 1131172060)) (.branch 59 (.leaf 1105724762) (.leaf 1080934874))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1056781485) (.branch 62 (.leaf 1033244517) (.leaf 1010304686))) (.branch 65 (.branch 64 (.leaf 987943462) (.leaf 966143038)) (.branch 66 (.leaf 944886291) (.leaf 924156755)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 903938588) (.leaf 884216543)) (.branch 70 (.leaf 864975943) (.leaf 846202655))) (.branch 73 (.branch 72 (.leaf 827883064) (.leaf 810004051)) (.branch 74 (.leaf 792552971) (.leaf 775517632))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 758886275) (.branch 77 (.leaf 742647557) (.leaf 726790529))) (.branch 80 (.branch 79 (.leaf 711304623) (.leaf 696179636)) (.branch 81 (.leaf 681405711) (.leaf 666973325)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 652873275) (.leaf 639096664)) (.branch 85 (.leaf 625634891) (.leaf 612479634))) (.branch 88 (.branch 87 (.leaf 599622843) (.leaf 587056727)) (.branch 89 (.leaf 574773746) (.leaf 562766597)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 551028208) (.branch 92 (.leaf 539551730) (.leaf 528330522))) (.branch 95 (.branch 94 (.leaf 517358153) (.leaf 506628383)) (.branch 96 (.leaf 496135165) (.leaf 485872632)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 475835092) (.leaf 466017024)) (.branch 100 (.leaf 456413067) (.leaf 447018017))) (.branch 103 (.branch 102 (.leaf 437826823) (.leaf 428834575)) (.branch 104 (.leaf 420036509) (.leaf 411427991))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 403004522) (.leaf 394761726)) (.branch 108 (.leaf 386695349) (.leaf 378801256))) (.branch 111 (.branch 110 (.leaf 371075424) (.leaf 363513941)) (.branch 112 (.leaf 356113000) (.leaf 348868896)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 341778024) (.leaf 334836876)) (.branch 116 (.leaf 328042033) (.leaf 321390169))) (.branch 119 (.branch 118 (.leaf 314878044) (.leaf 308502501)) (.branch 120 (.leaf 302260467) (.leaf 296148944)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 763).prefactor = (2401220136712229/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 763).cutoff/(generalMeanRows 763).c)).2 =
    (190178714291153/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 763).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 763).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 763).q*(generalMeanRows 763).c/2-2 = (197/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable218.value]
    have hcontinuation : (generalMeanRows 763).q*(generalMeanRows 763).cutoff/2-2 = (1964/945:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable237.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 763).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 763

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 763).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 763).criticalRate j.val*(generalMeanRows 763).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 763).c*(generalMeanRows 763).criticalPoint j.val)).2-
      (generalMeanRows 763).J/2-(generalMeanRows 763).error (generalMeanGrid j.val)+
      (generalMeanRows 763).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 763).c)).2-
      (generalMeanRows 763).J/2-(generalMeanRows 763).error 4 := by
  have he : (generalMeanRows 763).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 763) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 763)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0763

/-! Kernel-checked entropy margins for general spectral rectangle 764. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0764
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5253244344) (.branch 2 (.leaf 5076313342) (.leaf 4907196213))) (.branch 5 (.branch 4 (.leaf 4745451063) (.leaf 4590667113)) (.branch 6 (.leaf 4442461980) (.leaf 4300479258)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4164386342) (.leaf 4033872490)) (.branch 10 (.leaf 3908647069) (.leaf 3788437972))) (.branch 13 (.branch 12 (.leaf 3672990196) (.leaf 3562064541)) (.branch 14 (.leaf 3455436439) (.leaf 3352894878))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3254241427) (.branch 17 (.leaf 3159289347) (.leaf 3067862768))) (.branch 20 (.branch 19 (.leaf 2979795945) (.leaf 2894932566)) (.branch 21 (.leaf 2813125124) (.leaf 2734234330)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2658128577) (.leaf 2584683443)) (.branch 25 (.leaf 2513781236) (.leaf 2445310564))) (.branch 28 (.branch 27 (.leaf 2379165944) (.leaf 2315247436)) (.branch 29 (.leaf 2253460306) (.leaf 2193714706)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2135925388) (.branch 32 (.leaf 2080011425) (.leaf 2025895956))) (.branch 35 (.branch 34 (.leaf 1973505955) (.leaf 1922772003)) (.branch 36 (.leaf 1873628084) (.leaf 1826011392)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1779862146) (.leaf 1735123426)) (.branch 40 (.leaf 1691741012) (.leaf 1649663234))) (.branch 43 (.branch 42 (.leaf 1608840834) (.leaf 1569226833)) (.branch 44 (.leaf 1530776414) (.leaf 1493446797))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1457197141) (.branch 47 (.leaf 1421988434) (.leaf 1387783400))) (.branch 50 (.branch 49 (.leaf 1354546411) (.leaf 1322243398)) (.branch 51 (.leaf 1290841772) (.leaf 1260310351)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1230619287) (.leaf 1201739998)) (.branch 55 (.leaf 1173645105) (.leaf 1146308375))) (.branch 58 (.branch 57 (.leaf 1119704662) (.leaf 1093809852)) (.branch 59 (.leaf 1068600819) (.leaf 1044055370))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1020152204) (.branch 62 (.leaf 996870870) (.leaf 974191725))) (.branch 65 (.branch 64 (.leaf 952095895) (.leaf 930565242)) (.branch 66 (.leaf 909582328) (.leaf 889130383)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 869193273) (.leaf 849755473)) (.branch 70 (.leaf 830802039) (.leaf 812318579))) (.branch 73 (.branch 72 (.leaf 794291234) (.leaf 776706649)) (.branch 74 (.leaf 759551952) (.leaf 742814736))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 726483034) (.branch 77 (.leaf 710545304) (.leaf 694990407))) (.branch 80 (.branch 79 (.leaf 679807593) (.leaf 664986483)) (.branch 81 (.leaf 650517055) (.leaf 636389626)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 622594840) (.leaf 609123654)) (.branch 85 (.leaf 595967326) (.leaf 583117403))) (.branch 88 (.branch 87 (.leaf 570565705) (.leaf 558304321)) (.branch 89 (.leaf 546325593) (.leaf 534622108)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 523186690) (.branch 92 (.leaf 512012385) (.leaf 501092460))) (.branch 95 (.branch 94 (.leaf 490420390) (.leaf 479989849)) (.branch 96 (.leaf 469794706) (.leaf 459829016)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 450087013) (.leaf 440563104)) (.branch 100 (.leaf 431251860) (.leaf 422148014))) (.branch 103 (.branch 102 (.leaf 413246454) (.leaf 404542215)) (.branch 104 (.leaf 396030475) (.leaf 387706553))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 379565898) (.leaf 371604092)) (.branch 108 (.leaf 363816837) (.leaf 356199959))) (.branch 111 (.branch 110 (.leaf 348749397) (.leaf 341461203)) (.branch 112 (.leaf 334331538) (.leaf 327356667)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 320532956) (.leaf 313856871)) (.branch 116 (.leaf 307324969) (.leaf 300933901))) (.branch 119 (.branch 118 (.leaf 294680407) (.leaf 288561312)) (.branch 120 (.leaf 282573525) (.leaf 276714032)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 764).prefactor = (4869911068594073/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 764).cutoff/(generalMeanRows 764).c)).2 =
    (74606277698047/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 764).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 764).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 764).q*(generalMeanRows 764).c/2-2 = (1617/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable243.value]
    have hcontinuation : (generalMeanRows 764).q*(generalMeanRows 764).cutoff/2-2 = (1964/945:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable237.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 764).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 764

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 764).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 764).criticalRate j.val*(generalMeanRows 764).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 764).c*(generalMeanRows 764).criticalPoint j.val)).2-
      (generalMeanRows 764).J/2-(generalMeanRows 764).error (generalMeanGrid j.val)+
      (generalMeanRows 764).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 764).c)).2-
      (generalMeanRows 764).J/2-(generalMeanRows 764).error 4 := by
  have he : (generalMeanRows 764).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 764) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 764)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0764

/-! Kernel-checked entropy margins for general spectral rectangle 765. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0765
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5783832037) (.branch 2 (.leaf 5596025561) (.leaf 5416453586))) (.branch 5 (.branch 4 (.leaf 5244649299) (.leaf 5080178805)) (.branch 6 (.leaf 4922638252) (.leaf 4771651268)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4626866659) (.leaf 4487956360)) (.branch 10 (.leaf 4354613575) (.leaf 4226551110))) (.branch 13 (.branch 12 (.leaf 4103499857) (.leaf 3985207429)) (.branch 14 (.leaf 3871436913) (.leaf 3761965736))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3656584633) (.branch 17 (.leaf 3555096703) (.leaf 3457316546))) (.branch 20 (.branch 19 (.leaf 3363069466) (.leaf 3272190746)) (.branch 21 (.leaf 3184524981) (.leaf 3099925457)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3018253582) (.leaf 2939378366)) (.branch 25 (.leaf 2863175931) (.leaf 2789529063))) (.branch 28 (.branch 27 (.leaf 2718326792) (.leaf 2649464012)) (.branch 29 (.leaf 2582841117) (.leaf 2518363667)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2455942081) (.branch 32 (.leaf 2395491346) (.leaf 2336930747))) (.branch 35 (.branch 34 (.leaf 2280183615) (.leaf 2225177095)) (.branch 36 (.leaf 2171841924) (.leaf 2120112229)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2069925332) (.leaf 2021221572)) (.branch 40 (.leaf 1973944138) (.leaf 1928038911))) (.branch 43 (.branch 42 (.leaf 1883454313) (.leaf 1840141174)) (.branch 44 (.leaf 1798052598) (.leaf 1757143839))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1717372193) (.branch 47 (.leaf 1678696884) (.leaf 1641078962))) (.branch 50 (.branch 49 (.leaf 1604481213) (.leaf 1568868063)) (.branch 51 (.leaf 1534205497) (.leaf 1500460977)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1467603367) (.leaf 1435602864)) (.branch 55 (.leaf 1404430927) (.leaf 1374060219))) (.branch 58 (.branch 57 (.leaf 1344464542) (.leaf 1315618784)) (.branch 59 (.leaf 1287498864) (.leaf 1260081684))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1233345080) (.branch 62 (.leaf 1207267773) (.leaf 1181829336))) (.branch 65 (.branch 64 (.leaf 1157010143) (.leaf 1132791339)) (.branch 66 (.leaf 1109154800) (.leaf 1086083099)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1063559474) (.leaf 1041567799)) (.branch 70 (.leaf 1020092552) (.leaf 999118789))) (.branch 73 (.branch 72 (.leaf 978632119) (.leaf 958618678)) (.branch 74 (.leaf 939065102) (.leaf 919958511))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 901286486) (.branch 77 (.leaf 883037044) (.leaf 865198625))) (.branch 80 (.branch 79 (.leaf 847760070) (.leaf 830710607)) (.branch 81 (.leaf 814039830) (.leaf 797737688)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 781794467) (.leaf 766200778)) (.branch 85 (.leaf 750947542) (.leaf 736025978))) (.branch 88 (.branch 87 (.leaf 721427590) (.leaf 707144156)) (.branch 89 (.leaf 693167718) (.leaf 679490569)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 666105246) (.branch 92 (.leaf 653004516) (.leaf 640181373))) (.branch 95 (.branch 94 (.leaf 627629024) (.leaf 615340883)) (.branch 96 (.leaf 603310562) (.leaf 591531867)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 579998783) (.leaf 568705477)) (.branch 100 (.leaf 557646284) (.leaf 546815704))) (.branch 103 (.branch 102 (.leaf 536208394) (.leaf 525819165)) (.branch 104 (.leaf 515642974) (.leaf 505674919))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 495910237) (.leaf 486344294)) (.branch 108 (.leaf 476972586) (.leaf 467790730))) (.branch 111 (.branch 110 (.leaf 458794462) (.leaf 449979633)) (.branch 112 (.leaf 441342204) (.leaf 432878243)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 424583922) (.leaf 416455513)) (.branch 116 (.leaf 408489384) (.leaf 400681998))) (.branch 119 (.branch 118 (.leaf 393029907) (.leaf 385529752)) (.branch 120 (.leaf 378178257) (.leaf 370972230)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 765).prefactor = (1018352884035543/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 765).cutoff/(generalMeanRows 765).c)).2 =
    (391926190237101/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 765).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 765).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 765).q*(generalMeanRows 765).c/2-2 = (1481/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable171.value]
    have hcontinuation : (generalMeanRows 765).q*(generalMeanRows 765).cutoff/2-2 = (1334/649:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable228.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 765).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 765

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 765).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 765).criticalRate j.val*(generalMeanRows 765).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 765).c*(generalMeanRows 765).criticalPoint j.val)).2-
      (generalMeanRows 765).J/2-(generalMeanRows 765).error (generalMeanGrid j.val)+
      (generalMeanRows 765).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 765).c)).2-
      (generalMeanRows 765).J/2-(generalMeanRows 765).error 4 := by
  have he : (generalMeanRows 765).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 765) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 765)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0765

/-! Kernel-checked entropy margins for general spectral rectangle 766. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0766
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5001385059) (.branch 2 (.leaf 4830397386) (.leaf 4667070053))) (.branch 5 (.branch 4 (.leaf 4510964438) (.leaf 4361673016)) (.branch 6 (.leaf 4218816647) (.leaf 4082042147)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3951020124) (.leaf 3825443028)) (.branch 10 (.leaf 3705023401) (.leaf 3589492288))) (.branch 13 (.branch 12 (.leaf 3478597814) (.leaf 3372103877)) (.branch 14 (.leaf 3269788978) (.leaf 3171445137))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3076876923) (.branch 17 (.leaf 2985900552) (.leaf 2898343069))) (.branch 20 (.branch 19 (.leaf 2814041600) (.leaf 2732842656)) (.branch 21 (.leaf 2654601503) (.leaf 2579181578)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2506453946) (.leaf 2436296807)) (.branch 25 (.leaf 2368595030) (.leaf 2303239736))) (.branch 28 (.branch 27 (.leaf 2240127897) (.leaf 2179161971)) (.branch 29 (.leaf 2120249567) (.leaf 2063303124)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2008239622) (.branch 32 (.leaf 1954980308) (.leaf 1903450438))) (.branch 35 (.branch 34 (.leaf 1853579048) (.leaf 1805298724)) (.branch 36 (.leaf 1758545401) (.leaf 1713258170)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1669379095) (.leaf 1626853045)) (.branch 40 (.leaf 1585627540) (.leaf 1545652596))) (.branch 43 (.branch 42 (.leaf 1506880594) (.leaf 1469266145)) (.branch 44 (.leaf 1432765970) (.leaf 1397338783))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1362945190) (.branch 47 (.leaf 1329547581) (.leaf 1297110038))) (.branch 50 (.branch 49 (.leaf 1265598248) (.leaf 1234979413)) (.branch 51 (.leaf 1205222180) (.leaf 1176296556)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1148173847) (.leaf 1120826587)) (.branch 55 (.leaf 1094228478) (.leaf 1068354329))) (.branch 58 (.branch 57 (.leaf 1043180004) (.leaf 1018682366)) (.branch 59 (.leaf 994839230) (.leaf 971629315))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 949032203) (.branch 62 (.leaf 927028294) (.leaf 905598766))) (.branch 65 (.branch 64 (.leaf 884725543) (.leaf 864391255)) (.branch 66 (.leaf 844579205) (.leaf 825273340)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 806458221) (.leaf 788118991)) (.branch 70 (.leaf 770241353) (.leaf 752811541))) (.branch 73 (.branch 72 (.leaf 735816299) (.leaf 719242854)) (.branch 74 (.leaf 703078901) (.leaf 687312576))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 671932437) (.branch 77 (.leaf 656927451) (.leaf 642286972))) (.branch 80 (.branch 79 (.leaf 628000725) (.leaf 614058789)) (.branch 81 (.leaf 600451586) (.leaf 587169862)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 574204676) (.leaf 561547387)) (.branch 85 (.leaf 549189640) (.leaf 537123356))) (.branch 88 (.branch 87 (.leaf 525340721) (.leaf 513834173)) (.branch 89 (.leaf 502596395) (.leaf 491620303)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 480899037) (.branch 92 (.leaf 470425954) (.leaf 460194619))) (.branch 95 (.branch 94 (.leaf 450198794) (.leaf 440432435)) (.branch 96 (.leaf 430889683) (.leaf 421564853)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 412452436) (.leaf 403547085)) (.branch 100 (.leaf 394843611) (.leaf 386336979))) (.branch 103 (.branch 102 (.leaf 378022302) (.leaf 369894834)) (.branch 104 (.leaf 361949967) (.leaf 354183223))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 346590253) (.leaf 339166832)) (.branch 108 (.leaf 331908853) (.leaf 324812322))) (.branch 111 (.branch 110 (.leaf 317873359) (.leaf 311088189)) (.branch 112 (.leaf 304453141) (.leaf 297964644)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 291619225) (.leaf 285413503)) (.branch 116 (.leaf 279344187) (.leaf 273408077))) (.branch 119 (.branch 118 (.leaf 267602054) (.leaf 261923084)) (.branch 120 (.leaf 256368211) (.leaf 250934556)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 766).prefactor = (1200922140434843/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 766).cutoff/(generalMeanRows 766).c)).2 =
    (76513149495507/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 766).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 766).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 766).q*(generalMeanRows 766).c/2-2 = (829/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable068.value]
    have hcontinuation : (generalMeanRows 766).q*(generalMeanRows 766).cutoff/2-2 = (7982/3717:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable245.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 766).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 766

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 766).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 766).criticalRate j.val*(generalMeanRows 766).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 766).c*(generalMeanRows 766).criticalPoint j.val)).2-
      (generalMeanRows 766).J/2-(generalMeanRows 766).error (generalMeanGrid j.val)+
      (generalMeanRows 766).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 766).c)).2-
      (generalMeanRows 766).J/2-(generalMeanRows 766).error 4 := by
  have he : (generalMeanRows 766).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 766) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 766)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0766

/-! Kernel-checked entropy margins for general spectral rectangle 767. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0767
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5594761995) (.branch 2 (.leaf 5405320600) (.leaf 5224244591))) (.branch 5 (.branch 4 (.leaf 5051062994) (.leaf 4885337874)) (.branch 6 (.leaf 4726661447) (.leaf 4574653511)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4428959146) (.leaf 4289246648)) (.branch 10 (.leaf 4155205669) (.leaf 4026545551))) (.branch 13 (.branch 12 (.leaf 3902993802) (.leaf 3784294729)) (.branch 14 (.leaf 3670208191) (.leaf 3560508461))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3454983195) (.branch 17 (.leaf 3353432482) (.leaf 3255667985))) (.branch 20 (.branch 19 (.leaf 3161512139) (.leaf 3070797427)) (.branch 21 (.leaf 2983365710) (.leaf 2899067608)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2817761928) (.leaf 2739315143)) (.branch 25 (.leaf 2663600900) (.leaf 2590499574))) (.branch 28 (.branch 27 (.leaf 2519897848) (.leaf 2451688327)) (.branch 29 (.leaf 2385769175) (.leaf 2322043785)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2260420464) (.branch 32 (.leaf 2200812145) (.leaf 2143136115))) (.branch 35 (.branch 34 (.leaf 2087313764) (.leaf 2033270349)) (.branch 36 (.leaf 1980934774) (.leaf 1930239382)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1881119766) (.leaf 1833514587)) (.branch 40 (.leaf 1787365403) (.leaf 1742616513))) (.branch 43 (.branch 42 (.leaf 1699214808) (.leaf 1657109628)) (.branch 44 (.leaf 1616252638) (.leaf 1576597698))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1538100748) (.branch 47 (.leaf 1500719703) (.leaf 1464414348))) (.branch 50 (.branch 49 (.leaf 1429146239) (.leaf 1394878618)) (.branch 51 (.leaf 1361576320) (.leaf 1329205699)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1297734547) (.leaf 1267132023)) (.branch 55 (.leaf 1237368587) (.leaf 1208415935))) (.branch 58 (.branch 57 (.leaf 1180246936) (.leaf 1152835580)) (.branch 59 (.leaf 1126156917) (.leaf 1100187013))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1074902895) (.branch 62 (.leaf 1050282511) (.leaf 1026304682))) (.branch 65 (.branch 64 (.leaf 1002949064) (.leaf 980196107)) (.branch 66 (.leaf 958027021) (.leaf 936423737)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 915368878) (.leaf 894845724)) (.branch 70 (.leaf 874838186) (.leaf 855330773))) (.branch 73 (.branch 72 (.leaf 836308570) (.leaf 817757211)) (.branch 74 (.leaf 799662851) (.leaf 782012150))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 764792246) (.branch 77 (.leaf 747990734) (.leaf 731595651))) (.branch 80 (.branch 79 (.leaf 715595452) (.leaf 699978995)) (.branch 81 (.leaf 684735524) (.leaf 669854653)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 655326347) (.leaf 641140914)) (.branch 85 (.leaf 627288984) (.leaf 613761503))) (.branch 88 (.branch 87 (.leaf 600549712) (.leaf 587645142)) (.branch 89 (.leaf 575039601) (.leaf 562725159)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 550694143) (.branch 92 (.leaf 538939123) (.leaf 527452905))) (.branch 95 (.branch 94 (.leaf 516228520) (.leaf 505259217)) (.branch 96 (.leaf 494538454) (.leaf 484059890)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 473817378) (.leaf 463804955)) (.branch 100 (.leaf 454016841) (.leaf 444447425))) (.branch 103 (.branch 102 (.leaf 435091266) (.leaf 425943082)) (.branch 104 (.leaf 416997745) (.leaf 408250276))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 399695842) (.leaf 391329745)) (.branch 108 (.leaf 383147426) (.leaf 375144450))) (.branch 111 (.branch 110 (.leaf 367316511) (.leaf 359659420)) (.branch 112 (.leaf 352169108) (.leaf 344841615)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 337673092) (.leaf 330659795)) (.branch 116 (.leaf 323798079) (.leaf 317084402))) (.branch 119 (.branch 118 (.leaf 310515312) (.leaf 304087452)) (.branch 120 (.leaf 297797554) (.leaf 291642435)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 767).prefactor = (642784292491533/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 767).cutoff/(generalMeanRows 767).c)).2 =
    (45445515180161/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 767).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 767).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 767).q*(generalMeanRows 767).c/2-2 = (1607/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable174.value]
    have hcontinuation : (generalMeanRows 767).q*(generalMeanRows 767).cutoff/2-2 = (1990/979:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable227.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 767).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 767

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 767).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 767).criticalRate j.val*(generalMeanRows 767).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 767).c*(generalMeanRows 767).criticalPoint j.val)).2-
      (generalMeanRows 767).J/2-(generalMeanRows 767).error (generalMeanGrid j.val)+
      (generalMeanRows 767).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 767).c)).2-
      (generalMeanRows 767).J/2-(generalMeanRows 767).error 4 := by
  have he : (generalMeanRows 767).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 767) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 767)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0767

/-! Kernel-checked entropy margins for general spectral rectangle 768. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0768
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4915377277) (.branch 2 (.leaf 4742855708) (.leaf 4578100377))) (.branch 5 (.branch 4 (.leaf 4420668944) (.leaf 4270150284)) (.branch 6 (.leaf 4126161767) (.leaf 3988346826)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3856372784) (.leaf 3729928898)) (.branch 10 (.leaf 3608724607) (.leaf 3492487942))) (.branch 13 (.branch 12 (.leaf 3380964092) (.leaf 3273914105)) (.branch 14 (.leaf 3171113705) (.leaf 3072352217))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2977431583) (.branch 17 (.leaf 2886165466) (.leaf 2798378432))) (.branch 20 (.branch 19 (.leaf 2713905193) (.leaf 2632589917)) (.branch 21 (.leaf 2554285591) (.leaf 2478853439)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2406162378) (.leaf 2336088518)) (.branch 25 (.leaf 2268514706) (.leaf 2203330096))) (.branch 28 (.branch 27 (.leaf 2140429753) (.leaf 2079714287)) (.branch 29 (.leaf 2021089515) (.leaf 1964466138)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1909759454) (.branch 32 (.leaf 1856889078) (.leaf 1805778691))) (.branch 35 (.branch 34 (.leaf 1756355798) (.leaf 1708551510)) (.branch 36 (.leaf 1662300331) (.leaf 1617539969)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1574211153) (.leaf 1532257461)) (.branch 40 (.leaf 1491625164) (.leaf 1452263076))) (.branch 43 (.branch 42 (.leaf 1414122412) (.leaf 1377156663)) (.branch 44 (.leaf 1341321466) (.leaf 1306574493))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1272875341) (.branch 47 (.leaf 1240185432) (.leaf 1208467912))) (.branch 50 (.branch 49 (.leaf 1177687568) (.leaf 1147810736)) (.branch 51 (.leaf 1118805228) (.leaf 1090640251)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1063286337) (.leaf 1036715279)) (.branch 55 (.leaf 1010900066) (.leaf 985814823))) (.branch 58 (.branch 57 (.leaf 961434756) (.leaf 937736095)) (.branch 59 (.leaf 914696052) (.leaf 892292765))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 870505258) (.branch 62 (.leaf 849313398) (.leaf 828697852))) (.branch 65 (.branch 64 (.leaf 808640055) (.leaf 789122169)) (.branch 66 (.leaf 770127049) (.leaf 751638215)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 733639818) (.leaf 716116612)) (.branch 70 (.leaf 699053926) (.leaf 682437640))) (.branch 73 (.branch 72 (.leaf 666254158) (.leaf 650490388)) (.branch 74 (.leaf 635133713) (.leaf 620171980))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 605593470) (.branch 77 (.leaf 591386886) (.leaf 577541332))) (.branch 80 (.branch 79 (.leaf 564046294) (.leaf 550891630)) (.branch 81 (.leaf 538067548) (.leaf 525564593)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 513373635) (.leaf 501485855)) (.branch 85 (.leaf 489892728) (.leaf 478586020))) (.branch 88 (.branch 87 (.leaf 467557765) (.leaf 456800265)) (.branch 89 (.leaf 446306070) (.leaf 436067976)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 426079011) (.branch 92 (.leaf 416332424) (.leaf 406821683))) (.branch 95 (.branch 94 (.leaf 397540460) (.leaf 388482628)) (.branch 96 (.leaf 379642251) (.leaf 371013576)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 362591027) (.leaf 354369201)) (.branch 100 (.leaf 346342858) (.leaf 338506917))) (.branch 103 (.branch 102 (.leaf 330856447) (.leaf 323386668)) (.branch 104 (.leaf 316092940) (.leaf 308970760))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 302015756) (.leaf 295223685)) (.branch 108 (.leaf 288590426) (.leaf 282111977))) (.branch 111 (.branch 110 (.leaf 275784450) (.leaf 269604068)) (.branch 112 (.leaf 263567162) (.leaf 257670164)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 251909608) (.leaf 246282124)) (.branch 116 (.leaf 240784435) (.leaf 235413354))) (.branch 119 (.branch 118 (.leaf 230165782) (.leaf 225038706)) (.branch 120 (.leaf 220029191) (.leaf 215134385)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 768).prefactor = (2423441689413217/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 768).cutoff/(generalMeanRows 768).c)).2 =
    (181271596153589/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 768).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 768).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 768).q*(generalMeanRows 768).c/2-2 = (87/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable246.value]
    have hcontinuation : (generalMeanRows 768).q*(generalMeanRows 768).cutoff/2-2 = (3970/1869:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable240.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 768).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 768

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 768).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 768).criticalRate j.val*(generalMeanRows 768).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 768).c*(generalMeanRows 768).criticalPoint j.val)).2-
      (generalMeanRows 768).J/2-(generalMeanRows 768).error (generalMeanGrid j.val)+
      (generalMeanRows 768).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 768).c)).2-
      (generalMeanRows 768).J/2-(generalMeanRows 768).error 4 := by
  have he : (generalMeanRows 768).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 768) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 768)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0768

/-! Kernel-checked entropy margins for general spectral rectangle 769. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0769
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5034697862) (.branch 2 (.leaf 4862571289) (.leaf 4698156078))) (.branch 5 (.branch 4 (.leaf 4541010688) (.leaf 4390724879)) (.branch 6 (.leaf 4246916984) (.leaf 4109231468)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3977336744) (.leaf 3850923216)) (.branch 10 (.leaf 3729701507) (.leaf 3613400875))) (.branch 13 (.branch 12 (.leaf 3501767764) (.leaf 3394564502)) (.branch 14 (.leaf 3291568112) (.leaf 3192569231))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3097371125) (.branch 17 (.leaf 3005788786) (.leaf 2917648108))) (.branch 20 (.branch 19 (.leaf 2832785130) (.leaf 2751045343)) (.branch 21 (.leaf 2672283048) (.leaf 2596360773)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2523148723) (.leaf 2452524286)) (.branch 25 (.leaf 2384371567) (.leaf 2318580961))) (.branch 28 (.branch 27 (.leaf 2255048751) (.leaf 2193676749)) (.branch 29 (.leaf 2134371946) (.leaf 2077046199)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2021615935) (.branch 32 (.leaf 1968001875) (.leaf 1916128780))) (.branch 35 (.branch 34 (.leaf 1865925211) (.leaf 1817323305)) (.branch 36 (.leaf 1770258572) (.leaf 1724669695)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1680498354) (.leaf 1637689050)) (.branch 40 (.leaf 1596188954) (.leaf 1555947748))) (.branch 43 (.branch 42 (.leaf 1516917497) (.leaf 1479052509)) (.branch 44 (.leaf 1442309216) (.leaf 1406646059))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1372023380) (.branch 47 (.leaf 1338403319) (.leaf 1305749719))) (.branch 50 (.branch 49 (.leaf 1274028038) (.leaf 1243205260)) (.branch 51 (.leaf 1213249821) (.leaf 1184131532)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1155821506) (.leaf 1128292094)) (.branch 55 (.leaf 1101516822) (.leaf 1075470334))) (.branch 58 (.branch 57 (.leaf 1050128329) (.leaf 1025467519)) (.branch 59 (.leaf 1001465571) (.leaf 978101062))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 955353437) (.branch 62 (.leaf 933202965) (.leaf 911630702))) (.branch 65 (.branch 64 (.leaf 890618448) (.leaf 870148719)) (.branch 66 (.leaf 850204706) (.leaf 830770251)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 811829809) (.leaf 793368427)) (.branch 70 (.leaf 775371711) (.leaf 757825804))) (.branch 73 (.branch 72 (.leaf 740717361) (.leaf 724033526)) (.branch 74 (.leaf 707761910) (.leaf 691890569))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 676407988) (.branch 77 (.leaf 661303058) (.leaf 646565063))) (.branch 80 (.branch 79 (.leaf 632183659) (.leaf 618148860)) (.branch 81 (.leaf 604451023) (.leaf 591080833)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 578029290) (.leaf 565287694)) (.branch 85 (.leaf 552847635) (.leaf 540700982))) (.branch 88 (.branch 87 (.leaf 528839866) (.leaf 517256676)) (.branch 89 (.leaf 505944046) (.leaf 494894845)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 484102169) (.branch 92 (.leaf 473559328) (.leaf 463259844))) (.branch 95 (.branch 94 (.leaf 453197440) (.leaf 443366031)) (.branch 96 (.leaf 433759716) (.leaf 424372777)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 415199664) (.leaf 406234997)) (.branch 100 (.leaf 397473552) (.leaf 388910260))) (.branch 103 (.branch 102 (.leaf 380540201) (.leaf 372358599)) (.branch 104 (.leaf 364360812) (.leaf 356542336))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 348898792) (.leaf 341425926)) (.branch 108 (.leaf 334119603) (.leaf 326975804))) (.branch 111 (.branch 110 (.leaf 319990623) (.leaf 313160259)) (.branch 112 (.leaf 306481017) (.leaf 299949302)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 293561618) (.leaf 287314561)) (.branch 116 (.leaf 281204820) (.leaf 275229170))) (.branch 119 (.branch 118 (.leaf 269384475) (.leaf 263667679)) (.branch 120 (.leaf 258075806) (.leaf 252605959)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 769).prefactor = (2417842282090307/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 769).cutoff/(generalMeanRows 769).c)).2 =
    (76513149495507/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 769).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 769).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 769).q*(generalMeanRows 769).c/2-2 = (829/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable068.value]
    have hcontinuation : (generalMeanRows 769).q*(generalMeanRows 769).cutoff/2-2 = (7982/3717:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable245.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 769).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 769

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 769).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 769).criticalRate j.val*(generalMeanRows 769).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 769).c*(generalMeanRows 769).criticalPoint j.val)).2-
      (generalMeanRows 769).J/2-(generalMeanRows 769).error (generalMeanGrid j.val)+
      (generalMeanRows 769).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 769).c)).2-
      (generalMeanRows 769).J/2-(generalMeanRows 769).error 4 := by
  have he : (generalMeanRows 769).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 769) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 769)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0769

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock10 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 10 i) := by
  fin_cases i
  · exact EntropyRow0700.numerical
  · exact EntropyRow0701.numerical
  · exact EntropyRow0702.numerical
  · exact EntropyRow0703.numerical
  · exact EntropyRow0704.numerical
  · exact EntropyRow0705.numerical
  · exact EntropyRow0706.numerical
  · exact EntropyRow0707.numerical
  · exact EntropyRow0708.numerical
  · exact EntropyRow0709.numerical
  · exact EntropyRow0710.numerical
  · exact EntropyRow0711.numerical
  · exact EntropyRow0712.numerical
  · exact EntropyRow0713.numerical
  · exact EntropyRow0714.numerical
  · exact EntropyRow0715.numerical
  · exact EntropyRow0716.numerical
  · exact EntropyRow0717.numerical
  · exact EntropyRow0718.numerical
  · exact EntropyRow0719.numerical
  · exact EntropyRow0720.numerical
  · exact EntropyRow0721.numerical
  · exact EntropyRow0722.numerical
  · exact EntropyRow0723.numerical
  · exact EntropyRow0724.numerical
  · exact EntropyRow0725.numerical
  · exact EntropyRow0726.numerical
  · exact EntropyRow0727.numerical
  · exact EntropyRow0728.numerical
  · exact EntropyRow0729.numerical
  · exact EntropyRow0730.numerical
  · exact EntropyRow0731.numerical
  · exact EntropyRow0732.numerical
  · exact EntropyRow0733.numerical
  · exact EntropyRow0734.numerical
  · exact EntropyRow0735.numerical
  · exact EntropyRow0736.numerical
  · exact EntropyRow0737.numerical
  · exact EntropyRow0738.numerical
  · exact EntropyRow0739.numerical
  · exact EntropyRow0740.numerical
  · exact EntropyRow0741.numerical
  · exact EntropyRow0742.numerical
  · exact EntropyRow0743.numerical
  · exact EntropyRow0744.numerical
  · exact EntropyRow0745.numerical
  · exact EntropyRow0746.numerical
  · exact EntropyRow0747.numerical
  · exact EntropyRow0748.numerical
  · exact EntropyRow0749.numerical
  · exact EntropyRow0750.numerical
  · exact EntropyRow0751.numerical
  · exact EntropyRow0752.numerical
  · exact EntropyRow0753.numerical
  · exact EntropyRow0754.numerical
  · exact EntropyRow0755.numerical
  · exact EntropyRow0756.numerical
  · exact EntropyRow0757.numerical
  · exact EntropyRow0758.numerical
  · exact EntropyRow0759.numerical
  · exact EntropyRow0760.numerical
  · exact EntropyRow0761.numerical
  · exact EntropyRow0762.numerical
  · exact EntropyRow0763.numerical
  · exact EntropyRow0764.numerical
  · exact EntropyRow0765.numerical
  · exact EntropyRow0766.numerical
  · exact EntropyRow0767.numerical
  · exact EntropyRow0768.numerical
  · exact EntropyRow0769.numerical
end SingularValueBounds.KL.Certificates
