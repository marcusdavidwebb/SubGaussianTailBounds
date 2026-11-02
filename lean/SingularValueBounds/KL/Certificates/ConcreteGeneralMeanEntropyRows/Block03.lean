import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs
import SingularValueBounds.KL.Certificates.GeneralMeanPrefactorLogs
import SingularValueBounds.KL.Certificates.IntegerResolventEvaluation
import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block01
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block02
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block03
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block04
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block05
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block06
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block07
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 210. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0210
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4880584062) (.branch 2 (.leaf 4702777804) (.leaf 4533283267))) (.branch 5 (.branch 4 (.leaf 4371613838) (.leaf 4217317686)) (.branch 6 (.leaf 4069974729) (.leaf 3929193926)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3794610846) (.leaf 3665885493)) (.branch 10 (.leaf 3542700338) (.leaf 3424758549))) (.branch 13 (.branch 12 (.leaf 3311782382) (.leaf 3203511731)) (.branch 14 (.leaf 3099702800) (.leaf 3000126898))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2904569343) (.branch 17 (.leaf 2812828453) (.leaf 2724714629))) (.branch 20 (.branch 19 (.leaf 2640049508) (.leaf 2558665189)) (.branch 21 (.leaf 2480403523) (.leaf 2405115452)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2332660408) (.leaf 2262905752)) (.branch 25 (.leaf 2195726257) (.leaf 2131003633))) (.branch 28 (.branch 27 (.leaf 2068626083) (.leaf 2008487891)) (.branch 29 (.leaf 1950489044) (.leaf 1894534878)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1840535748) (.branch 32 (.leaf 1788406723) (.leaf 1738067301))) (.branch 35 (.branch 34 (.leaf 1689441144) (.leaf 1642455830)) (.branch 36 (.leaf 1597042624) (.leaf 1553136258)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1510674736) (.leaf 1469599139)) (.branch 40 (.leaf 1429853456) (.leaf 1391384410))) (.branch 43 (.branch 42 (.leaf 1354141314) (.leaf 1318075918)) (.branch 44 (.leaf 1283142277) (.leaf 1249296625))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1216497251) (.branch 47 (.leaf 1184704393) (.leaf 1153880127))) (.branch 50 (.branch 49 (.leaf 1123988272) (.leaf 1094994297)) (.branch 51 (.leaf 1066865230) (.leaf 1039569579)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1013077254) (.leaf 987359494)) (.branch 55 (.leaf 962388796) (.leaf 938138856))) (.branch 58 (.branch 57 (.leaf 914584502) (.leaf 891701639)) (.branch 59 (.leaf 869467196) (.leaf 847859072))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 826856090) (.branch 62 (.leaf 806437951) (.leaf 786585191))) (.branch 65 (.branch 64 (.leaf 767279139) (.leaf 748501879)) (.branch 66 (.leaf 730236216) (.leaf 712465638)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 695174286) (.leaf 678346922)) (.branch 70 (.leaf 661968902) (.leaf 646026145))) (.branch 73 (.branch 72 (.leaf 630505109) (.leaf 615392765)) (.branch 74 (.leaf 600676578) (.leaf 586344478))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 572384842) (.branch 77 (.leaf 558786477) (.leaf 545538596))) (.branch 80 (.branch 79 (.leaf 532630802) (.leaf 520053074)) (.branch 81 (.leaf 507795745) (.leaf 495849491)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 484205315) (.leaf 472854532)) (.branch 85 (.leaf 461788758) (.leaf 450999897))) (.branch 88 (.branch 87 (.leaf 440480125) (.leaf 430221886)) (.branch 89 (.leaf 420217875) (.leaf 410461030)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 400944521) (.branch 92 (.leaf 391661745) (.leaf 382606310))) (.branch 95 (.branch 94 (.leaf 373772033) (.leaf 365152926)) (.branch 96 (.leaf 356743196) (.leaf 348537230)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 340529591) (.leaf 332715012)) (.branch 100 (.leaf 325088390) (.leaf 317644777))) (.branch 103 (.branch 102 (.leaf 310379379) (.leaf 303287544)) (.branch 104 (.leaf 296364761) (.leaf 289606657))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 283008985) (.leaf 276567625)) (.branch 108 (.leaf 270278581) (.leaf 264137969))) (.branch 111 (.branch 110 (.leaf 258142020) (.leaf 252287075)) (.branch 112 (.leaf 246569577) (.leaf 240986073)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 235533207) (.leaf 230207717)) (.branch 116 (.leaf 225006434) (.leaf 219926276))) (.branch 119 (.branch 118 (.leaf 214964247) (.leaf 210117434)) (.branch 120 (.leaf 205383004) (.leaf 200758200)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 210).prefactor = (1274950120584337/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 210).cutoff/(generalMeanRows 210).c)).2 =
    (47171752694837/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 210).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 210).q*(generalMeanRows 210).c/2-2 = (441/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable108.value]
  have hcontinuation : (generalMeanRows 210).q*(generalMeanRows 210).cutoff/2-2 = (271/123:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable098.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 210).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 210).criticalRate j.val*(generalMeanRows 210).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 210).c*(generalMeanRows 210).criticalPoint j.val)).2-
      (generalMeanRows 210).J/2-(generalMeanRows 210).error (generalMeanGrid j.val)+
      (generalMeanRows 210).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 210).c)).2-
      (generalMeanRows 210).J/2-(generalMeanRows 210).error 4 := by
  have he : (generalMeanRows 210).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 210) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 210)
    (generalMeanRows_prefactorDomain 210) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0210

/-! Kernel-checked entropy margins for general spectral rectangle 211. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0211
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5104742510) (.branch 2 (.leaf 4929001518) (.leaf 4761406538))) (.branch 5 (.branch 4 (.leaf 4601474726) (.leaf 4448758102)) (.branch 6 (.leaf 4302840514) (.leaf 4163334904)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4029880877) (.leaf 3902142503)) (.branch 10 (.leaf 3779806343) (.leaf 3662579666))) (.branch 13 (.branch 12 (.leaf 3550188832) (.leaf 3442377828)) (.branch 14 (.leaf 3338906935) (.leaf 3239551516))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3144100908) (.branch 17 (.leaf 3052357410) (.leaf 2964135358))) (.branch 20 (.branch 19 (.leaf 2879260276) (.leaf 2797568094)) (.branch 21 (.leaf 2718904433) (.leaf 2643123942)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2570089696) (.leaf 2499672628)) (.branch 25 (.leaf 2431751011) (.leaf 2366209982))) (.branch 28 (.branch 27 (.leaf 2302941097) (.leaf 2241841913)) (.branch 29 (.leaf 2182815617) (.leaf 2125770663)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2070620446) (.branch 32 (.leaf 2017282997) (.leaf 1965680695))) (.branch 35 (.branch 34 (.leaf 1915740006) (.leaf 1867391233)) (.branch 36 (.leaf 1820568284) (.leaf 1775208464)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1731252265) (.leaf 1688643186)) (.branch 40 (.leaf 1647327554) (.leaf 1607254361))) (.branch 43 (.branch 42 (.leaf 1568375112) (.leaf 1530643680)) (.branch 44 (.leaf 1494016171) (.leaf 1458450801))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1423907774) (.branch 47 (.leaf 1390349175) (.leaf 1357738864))) (.branch 50 (.branch 49 (.leaf 1326042379) (.leaf 1295226846)) (.branch 51 (.leaf 1265260889) (.leaf 1236114554)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1207759229) (.leaf 1180167576)) (.branch 55 (.leaf 1153313462) (.leaf 1127171896))) (.branch 58 (.branch 57 (.leaf 1101718967) (.leaf 1076931794)) (.branch 59 (.leaf 1052788467) (.leaf 1029268002))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1006350289) (.branch 62 (.leaf 984016054) (.leaf 962246811))) (.branch 65 (.branch 64 (.leaf 941024826) (.leaf 920333082)) (.branch 66 (.leaf 900155238) (.leaf 880475601)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 861279093) (.leaf 842551220)) (.branch 70 (.leaf 824278046) (.leaf 806446167))) (.branch 73 (.branch 72 (.leaf 789042683) (.leaf 772055178)) (.branch 74 (.leaf 755471694) (.leaf 739280715))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 723471140) (.branch 77 (.leaf 708032269) (.leaf 692953786))) (.branch 80 (.branch 79 (.leaf 678225735) (.leaf 663838513)) (.branch 81 (.leaf 649782847) (.leaf 636049784)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 622630675) (.leaf 609517165)) (.branch 85 (.leaf 596701175) (.leaf 584174895))) (.branch 88 (.branch 87 (.leaf 571930772) (.leaf 559961497)) (.branch 89 (.leaf 548259997) (.leaf 536819425)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 525633152) (.branch 92 (.leaf 514694755) (.leaf 503998011))) (.branch 95 (.branch 94 (.leaf 493536890) (.leaf 483305544)) (.branch 96 (.leaf 473298306) (.leaf 463509674)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 453934314) (.leaf 444567049)) (.branch 100 (.leaf 435402852) (.leaf 426436844))) (.branch 103 (.branch 102 (.leaf 417664284) (.leaf 409080569)) (.branch 104 (.leaf 400681226) (.leaf 392461909))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 384418390) (.leaf 376546561)) (.branch 108 (.leaf 368842428) (.leaf 361302103))) (.branch 111 (.branch 110 (.leaf 353921807) (.leaf 346697859)) (.branch 112 (.leaf 339626679) (.leaf 332704783)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 325928776) (.leaf 319295354)) (.branch 116 (.leaf 312801298) (.leaf 306443474))) (.branch 119 (.branch 118 (.leaf 300218827) (.leaf 294124380)) (.branch 120 (.leaf 288157233) (.leaf 282314557)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 211).prefactor = (5050727406408479/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 211).cutoff/(generalMeanRows 211).c)).2 =
    (26290896930817/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 211).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 211).q*(generalMeanRows 211).c/2-2 = (397/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable105.value]
  have hcontinuation : (generalMeanRows 211).q*(generalMeanRows 211).cutoff/2-2 = (548/243:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable101.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 211).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 211).criticalRate j.val*(generalMeanRows 211).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 211).c*(generalMeanRows 211).criticalPoint j.val)).2-
      (generalMeanRows 211).J/2-(generalMeanRows 211).error (generalMeanGrid j.val)+
      (generalMeanRows 211).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 211).c)).2-
      (generalMeanRows 211).J/2-(generalMeanRows 211).error 4 := by
  have he : (generalMeanRows 211).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 211) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 211)
    (generalMeanRows_prefactorDomain 211) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0211

/-! Kernel-checked entropy margins for general spectral rectangle 212. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0212
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4748913705) (.branch 2 (.leaf 4571241856) (.leaf 4401947334))) (.branch 5 (.branch 4 (.leaf 4240539880) (.leaf 4086564221)) (.branch 6 (.leaf 3939597016) (.leaf 3799244140)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3665138237) (.leaf 3536936536)) (.branch 10 (.leaf 3414318870) (.leaf 3296985899))) (.branch 13 (.branch 12 (.leaf 3184657492) (.leaf 3077071270)) (.branch 14 (.leaf 2973981268) (.leaf 2875156732))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2780381005) (.branch 17 (.leaf 2689450525) (.leaf 2602173893))) (.branch 20 (.branch 19 (.leaf 2518371028) (.leaf 2437872388)) (.branch 21 (.leaf 2360518253) (.leaf 2286158063)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2214649813) (.leaf 2145859489)) (.branch 25 (.leaf 2079660549) (.leaf 2015933444))) (.branch 28 (.branch 27 (.leaf 1954565171) (.leaf 1895448860)) (.branch 29 (.leaf 1838483395) (.leaf 1783573054)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1730627179) (.branch 32 (.leaf 1679559871) (.leaf 1630289702))) (.branch 35 (.branch 34 (.leaf 1582739445) (.leaf 1536835831)) (.branch 36 (.leaf 1492509310) (.leaf 1449693839)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1408326679) (.leaf 1368348201)) (.branch 40 (.leaf 1329701713) (.leaf 1292333292))) (.branch 43 (.branch 42 (.leaf 1256191629) (.leaf 1221227883)) (.branch 44 (.leaf 1187395545) (.leaf 1154650308))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1122949950) (.branch 47 (.leaf 1092254217) (.leaf 1062524718))) (.branch 50 (.branch 49 (.leaf 1033724830) (.leaf 1005819595)) (.branch 51 (.leaf 978775641) (.leaf 952561093)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 927145498) (.leaf 902499750)) (.branch 55 (.leaf 878596020) (.leaf 855407692))) (.branch 58 (.branch 57 (.leaf 832909302) (.leaf 811076478)) (.branch 59 (.leaf 789885886) (.leaf 769315178))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 749342945) (.branch 62 (.leaf 729948668) (.leaf 711112677))) (.branch 65 (.branch 64 (.leaf 692816106) (.leaf 675040860)) (.branch 66 (.leaf 657769573) (.leaf 640985576)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 624672862) (.leaf 608816058)) (.branch 70 (.leaf 593400390) (.leaf 578411663))) (.branch 73 (.branch 72 (.leaf 563836225) (.leaf 549660952)) (.branch 74 (.leaf 535873214) (.leaf 522460862))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 509412200) (.branch 77 (.leaf 496715967) (.leaf 484361318))) (.branch 80 (.branch 79 (.leaf 472337804) (.leaf 460635358)) (.branch 81 (.leaf 449244276) (.leaf 438155200)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 427359106) (.leaf 416847291)) (.branch 85 (.leaf 406611353) (.leaf 396643186))) (.branch 88 (.branch 87 (.leaf 386934962) (.leaf 377479124)) (.branch 89 (.leaf 368268371) (.leaf 359295650)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 350554144) (.branch 92 (.leaf 342037265) (.leaf 333738643))) (.branch 95 (.branch 94 (.leaf 325652118) (.leaf 317771732)) (.branch 96 (.leaf 310091719) (.leaf 302606502)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 295310681) (.leaf 288199029)) (.branch 100 (.leaf 281266484) (.leaf 274508144))) (.branch 103 (.branch 102 (.leaf 267919261) (.leaf 261495234)) (.branch 104 (.leaf 255231604) (.leaf 249124049))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 243168380) (.leaf 237360536)) (.branch 108 (.leaf 231696575) (.leaf 226172678))) (.branch 111 (.branch 110 (.leaf 220785138) (.leaf 215530357)) (.branch 112 (.leaf 210404845) (.leaf 205405214)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 200528176) (.leaf 195770537)) (.branch 116 (.leaf 191129196) (.leaf 186601143))) (.branch 119 (.branch 118 (.leaf 182183452) (.leaf 177873282)) (.branch 120 (.leaf 173667871) (.leaf 169564537)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 212).prefactor = (5133598716496251/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 212).cutoff/(generalMeanRows 212).c)).2 =
    (362222216538093/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 212).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 212).q*(generalMeanRows 212).c/2-2 = (463/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable109.value]
  have hcontinuation : (generalMeanRows 212).q*(generalMeanRows 212).cutoff/2-2 = (271/123:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable098.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 212).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 212).criticalRate j.val*(generalMeanRows 212).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 212).c*(generalMeanRows 212).criticalPoint j.val)).2-
      (generalMeanRows 212).J/2-(generalMeanRows 212).error (generalMeanGrid j.val)+
      (generalMeanRows 212).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 212).c)).2-
      (generalMeanRows 212).J/2-(generalMeanRows 212).error 4 := by
  have he : (generalMeanRows 212).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 212) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 212)
    (generalMeanRows_prefactorDomain 212) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0212

/-! Kernel-checked entropy margins for general spectral rectangle 213. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0213
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4780386485) (.branch 2 (.leaf 4601537140) (.leaf 4431120642))) (.branch 5 (.branch 4 (.leaf 4268643482) (.leaf 4113647369)) (.branch 6 (.leaf 3965706160) (.leaf 3824423114)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3689428443) (.leaf 3560377102)) (.branch 10 (.leaf 3436946804) (.leaf 3318836224))) (.branch 13 (.branch 12 (.leaf 3205763377) (.leaf 3097464141)) (.branch 14 (.leaf 2993690925) (.leaf 2894211442))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2798807602) (.branch 17 (.leaf 2707274493) (.leaf 2619419446))) (.branch 20 (.branch 19 (.leaf 2535061190) (.leaf 2454029056)) (.branch 21 (.leaf 2376162267) (.leaf 2301309265)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2229327103) (.leaf 2160080881)) (.branch 25 (.leaf 2093443217) (.leaf 2029293769))) (.branch 28 (.branch 27 (.leaf 1967518786) (.leaf 1908010690)) (.branch 29 (.leaf 1850667694) (.leaf 1795393442)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1742096675) (.branch 32 (.leaf 1690690926) (.leaf 1641094225))) (.branch 35 (.branch 34 (.leaf 1593228836) (.leaf 1547021001)) (.branch 36 (.leaf 1502400712) (.leaf 1459301488)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1417660172) (.leaf 1377416742)) (.branch 40 (.leaf 1338514130) (.leaf 1300898055))) (.branch 43 (.branch 42 (.leaf 1264516868) (.leaf 1229321405)) (.branch 44 (.leaf 1195264847) (.leaf 1162302596))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1130392148) (.branch 47 (.leaf 1099492983) (.leaf 1069566456))) (.branch 50 (.branch 49 (.leaf 1040575700) (.leaf 1012485527)) (.branch 51 (.leaf 985262343) (.leaf 958874062)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 933290029) (.leaf 908480944)) (.branch 55 (.leaf 884418795) (.leaf 861076790))) (.branch 58 (.branch 57 (.leaf 838429295) (.leaf 816451777)) (.branch 59 (.leaf 795120747) (.leaf 774413710))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 754309114) (.branch 62 (.leaf 734786304) (.leaf 715825479))) (.branch 65 (.branch 64 (.leaf 697407651) (.leaf 679514602)) (.branch 66 (.leaf 662128852) (.leaf 645233621)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 628812797) (.leaf 612850903)) (.branch 70 (.leaf 597333071) (.leaf 582245007))) (.branch 73 (.branch 72 (.leaf 567572973) (.leaf 553303755)) (.branch 74 (.leaf 539424641) (.leaf 525923401))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 512788261) (.branch 77 (.leaf 500007885) (.leaf 487571357))) (.branch 80 (.branch 79 (.leaf 475468159) (.leaf 463688157)) (.branch 81 (.leaf 452221581) (.leaf 441059014)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 430191371) (.leaf 419609889)) (.branch 85 (.leaf 409306114) (.leaf 399271884))) (.branch 88 (.branch 87 (.leaf 389499321) (.leaf 379980816)) (.branch 89 (.leaf 370709020) (.leaf 361676833)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 352877394) (.branch 92 (.leaf 344304070) (.leaf 335950450))) (.branch 95 (.branch 94 (.leaf 327810333) (.leaf 319877720)) (.branch 96 (.leaf 312146810) (.leaf 304611985)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 297267812) (.leaf 290109028)) (.branch 100 (.leaf 283130539) (.leaf 276327410))) (.branch 103 (.branch 102 (.leaf 269694860) (.leaf 263228258)) (.branch 104 (.leaf 256923116) (.leaf 250775085))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 244779946) (.leaf 238933610)) (.branch 108 (.leaf 233232113) (.leaf 227671607))) (.branch 111 (.branch 110 (.leaf 222248361) (.leaf 216958755)) (.branch 112 (.leaf 211799274) (.leaf 206766509)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 201857149) (.leaf 197067979)) (.branch 116 (.leaf 192395879) (.leaf 187837817))) (.branch 119 (.branch 118 (.leaf 183390848) (.leaf 179052113)) (.branch 120 (.leaf 174818831) (.leaf 170688303)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 213).prefactor = (5167620943855717/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 213).cutoff/(generalMeanRows 213).c)).2 =
    (362222216538093/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 213).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 213).q*(generalMeanRows 213).c/2-2 = (463/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable109.value]
  have hcontinuation : (generalMeanRows 213).q*(generalMeanRows 213).cutoff/2-2 = (271/123:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable098.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 213).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 213).criticalRate j.val*(generalMeanRows 213).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 213).c*(generalMeanRows 213).criticalPoint j.val)).2-
      (generalMeanRows 213).J/2-(generalMeanRows 213).error (generalMeanGrid j.val)+
      (generalMeanRows 213).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 213).c)).2-
      (generalMeanRows 213).J/2-(generalMeanRows 213).error 4 := by
  have he : (generalMeanRows 213).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 213) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 213)
    (generalMeanRows_prefactorDomain 213) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0213

/-! Kernel-checked entropy margins for general spectral rectangle 214. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0214
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7209300889) (.branch 2 (.leaf 6958985619) (.leaf 6719180821))) (.branch 5 (.branch 4 (.leaf 6489332882) (.leaf 6268926235)) (.branch 6 (.leaf 6057479911) (.leaf 5854544501)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5659699444) (.leaf 5472550624)) (.branch 10 (.leaf 5292728211) (.leaf 5119884730))) (.branch 13 (.branch 12 (.leaf 4953693326) (.leaf 4793846199)) (.branch 14 (.leaf 4640053184) (.leaf 4492040475))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4349549455) (.branch 17 (.leaf 4212335639) (.leaf 4080167706))) (.branch 20 (.branch 19 (.leaf 3952826614) (.leaf 3830104792)) (.branch 21 (.leaf 3711805394) (.leaf 3597741621)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3487736085) (.leaf 3381620235)) (.branch 25 (.leaf 3279233821) (.leaf 3180424392))) (.branch 28 (.branch 27 (.leaf 3085046843) (.leaf 2992962987)) (.branch 29 (.leaf 2904041159) (.leaf 2818155847)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2735187349) (.branch 32 (.leaf 2655021456) (.leaf 2577549150))) (.branch 35 (.branch 34 (.leaf 2502666328) (.leaf 2430273537)) (.branch 36 (.leaf 2360275737) (.leaf 2292582064)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2227105621) (.leaf 2163763273)) (.branch 40 (.leaf 2102475461) (.leaf 2043166020))) (.branch 43 (.branch 42 (.leaf 1985762014) (.leaf 1930193578)) (.branch 44 (.leaf 1876393767) (.leaf 1824298418))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1773846016) (.branch 47 (.leaf 1724977570) (.leaf 1677636494))) (.branch 50 (.branch 49 (.leaf 1631768496) (.leaf 1587321468)) (.branch 51 (.leaf 1544245395) (.leaf 1502492248)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1462015906) (.leaf 1422772062)) (.branch 55 (.leaf 1384718145) (.leaf 1347813244))) (.branch 58 (.branch 57 (.leaf 1312018037) (.leaf 1277294715)) (.branch 59 (.leaf 1243606922) (.leaf 1210919692))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1179199387) (.branch 62 (.leaf 1148413642) (.leaf 1118531309))) (.branch 65 (.branch 64 (.leaf 1089522411) (.leaf 1061358086)) (.branch 66 (.leaf 1034010544) (.leaf 1007453023)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 981659747) (.leaf 956605883)) (.branch 70 (.leaf 932267505) (.leaf 908621553))) (.branch 73 (.branch 72 (.leaf 885645806) (.leaf 863318839)) (.branch 74 (.leaf 841619997) (.leaf 820529364))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 800027730) (.branch 77 (.leaf 780096567) (.leaf 760718000))) (.branch 80 (.branch 79 (.leaf 741874782) (.leaf 723550271)) (.branch 81 (.leaf 705728402) (.leaf 688393670)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 671531106) (.leaf 655126258)) (.branch 85 (.leaf 639165165) (.leaf 623634350))) (.branch 88 (.branch 87 (.leaf 608520789) (.leaf 593811903)) (.branch 89 (.leaf 579495537) (.leaf 565559945)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 551993776) (.branch 92 (.leaf 538786057) (.leaf 525926181))) (.branch 95 (.branch 94 (.leaf 513403892) (.leaf 501209273)) (.branch 96 (.leaf 489332735) (.leaf 477765001)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 466497098) (.leaf 455520346)) (.branch 100 (.leaf 444826346) (.leaf 434406969))) (.branch 103 (.branch 102 (.leaf 424254351) (.leaf 414360877)) (.branch 104 (.leaf 404719176) (.leaf 395322115))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 386162782) (.leaf 377234488)) (.branch 108 (.leaf 368530752) (.leaf 360045299))) (.branch 111 (.branch 110 (.leaf 351772049) (.leaf 343705110)) (.branch 112 (.leaf 335838776) (.leaf 328167515)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 320685967) (.leaf 313388937)) (.branch 116 (.leaf 306271388) (.leaf 299328438))) (.branch 119 (.branch 118 (.leaf 292555351) (.leaf 285947539)) (.branch 120 (.leaf 279500547) (.leaf 273210059)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 214).prefactor = (70634056192341/12500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 214).cutoff/(generalMeanRows 214).c)).2 =
    (4524134975101/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 214).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 214).q*(generalMeanRows 214).c/2-2 = (161/200:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable110.value]
  have hcontinuation : (generalMeanRows 214).q*(generalMeanRows 214).cutoff/2-2 = (223/147:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable111.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 214).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 214).criticalRate j.val*(generalMeanRows 214).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 214).c*(generalMeanRows 214).criticalPoint j.val)).2-
      (generalMeanRows 214).J/2-(generalMeanRows 214).error (generalMeanGrid j.val)+
      (generalMeanRows 214).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 214).c)).2-
      (generalMeanRows 214).J/2-(generalMeanRows 214).error 4 := by
  have he : (generalMeanRows 214).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 214) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 214)
    (generalMeanRows_prefactorDomain 214) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0214

/-! Kernel-checked entropy margins for general spectral rectangle 215. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0215
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6790155431) (.branch 2 (.leaf 6593622203) (.leaf 6405387432))) (.branch 5 (.branch 4 (.leaf 6224994974) (.leaf 6052020304)) (.branch 6 (.leaf 5886067720) (.leaf 5726767865)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5573775509) (.leaf 5426767570)) (.branch 10 (.leaf 5285441340) (.leaf 5149512889))) (.branch 13 (.branch 12 (.leaf 5018715618) (.leaf 4892798963)) (.branch 14 (.leaf 4771527210) (.leaf 4654678420))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4542043454) (.branch 17 (.leaf 4433425080) (.leaf 4328637156))) (.branch 20 (.branch 19 (.leaf 4227503883) (.leaf 4129859118)) (.branch 21 (.leaf 4035545746) (.leaf 3944415095)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3856326401) (.leaf 3771146316)) (.branch 25 (.leaf 3688748446) (.leaf 3609012929))) (.branch 28 (.branch 27 (.leaf 3531826042) (.leaf 3457079835)) (.branch 29 (.leaf 3384671789) (.leaf 3314504505)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3246485405) (.branch 32 (.leaf 3180526458) (.leaf 3116543925))) (.branch 35 (.branch 34 (.leaf 3054458121) (.leaf 2994193184)) (.branch 36 (.leaf 2935676872) (.leaf 2878840366)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2823618079) (.leaf 2769947492)) (.branch 40 (.leaf 2717768984) (.leaf 2667025685))) (.branch 43 (.branch 42 (.leaf 2617663328) (.leaf 2569630119)) (.branch 44 (.leaf 2522876604) (.leaf 2477355555))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2433021852) (.branch 47 (.leaf 2389832380) (.leaf 2347745929))) (.branch 50 (.branch 49 (.leaf 2306723096) (.leaf 2266726199)) (.branch 51 (.leaf 2227719188) (.leaf 2189667572)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2152538335) (.leaf 2116299871)) (.branch 55 (.leaf 2080921914) (.leaf 2046375473))) (.branch 58 (.branch 57 (.leaf 2012632773) (.leaf 1979667195)) (.branch 59 (.leaf 1947453225) (.leaf 1915966399))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1885183256) (.branch 62 (.leaf 1855081290) (.leaf 1825638906))) (.branch 65 (.branch 64 (.leaf 1796835382) (.leaf 1768650821)) (.branch 66 (.leaf 1741066121) (.leaf 1714062936)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1687623641) (.leaf 1661731300)) (.branch 70 (.leaf 1636369636) (.leaf 1611523002))) (.branch 73 (.branch 72 (.leaf 1587176352) (.leaf 1563315212)) (.branch 74 (.leaf 1539925660) (.leaf 1516994300))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1494508235) (.branch 77 (.leaf 1472455051) (.leaf 1450822792))) (.branch 80 (.branch 79 (.leaf 1429599944) (.leaf 1408775411)) (.branch 81 (.leaf 1388338503) (.leaf 1368278913)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1348586704) (.leaf 1329252294)) (.branch 85 (.leaf 1310266439) (.leaf 1291620220))) (.branch 88 (.branch 87 (.leaf 1273305027) (.leaf 1255312552)) (.branch 89 (.leaf 1237634770) (.leaf 1220263930)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1203192546) (.branch 92 (.leaf 1186413382) (.leaf 1169919445))) (.branch 95 (.branch 94 (.leaf 1153703972) (.leaf 1137760426)) (.branch 96 (.leaf 1122082480) (.leaf 1106664016)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1091499109) (.leaf 1076582027)) (.branch 100 (.leaf 1061907216) (.leaf 1047469299))) (.branch 103 (.branch 102 (.leaf 1033263067) (.leaf 1019283471)) (.branch 104 (.leaf 1005525617) (.leaf 991984761))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 978656302) (.leaf 965535775)) (.branch 108 (.leaf 952618851) (.leaf 939901325))) (.branch 111 (.branch 110 (.leaf 927379118) (.leaf 915048267)) (.branch 112 (.leaf 902904924) (.leaf 890945349)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 879165910) (.leaf 867563075)) (.branch 116 (.leaf 856133409) (.leaf 844873574))) (.branch 119 (.branch 118 (.leaf 833780322) (.leaf 822850492)) (.branch 120 (.leaf 812081009) (.leaf 801468877)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 215).prefactor = (18331717773571/3906250000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 215).cutoff/(generalMeanRows 215).c)).2 =
    (405172597702031/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 215).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 215).q*(generalMeanRows 215).c/2-2 = (39/80:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable085.value]
  have hcontinuation : (generalMeanRows 215).q*(generalMeanRows 215).cutoff/2-2 = (109/63:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable112.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 215).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 215).criticalRate j.val*(generalMeanRows 215).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 215).c*(generalMeanRows 215).criticalPoint j.val)).2-
      (generalMeanRows 215).J/2-(generalMeanRows 215).error (generalMeanGrid j.val)+
      (generalMeanRows 215).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 215).c)).2-
      (generalMeanRows 215).J/2-(generalMeanRows 215).error 4 := by
  have he : (generalMeanRows 215).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 215) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 215)
    (generalMeanRows_prefactorDomain 215) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0215

/-! Kernel-checked entropy margins for general spectral rectangle 216. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0216
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6950525491) (.branch 2 (.leaf 6745702077) (.leaf 6549533934))) (.branch 5 (.branch 4 (.leaf 6361546073) (.leaf 6181296419)) (.branch 6 (.leaf 6008372901) (.leaf 5842390868)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5682990783) (.leaf 5529836162)) (.branch 10 (.leaf 5382611729) (.leaf 5241021746))) (.branch 13 (.branch 12 (.leaf 5104788523) (.leaf 4973651050)) (.branch 14 (.leaf 4847363777) (.leaf 4725695491))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4608428297) (.branch 17 (.leaf 4495356695) (.leaf 4386286726))) (.branch 20 (.branch 19 (.leaf 4281035195) (.leaf 4179428957)) (.branch 21 (.leaf 4081304260) (.leaf 3986506142)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3894887870) (.leaf 3806310428)) (.branch 25 (.leaf 3720642038) (.leaf 3637757723))) (.branch 28 (.branch 27 (.leaf 3557538889) (.leaf 3479872956)) (.branch 29 (.leaf 3404652995) (.leaf 3331777404)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3261149602) (.branch 32 (.leaf 3192677739) (.leaf 3126274434))) (.branch 35 (.branch 34 (.leaf 3061856523) (.leaf 2999344825)) (.branch 36 (.leaf 2938663928) (.leaf 2879741978)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2822510492) (.leaf 2766904178)) (.branch 40 (.leaf 2712860763) (.leaf 2660320837))) (.branch 43 (.branch 42 (.leaf 2609227702) (.leaf 2559527235)) (.branch 44 (.leaf 2511167749) (.leaf 2464099875))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2418276444) (.branch 47 (.leaf 2373652371) (.leaf 2330184555))) (.branch 50 (.branch 49 (.leaf 2287831782) (.leaf 2246554627)) (.branch 51 (.leaf 2206315369) (.leaf 2167077908)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2128807684) (.leaf 2091471606)) (.branch 55 (.leaf 2055037979) (.leaf 2019476438))) (.branch 58 (.branch 57 (.leaf 1984757885) (.leaf 1950854429)) (.branch 59 (.leaf 1917739329) (.leaf 1885386942))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1853772669) (.branch 62 (.leaf 1822872908) (.leaf 1792665009))) (.branch 65 (.branch 64 (.leaf 1763127229) (.leaf 1734238691)) (.branch 66 (.leaf 1705979345) (.leaf 1678329930)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1651271938) (.leaf 1624787583)) (.branch 70 (.leaf 1598859764) (.leaf 1573472040))) (.branch 73 (.branch 72 (.leaf 1548608595) (.leaf 1524254217)) (.branch 74 (.leaf 1500394266) (.leaf 1477014651))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1454101807) (.branch 77 (.leaf 1431642671) (.leaf 1409624659))) (.branch 80 (.branch 79 (.leaf 1388035651) (.leaf 1366863964)) (.branch 81 (.leaf 1346098338) (.leaf 1325727917)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1305742230) (.leaf 1286131179)) (.branch 85 (.leaf 1266885020) (.leaf 1247994348))) (.branch 88 (.branch 87 (.leaf 1229450085) (.leaf 1211243466)) (.branch 89 (.leaf 1193366025) (.leaf 1175809582)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1158566237) (.branch 92 (.leaf 1141628349) (.leaf 1124988535))) (.branch 95 (.branch 94 (.leaf 1108639654) (.leaf 1092574798)) (.branch 96 (.leaf 1076787286) (.leaf 1061270648)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1046018626) (.leaf 1031025159)) (.branch 100 (.leaf 1016284375) (.leaf 1001790590))) (.branch 103 (.branch 102 (.leaf 987538291) (.leaf 973522140)) (.branch 104 (.leaf 959736959) (.leaf 946177727))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 932839576) (.leaf 919717781)) (.branch 108 (.leaf 906807759) (.leaf 894105059))) (.branch 111 (.branch 110 (.leaf 881605361) (.leaf 869304470)) (.branch 112 (.leaf 857198310) (.leaf 845282921)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 833554456) (.leaf 822009173)) (.branch 116 (.leaf 810643436) (.leaf 799453706))) (.branch 119 (.branch 118 (.leaf 788436544) (.leaf 777588599)) (.branch 120 (.leaf 766906615) (.leaf 756387418)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 216).prefactor = (4891218574344911/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 216).cutoff/(generalMeanRows 216).c)).2 =
    (197586257183723/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 216).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 216).q*(generalMeanRows 216).c/2-2 = (41/80:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable058.value]
  have hcontinuation : (generalMeanRows 216).q*(generalMeanRows 216).cutoff/2-2 = (109/63:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable112.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 216).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 216).criticalRate j.val*(generalMeanRows 216).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 216).c*(generalMeanRows 216).criticalPoint j.val)).2-
      (generalMeanRows 216).J/2-(generalMeanRows 216).error (generalMeanGrid j.val)+
      (generalMeanRows 216).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 216).c)).2-
      (generalMeanRows 216).J/2-(generalMeanRows 216).error 4 := by
  have he : (generalMeanRows 216).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 216) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 216)
    (generalMeanRows_prefactorDomain 216) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0216

/-! Kernel-checked entropy margins for general spectral rectangle 217. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0217
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6868341326) (.branch 2 (.leaf 6655349558) (.leaf 6451398764))) (.branch 5 (.branch 4 (.leaf 6255994891) (.leaf 6068678081)) (.branch 6 (.leaf 5889019635) (.leaf 5716619338)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5551103057) (.leaf 5392120603)) (.branch 10 (.leaf 5239343811) (.leaf 5092464807))) (.branch 13 (.branch 12 (.leaf 4951194458) (.leaf 4815260957)) (.branch 14 (.leaf 4684408544) (.leaf 4558396353))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4436997348) (.branch 17 (.leaf 4319997358) (.leaf 4207194203))) (.branch 20 (.branch 19 (.leaf 4098396877) (.leaf 3993424811)) (.branch 21 (.leaf 3892107192) (.leaf 3794282332)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3699797094) (.leaf 3608506352)) (.branch 25 (.leaf 3520272499) (.leaf 3434964991))) (.branch 28 (.branch 27 (.leaf 3352459919) (.leaf 3272639614)) (.branch 29 (.leaf 3195392286) (.leaf 3120611676)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3048196741) (.branch 32 (.leaf 2978051359) (.leaf 2910084049))) (.branch 35 (.branch 34 (.leaf 2844207717) (.leaf 2780339408)) (.branch 36 (.leaf 2718400085) (.leaf 2658314414)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2600010565) (.leaf 2543420029)) (.branch 40 (.leaf 2488477437) (.leaf 2435120401))) (.branch 43 (.branch 42 (.leaf 2383289355) (.leaf 2332927412)) (.branch 44 (.leaf 2283980226) (.leaf 2236395863))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2190124678) (.branch 47 (.leaf 2145119203) (.leaf 2101334037))) (.branch 50 (.branch 49 (.leaf 2058725741) (.leaf 2017252749)) (.branch 51 (.leaf 1976875268) (.leaf 1937555197)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1899256045) (.leaf 1861942853)) (.branch 55 (.leaf 1825582120) (.leaf 1790141734))) (.branch 58 (.branch 57 (.leaf 1755590909) (.leaf 1721900120)) (.branch 59 (.leaf 1689041045) (.leaf 1656986511))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1625710437) (.branch 62 (.leaf 1595187787) (.leaf 1565394522))) (.branch 65 (.branch 64 (.leaf 1536307552) (.leaf 1507904699)) (.branch 66 (.leaf 1480164648) (.leaf 1453066913)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1426591802) (.leaf 1400720376)) (.branch 70 (.leaf 1375434421) (.leaf 1350716412))) (.branch 73 (.branch 72 (.leaf 1326549487) (.leaf 1302917413)) (.branch 74 (.leaf 1279804565) (.leaf 1257195893))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1235076903) (.branch 77 (.leaf 1213433631) (.leaf 1192252617))) (.branch 80 (.branch 79 (.leaf 1171520891) (.leaf 1151225946)) (.branch 81 (.leaf 1131355722) (.leaf 1111898583)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1092843307) (.leaf 1074179061)) (.branch 85 (.leaf 1055895388) (.leaf 1037982195))) (.branch 88 (.branch 87 (.leaf 1020429731) (.leaf 1003228579)) (.branch 89 (.leaf 986369641) (.leaf 969844122)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 953643522) (.branch 92 (.leaf 937759624) (.leaf 922184479))) (.branch 95 (.branch 94 (.leaf 906910398) (.leaf 891929942)) (.branch 96 (.leaf 877235913) (.leaf 862821340)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 848679477) (.leaf 834803789)) (.branch 100 (.leaf 821187945) (.leaf 807825811))) (.branch 103 (.branch 102 (.leaf 794711445) (.leaf 781839083)) (.branch 104 (.leaf 769203139) (.leaf 756798195))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 744618996) (.leaf 732660442)) (.branch 108 (.leaf 720917584) (.leaf 709385620))) (.branch 111 (.branch 110 (.leaf 698059885) (.leaf 686935850)) (.branch 112 (.leaf 676009115) (.leaf 665275408)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 654730574) (.leaf 644370576)) (.branch 116 (.leaf 634191490) (.leaf 624189499))) (.branch 119 (.branch 118 (.leaf 614360891) (.leaf 604702056)) (.branch 120 (.leaf 595209479) (.leaf 585879743)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 217).prefactor = (5097896494360983/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 217).cutoff/(generalMeanRows 217).c)).2 =
    (5714978580643/15625000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 217).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 217).q*(generalMeanRows 217).c/2-2 = (47/80:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable034.value]
  have hcontinuation : (generalMeanRows 217).q*(generalMeanRows 217).cutoff/2-2 = (109/63:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable112.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 217).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 217).criticalRate j.val*(generalMeanRows 217).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 217).c*(generalMeanRows 217).criticalPoint j.val)).2-
      (generalMeanRows 217).J/2-(generalMeanRows 217).error (generalMeanGrid j.val)+
      (generalMeanRows 217).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 217).c)).2-
      (generalMeanRows 217).J/2-(generalMeanRows 217).error 4 := by
  have he : (generalMeanRows 217).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 217) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 217)
    (generalMeanRows_prefactorDomain 217) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0217

/-! Kernel-checked entropy margins for general spectral rectangle 218. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0218
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6429632449) (.branch 2 (.leaf 6236478017) (.leaf 6051621124))) (.branch 5 (.branch 4 (.leaf 5874599071) (.leaf 5704981408)) (.branch 6 (.leaf 5542367105) (.leaf 5386382029)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5236676694) (.leaf 5092924250)) (.branch 10 (.leaf 4954818667) (.leaf 4822073111))) (.branch 13 (.branch 12 (.leaf 4694418472) (.leaf 4571602024)) (.branch 14 (.leaf 4453386226) (.leaf 4339547614))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4229875802) (.branch 17 (.leaf 4124172566) (.leaf 4022251005))) (.branch 20 (.branch 19 (.leaf 3923934776) (.leaf 3829057385)) (.branch 21 (.leaf 3737461539) (.leaf 3648998553)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3563527791) (.leaf 3480916163)) (.branch 25 (.leaf 3401037651) (.leaf 3323772872))) (.branch 28 (.branch 27 (.leaf 3249008675) (.leaf 3176637764)) (.branch 29 (.leaf 3106558347) (.leaf 3038673815)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2972892434) (.branch 32 (.leaf 2909127067) (.leaf 2847294908))) (.branch 35 (.branch 34 (.leaf 2787317236) (.leaf 2729119185)) (.branch 36 (.leaf 2672629529) (.leaf 2617780482)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2564507505) (.leaf 2512749132)) (.branch 40 (.leaf 2462446803) (.leaf 2413544709))) (.branch 43 (.branch 42 (.leaf 2365989643) (.leaf 2319730865)) (.branch 44 (.leaf 2274719968) (.leaf 2230910762))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2188259155) (.branch 47 (.leaf 2146723045) (.leaf 2106262218))) (.branch 50 (.branch 49 (.leaf 2066838256) (.leaf 2028414439)) (.branch 51 (.leaf 1990955665) (.leaf 1954428366)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1918800435) (.leaf 1884041148)) (.branch 55 (.leaf 1850121104) (.leaf 1817012152))) (.branch 58 (.branch 57 (.leaf 1784687334) (.leaf 1753120829)) (.branch 59 (.leaf 1722287895) (.leaf 1692164817))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1662728862) (.branch 62 (.leaf 1633958228) (.leaf 1605832002))) (.branch 65 (.branch 64 (.leaf 1578330118) (.leaf 1551433317)) (.branch 66 (.leaf 1525123109) (.leaf 1499381740)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1474192154) (.leaf 1449537964)) (.branch 70 (.leaf 1425403420) (.leaf 1401773380))) (.branch 73 (.branch 72 (.leaf 1378633284) (.leaf 1355969126)) (.branch 74 (.leaf 1333767430) (.leaf 1312015225))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1290700024) (.branch 77 (.leaf 1269809804) (.leaf 1249332983))) (.branch 80 (.branch 79 (.leaf 1229258399) (.leaf 1209575297)) (.branch 81 (.leaf 1190273308) (.leaf 1171342432)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1152773024) (.leaf 1134555776)) (.branch 85 (.leaf 1116681707) (.leaf 1099142144))) (.branch 88 (.branch 87 (.leaf 1081928712) (.leaf 1065033323)) (.branch 89 (.leaf 1048448160) (.leaf 1032165669)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1016178546) (.branch 92 (.leaf 1000479729) (.leaf 985062384))) (.branch 95 (.branch 94 (.leaf 969919902) (.leaf 955045885)) (.branch 96 (.leaf 940434137) (.leaf 926078661)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 911973646) (.leaf 898113461)) (.branch 100 (.leaf 884492651) (.leaf 871105924))) (.branch 103 (.branch 102 (.leaf 857948151) (.leaf 845014356)) (.branch 104 (.leaf 832299710) (.leaf 819799528))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 807509261) (.leaf 795424492)) (.branch 108 (.leaf 783540931) (.leaf 771854410))) (.branch 111 (.branch 110 (.leaf 760360878) (.leaf 749056397)) (.branch 112 (.leaf 737937140) (.leaf 726999383)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 716239504) (.leaf 705653979)) (.branch 116 (.leaf 695239378) (.leaf 684992363))) (.branch 119 (.branch 118 (.leaf 674909680) (.leaf 664988165)) (.branch 120 (.leaf 655224731) (.leaf 645616371)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 218).prefactor = (1199401183114559/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 218).cutoff/(generalMeanRows 218).c)).2 =
    (406178128204049/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 218).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 218).q*(generalMeanRows 218).c/2-2 = (139/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable113.value]
  have hcontinuation : (generalMeanRows 218).q*(generalMeanRows 218).cutoff/2-2 = (90/49:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable114.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 218).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 218).criticalRate j.val*(generalMeanRows 218).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 218).c*(generalMeanRows 218).criticalPoint j.val)).2-
      (generalMeanRows 218).J/2-(generalMeanRows 218).error (generalMeanGrid j.val)+
      (generalMeanRows 218).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 218).c)).2-
      (generalMeanRows 218).J/2-(generalMeanRows 218).error 4 := by
  have he : (generalMeanRows 218).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 218) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 218)
    (generalMeanRows_prefactorDomain 218) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0218

/-! Kernel-checked entropy margins for general spectral rectangle 219. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0219
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6214151988) (.branch 2 (.leaf 6014764294) (.leaf 5824013039))) (.branch 5 (.branch 4 (.leaf 5641419233) (.leaf 5466537186)) (.branch 6 (.leaf 5298951595) (.leaf 5138274930)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4984145117) (.leaf 4836223455)) (.branch 10 (.leaf 4694192747) (.leaf 4557755618))) (.branch 13 (.branch 12 (.leaf 4426632991) (.leaf 4300562716)) (.branch 14 (.leaf 4179298320) (.leaf 4062607870))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3950272938) (.branch 17 (.leaf 3842087659) (.leaf 3737857863))) (.branch 20 (.branch 19 (.leaf 3637400284) (.leaf 3540541832)) (.branch 21 (.leaf 3447118925) (.leaf 3356976869)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3269969293) (.leaf 3185957622)) (.branch 25 (.leaf 3104810589) (.leaf 3026403790))) (.branch 28 (.branch 27 (.leaf 2950619260) (.leaf 2877345089)) (.branch 29 (.leaf 2806475064) (.leaf 2737908327)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2671549068) (.branch 32 (.leaf 2607306234) (.leaf 2545093252))) (.branch 35 (.branch 34 (.leaf 2484827782) (.leaf 2426431474)) (.branch 36 (.leaf 2369829751) (.leaf 2314951595)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2261729359) (.leaf 2210098579)) (.branch 40 (.leaf 2159997807) (.leaf 2111368446))) (.branch 43 (.branch 42 (.leaf 2064154600) (.leaf 2018302935)) (.branch 44 (.leaf 1973762541) (.leaf 1930484807))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1888423307) (.branch 47 (.leaf 1847533681) (.leaf 1807773535))) (.branch 50 (.branch 49 (.leaf 1769102342) (.leaf 1731481343)) (.branch 51 (.leaf 1694873466) (.leaf 1659243235)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1624556699) (.leaf 1590781349)) (.branch 55 (.leaf 1557886054) (.leaf 1525840992))) (.branch 58 (.branch 57 (.leaf 1494617587) (.leaf 1464188449)) (.branch 59 (.leaf 1434527318) (.leaf 1405609009))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1377409363) (.branch 62 (.leaf 1349905198) (.leaf 1323074265))) (.branch 65 (.branch 64 (.leaf 1296895202) (.leaf 1271347495)) (.branch 66 (.leaf 1246411437) (.leaf 1222068094)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1198299268) (.leaf 1175087463)) (.branch 70 (.leaf 1152415856) (.leaf 1130268264))) (.branch 73 (.branch 72 (.leaf 1108629116) (.leaf 1087483429)) (.branch 74 (.leaf 1066816777) (.leaf 1046615270))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1026865530) (.branch 77 (.leaf 1007554668) (.leaf 988670263))) (.branch 80 (.branch 79 (.leaf 970200344) (.leaf 952133365)) (.branch 81 (.leaf 934458194) (.leaf 917164091)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 900240692) (.leaf 883677995)) (.branch 85 (.leaf 867466343) (.leaf 851596410))) (.branch 88 (.branch 87 (.leaf 836059189) (.leaf 820845976)) (.branch 89 (.leaf 805948360) (.leaf 791358210)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 777067665) (.branch 92 (.leaf 763069120) (.leaf 749355219))) (.branch 95 (.branch 94 (.leaf 735918844) (.leaf 722753105)) (.branch 96 (.leaf 709851333) (.leaf 697207068)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 684814053) (.leaf 672666226)) (.branch 100 (.leaf 660757714) (.leaf 649082822))) (.branch 103 (.branch 102 (.leaf 637636028) (.leaf 626411980)) (.branch 104 (.leaf 615405483) (.leaf 604611499))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 594025136) (.leaf 583641648)) (.branch 108 (.leaf 573456425) (.leaf 563464993))) (.branch 111 (.branch 110 (.leaf 553663002) (.leaf 544046229)) (.branch 112 (.leaf 534610568) (.leaf 525352029)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 516266732) (.leaf 507350905)) (.branch 116 (.leaf 498600879) (.leaf 490013084))) (.branch 119 (.branch 118 (.leaf 481584046) (.leaf 473310385)) (.branch 120 (.leaf 465188810) (.leaf 457216118)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 219).prefactor = (2487803827454453/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 219).cutoff/(generalMeanRows 219).c)).2 =
    (369307592395721/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 219).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 219).q*(generalMeanRows 219).c/2-2 = (163/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable052.value]
  have hcontinuation : (generalMeanRows 219).q*(generalMeanRows 219).cutoff/2-2 = (90/49:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable114.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 219).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 219).criticalRate j.val*(generalMeanRows 219).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 219).c*(generalMeanRows 219).criticalPoint j.val)).2-
      (generalMeanRows 219).J/2-(generalMeanRows 219).error (generalMeanGrid j.val)+
      (generalMeanRows 219).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 219).c)).2-
      (generalMeanRows 219).J/2-(generalMeanRows 219).error 4 := by
  have he : (generalMeanRows 219).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 219) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 219)
    (generalMeanRows_prefactorDomain 219) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0219

/-! Kernel-checked entropy margins for general spectral rectangle 220. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0220
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5873072747) (.branch 2 (.leaf 5693807957) (.leaf 5522370182))) (.branch 5 (.branch 4 (.leaf 5358314830) (.leaf 5201228585)) (.branch 6 (.leaf 5050726672) (.leaf 4906450419)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4768065081) (.leaf 4635257885)) (.branch 10 (.leaf 4507736274) (.leaf 4385226324))) (.branch 13 (.branch 12 (.leaf 4267471308) (.leaf 4154230401)) (.branch 14 (.leaf 4045277504) (.leaf 3940400164))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3839398604) (.branch 17 (.leaf 3742084821) (.leaf 3648281774))) (.branch 20 (.branch 19 (.leaf 3557822629) (.leaf 3470550070)) (.branch 21 (.leaf 3386315669) (.leaf 3304979294)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3226408577) (.leaf 3150478412)) (.branch 25 (.leaf 3077070496) (.leaf 3006072899))) (.branch 28 (.branch 27 (.leaf 2937379674) (.leaf 2870890482)) (.branch 29 (.leaf 2806510260) (.leaf 2744148896)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2683720935) (.branch 32 (.leaf 2625145308) (.leaf 2568345069))) (.branch 35 (.branch 34 (.leaf 2513247161) (.leaf 2459782187)) (.branch 36 (.leaf 2407884205) (.leaf 2357490528)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2308541547) (.leaf 2260980551)) (.branch 40 (.leaf 2214753572) (.leaf 2169809233))) (.branch 43 (.branch 42 (.leaf 2126098604) (.leaf 2083575073)) (.branch 44 (.leaf 2042194217) (.leaf 2001913686))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1962693094) (.branch 47 (.leaf 1924493913) (.leaf 1887279376))) (.branch 50 (.branch 49 (.leaf 1851014384) (.leaf 1815665421)) (.branch 51 (.leaf 1781200472) (.leaf 1747588942)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1714801590) (.leaf 1682810453)) (.branch 55 (.leaf 1651588787) (.leaf 1621111002))) (.branch 58 (.branch 57 (.leaf 1591352608) (.leaf 1562290155)) (.branch 59 (.leaf 1533901187) (.leaf 1506164188))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1479058541) (.branch 62 (.leaf 1452564479) (.leaf 1426663050))) (.branch 65 (.branch 64 (.leaf 1401336071) (.leaf 1376566094)) (.branch 66 (.leaf 1352336374) (.leaf 1328630831)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1305434018) (.leaf 1282731098)) (.branch 70 (.leaf 1260507808) (.leaf 1238750435))) (.branch 73 (.branch 72 (.leaf 1217445794) (.leaf 1196581196)) (.branch 74 (.leaf 1176144434) (.leaf 1156123754))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1136507839) (.branch 77 (.leaf 1117285786) (.leaf 1098447091))) (.branch 80 (.branch 79 (.leaf 1079981627) (.leaf 1061879632)) (.branch 81 (.leaf 1044131688) (.leaf 1026728710)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1009661931) (.leaf 992922883)) (.branch 85 (.leaf 976503392) (.leaf 960395560))) (.branch 88 (.branch 87 (.leaf 944591755) (.leaf 929084600)) (.branch 89 (.leaf 913866961) (.leaf 898931937)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 884272854) (.branch 92 (.leaf 869883249) (.leaf 855756867))) (.branch 95 (.branch 94 (.leaf 841887650) (.leaf 828269728)) (.branch 96 (.leaf 814897416) (.leaf 801765201)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 788867737) (.leaf 776199842)) (.branch 100 (.leaf 763756486) (.leaf 751532788))) (.branch 103 (.branch 102 (.leaf 739524011) (.leaf 727725554)) (.branch 104 (.leaf 716132950) (.leaf 704741858))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 693548059) (.leaf 682547453)) (.branch 108 (.leaf 671736052) (.leaf 661109979))) (.branch 111 (.branch 110 (.leaf 650665460) (.leaf 640398825)) (.branch 112 (.leaf 630306500) (.leaf 620385008)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 610630959) (.leaf 601041053)) (.branch 116 (.leaf 591612077) (.leaf 582340896))) (.branch 119 (.branch 118 (.leaf 573224456) (.leaf 564259779)) (.branch 120 (.leaf 555443961) (.leaf 546774170)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 220).prefactor = (4648543194388167/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 220).cutoff/(generalMeanRows 220).c)).2 =
    (421043266794909/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 220).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 220).q*(generalMeanRows 220).cutoff/2-2 = (535/273:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable115.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 220).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 220).criticalRate j.val*(generalMeanRows 220).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 220).c*(generalMeanRows 220).criticalPoint j.val)).2-
      (generalMeanRows 220).J/2-(generalMeanRows 220).error (generalMeanGrid j.val)+
      (generalMeanRows 220).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 220).c)).2-
      (generalMeanRows 220).J/2-(generalMeanRows 220).error 4 := by
  have he : (generalMeanRows 220).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 220) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 220)
    (generalMeanRows_prefactorDomain 220) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0220

/-! Kernel-checked entropy margins for general spectral rectangle 221. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0221
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5555331432) (.branch 2 (.leaf 5371634644) (.leaf 5196062260))) (.branch 5 (.branch 4 (.leaf 5028155754) (.leaf 4867488737)) (.branch 6 (.leaf 4713664151) (.leaf 4566311758)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4425085911) (.leaf 4289663540)) (.branch 10 (.leaf 4159742353) (.leaf 4035039205))) (.branch 13 (.branch 12 (.leaf 3915288630) (.leaf 3800241505)) (.branch 14 (.leaf 3689663845) (.leaf 3583335695))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3481050132) (.branch 17 (.leaf 3382612342) (.leaf 3287838781))) (.branch 20 (.branch 19 (.leaf 3196556408) (.leaf 3108601974)) (.branch 21 (.leaf 3023821370) (.leaf 2942069031)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2863207380) (.leaf 2787106318)) (.branch 25 (.leaf 2713642752) (.leaf 2642700154))) (.branch 28 (.branch 27 (.leaf 2574168159) (.leaf 2507942186)) (.branch 29 (.leaf 2443923088) (.leaf 2382016826)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2322134169) (.branch 32 (.leaf 2264190406) (.leaf 2208105087))) (.branch 35 (.branch 34 (.leaf 2153801777) (.leaf 2101207822)) (.branch 36 (.leaf 2050254138) (.leaf 2000875011)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1953007905) (.leaf 1906593288)) (.branch 40 (.leaf 1861574468) (.leaf 1817897435))) (.branch 43 (.branch 42 (.leaf 1775510718) (.leaf 1734365246)) (.branch 44 (.leaf 1694414223) (.leaf 1655613005))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1617918986) (.branch 47 (.leaf 1581291492) (.leaf 1545691683))) (.branch 50 (.branch 49 (.leaf 1511082452) (.leaf 1477428343)) (.branch 51 (.leaf 1444695460) (.leaf 1412851393)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1381865142) (.leaf 1351707041)) (.branch 55 (.leaf 1322348701) (.leaf 1293762937))) (.branch 58 (.branch 57 (.leaf 1265923715) (.leaf 1238806094)) (.branch 59 (.leaf 1212386170) (.leaf 1186641030))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1161548700) (.branch 62 (.leaf 1137088105) (.leaf 1113239021))) (.branch 65 (.branch 64 (.leaf 1089982037) (.leaf 1067298518)) (.branch 66 (.leaf 1045170566) (.leaf 1023580987)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1002513259) (.leaf 981951498)) (.branch 70 (.leaf 961880433) (.leaf 942285375))) (.branch 73 (.branch 72 (.leaf 923152192) (.leaf 904467283)) (.branch 74 (.leaf 886217555) (.leaf 868390399))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 850973671) (.branch 77 (.leaf 833955669) (.leaf 817325114))) (.branch 80 (.branch 79 (.leaf 801071133) (.leaf 785183240)) (.branch 81 (.leaf 769651321) (.leaf 754465615)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 739616703) (.leaf 725095489)) (.branch 85 (.leaf 710893191) (.leaf 697001324))) (.branch 88 (.branch 87 (.leaf 683411691) (.leaf 670116368)) (.branch 89 (.leaf 657107694) (.leaf 644378261)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 631920904) (.branch 92 (.leaf 619728689) (.leaf 607794905))) (.branch 95 (.branch 94 (.leaf 596113057) (.leaf 584676853)) (.branch 96 (.leaf 573480202) (.leaf 562517199)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 551782126) (.leaf 541269436)) (.branch 100 (.leaf 530973755) (.leaf 520889867))) (.branch 103 (.branch 102 (.leaf 511012717) (.leaf 501337396)) (.branch 104 (.leaf 491859143) (.leaf 482573335))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 473475484) (.leaf 464561230)) (.branch 108 (.leaf 455826339) (.leaf 447266697))) (.branch 111 (.branch 110 (.leaf 438878306) (.leaf 430657279)) (.branch 112 (.leaf 422599838) (.leaf 414702309)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 406961118) (.leaf 399372788)) (.branch 116 (.leaf 391933936) (.leaf 384641269))) (.branch 119 (.branch 118 (.leaf 377491584) (.leaf 370481759)) (.branch 120 (.leaf 363608755) (.leaf 356869613)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 221).prefactor = (239997004581687/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 221).cutoff/(generalMeanRows 221).c)).2 =
    (377746461041587/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 221).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 221).q*(generalMeanRows 221).c/2-2 = (357/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable067.value]
  have hcontinuation : (generalMeanRows 221).q*(generalMeanRows 221).cutoff/2-2 = (535/273:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable115.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 221).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 221).criticalRate j.val*(generalMeanRows 221).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 221).c*(generalMeanRows 221).criticalPoint j.val)).2-
      (generalMeanRows 221).J/2-(generalMeanRows 221).error (generalMeanGrid j.val)+
      (generalMeanRows 221).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 221).c)).2-
      (generalMeanRows 221).J/2-(generalMeanRows 221).error 4 := by
  have he : (generalMeanRows 221).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 221) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 221)
    (generalMeanRows_prefactorDomain 221) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0221

/-! Kernel-checked entropy margins for general spectral rectangle 222. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0222
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5414103497) (.branch 2 (.leaf 5237984663) (.leaf 5069687213))) (.branch 5 (.branch 4 (.leaf 4908764518) (.leaf 4754801472)) (.branch 6 (.leaf 4607411738) (.leaf 4466235297)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4330936247) (.leaf 4201200840)) (.branch 10 (.leaf 4076735702) (.leaf 3957266238))) (.branch 13 (.branch 12 (.leaf 3842535186) (.leaf 3732301305)) (.branch 14 (.leaf 3626338182) (.leaf 3524433152))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3426386305) (.branch 17 (.leaf 3332009583) (.leaf 3241125956))) (.branch 20 (.branch 19 (.leaf 3153568656) (.leaf 3069180488)) (.branch 21 (.leaf 2987813182) (.leaf 2909326805)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2833589217) (.leaf 2760475566)) (.branch 25 (.leaf 2689867822) (.leaf 2621654349))) (.branch 28 (.branch 27 (.leaf 2555729501) (.leaf 2491993255)) (.branch 29 (.leaf 2430350864) (.leaf 2370712540)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2312993150) (.branch 32 (.leaf 2257111947) (.leaf 2202992304))) (.branch 35 (.branch 34 (.leaf 2150561475) (.leaf 2099750371)) (.branch 36 (.leaf 2050493348) (.leaf 2002728010)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1956395026) (.leaf 1911437956)) (.branch 40 (.leaf 1867803089) (.leaf 1825439296))) (.branch 43 (.branch 42 (.leaf 1784297881) (.leaf 1744332453)) (.branch 44 (.leaf 1705498800) (.leaf 1667754767))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1631060153) (.branch 47 (.leaf 1595376602) (.leaf 1560667504))) (.branch 50 (.branch 49 (.leaf 1526897907) (.leaf 1494034430)) (.branch 51 (.leaf 1462045178) (.leaf 1430899668)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1400568755) (.leaf 1371024565)) (.branch 55 (.leaf 1342240430) (.leaf 1314190827))) (.branch 58 (.branch 57 (.leaf 1286851320) (.leaf 1260198505)) (.branch 59 (.leaf 1234209963) (.leaf 1208864207))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1184140637) (.branch 62 (.leaf 1160019499) (.leaf 1136481842))) (.branch 65 (.branch 64 (.leaf 1113509478) (.leaf 1091084951)) (.branch 66 (.leaf 1069191495) (.leaf 1047813007)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1026934011) (.leaf 1006539634)) (.branch 70 (.leaf 986615573) (.leaf 967148070))) (.branch 73 (.branch 72 (.leaf 948123890) (.leaf 929530293)) (.branch 74 (.leaf 911355012) (.leaf 893586235))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 876212580) (.branch 77 (.leaf 859223080) (.leaf 842607162))) (.branch 80 (.branch 79 (.leaf 826354629) (.leaf 810455646)) (.branch 81 (.leaf 794900722) (.leaf 779680697)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 764786727) (.leaf 750210268)) (.branch 85 (.leaf 735943069) (.leaf 721977153))) (.branch 88 (.branch 87 (.leaf 708304810) (.leaf 694918585)) (.branch 89 (.leaf 681811266) (.leaf 668975876)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 656405661) (.branch 92 (.leaf 644094084) (.leaf 632034815))) (.branch 95 (.branch 94 (.leaf 620221719) (.leaf 608648855)) (.branch 96 (.leaf 597310465) (.leaf 586200964)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 575314938) (.leaf 564647136)) (.branch 100 (.leaf 554192463) (.leaf 543945974))) (.branch 103 (.branch 102 (.leaf 533902867) (.leaf 524058483)) (.branch 104 (.leaf 514408293) (.leaf 504947901))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 495673033) (.leaf 486579536)) (.branch 108 (.leaf 477663372) (.leaf 468920614))) (.branch 111 (.branch 110 (.leaf 460347444) (.leaf 451940146)) (.branch 112 (.leaf 443695106) (.leaf 435608806)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 427677820) (.leaf 419898814)) (.branch 116 (.leaf 412268540) (.leaf 404783836))) (.branch 119 (.branch 118 (.leaf 397441618) (.leaf 390238883)) (.branch 120 (.leaf 383172705) (.leaf 376240231)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 222).prefactor = (4697060392981179/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 222).cutoff/(generalMeanRows 222).c)).2 =
    (50020006984811/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 222).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 222).q*(generalMeanRows 222).c/2-2 = (7/10:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable043.value]
  have hcontinuation : (generalMeanRows 222).q*(generalMeanRows 222).cutoff/2-2 = (71/35:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable023.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 222).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 222).criticalRate j.val*(generalMeanRows 222).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 222).c*(generalMeanRows 222).criticalPoint j.val)).2-
      (generalMeanRows 222).J/2-(generalMeanRows 222).error (generalMeanGrid j.val)+
      (generalMeanRows 222).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 222).c)).2-
      (generalMeanRows 222).J/2-(generalMeanRows 222).error 4 := by
  have he : (generalMeanRows 222).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 222) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 222)
    (generalMeanRows_prefactorDomain 222) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0222

/-! Kernel-checked entropy margins for general spectral rectangle 223. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0223
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5375147676) (.branch 2 (.leaf 5206578311) (.leaf 5045498269))) (.branch 5 (.branch 4 (.leaf 4891473771) (.leaf 4744101942)) (.branch 6 (.leaf 4603008104) (.leaf 4467843378)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4338282520) (.leaf 4214021996)) (.branch 10 (.leaf 4094778230) (.leaf 3980286039))) (.branch 13 (.branch 12 (.leaf 3870297208) (.leaf 3764579200)) (.branch 14 (.leaf 3662913984) (.leaf 3565096970))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3470936029) (.branch 17 (.leaf 3380250610) (.leaf 3292870921))) (.branch 20 (.branch 19 (.leaf 3208637181) (.leaf 3127398937)) (.branch 21 (.leaf 3049014427) (.leaf 2973350004)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2900279598) (.leaf 2829684216)) (.branch 25 (.leaf 2761451490) (.leaf 2695475250))) (.branch 28 (.branch 27 (.leaf 2631655132) (.leaf 2569896212)) (.branch 29 (.leaf 2510108671) (.leaf 2452207476)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2396112091) (.branch 32 (.leaf 2341746204) (.leaf 2289037473))) (.branch 35 (.branch 34 (.leaf 2237917290) (.leaf 2188320560)) (.branch 36 (.leaf 2140185494) (.leaf 2093453419)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2048068596) (.leaf 2003978053)) (.branch 40 (.leaf 1961131426) (.leaf 1919480811))) (.branch 43 (.branch 42 (.leaf 1878980629) (.leaf 1839587494)) (.branch 44 (.leaf 1801260090) (.leaf 1763959060))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1727646897) (.branch 47 (.leaf 1692287843) (.leaf 1657847794))) (.branch 50 (.branch 49 (.leaf 1624294215) (.leaf 1591596050)) (.branch 51 (.leaf 1559723650) (.leaf 1528648692)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1498344115) (.leaf 1468784052)) (.branch 55 (.leaf 1439943766) (.leaf 1411799597))) (.branch 58 (.branch 57 (.leaf 1384328900) (.leaf 1357510000)) (.branch 59 (.leaf 1331322138) (.leaf 1305745425))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1280760803) (.branch 62 (.leaf 1256349999) (.leaf 1232495487))) (.branch 65 (.branch 64 (.leaf 1209180452) (.leaf 1186388756)) (.branch 66 (.leaf 1164104904) (.leaf 1142314012)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1121001778) (.leaf 1100154458)) (.branch 70 (.leaf 1079758833) (.leaf 1059802190))) (.branch 73 (.branch 72 (.leaf 1040272292) (.leaf 1021157365)) (.branch 74 (.leaf 1002446066) (.leaf 984127472))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 966191054) (.branch 77 (.leaf 948626665) (.leaf 931424518))) (.branch 80 (.branch 79 (.leaf 914575172) (.leaf 898069518)) (.branch 81 (.leaf 881898759) (.leaf 866054404)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 850528248) (.leaf 835312363)) (.branch 85 (.leaf 820399085) (.leaf 805781003))) (.branch 88 (.branch 87 (.leaf 791450948) (.leaf 777401984)) (.branch 89 (.leaf 763627395) (.leaf 750120680)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 736875543) (.branch 92 (.leaf 723885881) (.leaf 711145782))) (.branch 95 (.branch 94 (.leaf 698649513) (.leaf 686391514)) (.branch 96 (.leaf 674366392) (.leaf 662568913)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 650993998) (.leaf 639636714)) (.branch 100 (.leaf 628492272) (.leaf 617556017))) (.branch 103 (.branch 102 (.leaf 606823427) (.leaf 596290107)) (.branch 104 (.leaf 585951783) (.leaf 575804298))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 565843609) (.leaf 556065782)) (.branch 108 (.leaf 546466987) (.leaf 537043497))) (.branch 111 (.branch 110 (.leaf 527791680) (.leaf 518708003)) (.branch 112 (.leaf 509789019) (.leaf 501031373)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 492431793) (.leaf 483987090)) (.branch 116 (.leaf 475694154) (.leaf 467549952))) (.branch 119 (.branch 118 (.leaf 459551525) (.leaf 451695987)) (.branch 120 (.leaf 443980520) (.leaf 436402374)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 223).prefactor = (1146626331015131/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 223).cutoff/(generalMeanRows 223).c)).2 =
    (86536649516809/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 223).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 223).q*(generalMeanRows 223).c/2-2 = (331/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable116.value]
  have hcontinuation : (generalMeanRows 223).q*(generalMeanRows 223).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable030.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 223).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 223).criticalRate j.val*(generalMeanRows 223).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 223).c*(generalMeanRows 223).criticalPoint j.val)).2-
      (generalMeanRows 223).J/2-(generalMeanRows 223).error (generalMeanGrid j.val)+
      (generalMeanRows 223).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 223).c)).2-
      (generalMeanRows 223).J/2-(generalMeanRows 223).error 4 := by
  have he : (generalMeanRows 223).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 223) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 223)
    (generalMeanRows_prefactorDomain 223) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0223

/-! Kernel-checked entropy margins for general spectral rectangle 224. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0224
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4871837865) (.branch 2 (.leaf 4696170598) (.leaf 4528571102))) (.branch 5 (.branch 4 (.leaf 4368576551) (.leaf 4215756774)) (.branch 6 (.leaf 4069711408) (.leaf 3930067357)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3796476523) (.leaf 3668613765)) (.branch 10 (.leaf 3546175059) (.leaf 3428875848))) (.branch 13 (.branch 12 (.leaf 3316449538) (.leaf 3208646141)) (.branch 14 (.leaf 3105231042) (.leaf 3005983872))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2910697483) (.branch 17 (.leaf 2819177011) (.leaf 2731239020))) (.branch 20 (.branch 19 (.leaf 2646710709) (.leaf 2565429196)) (.branch 21 (.leaf 2487240848) (.leaf 2412000669)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2339571737) (.leaf 2269824681)) (.branch 25 (.leaf 2202637195) (.leaf 2137893596))) (.branch 28 (.branch 27 (.leaf 2075484409) (.leaf 2015305978)) (.branch 29 (.leaf 1957260115) (.leaf 1901253765)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1847198697) (.branch 32 (.leaf 1795011217) (.leaf 1744611902))) (.branch 35 (.branch 34 (.leaf 1695925348) (.leaf 1648879935)) (.branch 36 (.leaf 1603407612) (.leaf 1559443693)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1516926666) (.leaf 1475798010)) (.branch 40 (.leaf 1436002037) (.leaf 1397485727))) (.branch 43 (.branch 42 (.leaf 1360198584) (.leaf 1324092500)) (.branch 44 (.leaf 1289121624) (.leaf 1255242239))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1222412650) (.branch 47 (.leaf 1190593075) (.leaf 1159745547))) (.branch 50 (.branch 49 (.leaf 1129833813) (.leaf 1100823252)) (.branch 51 (.leaf 1072680785) (.leaf 1045374797)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1018875063) (.leaf 993152679)) (.branch 55 (.leaf 968179990) (.leaf 943930533))) (.branch 58 (.branch 57 (.leaf 920378974) (.leaf 897501054)) (.branch 59 (.leaf 875273536) (.leaf 853674151))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 832681558) (.branch 62 (.leaf 812275293) (.leaf 792435729))) (.branch 65 (.branch 64 (.leaf 773144037) (.leaf 754382145)) (.branch 66 (.leaf 736132707) (.leaf 718379064)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 701105215) (.leaf 684295785)) (.branch 70 (.leaf 667935998) (.leaf 652011647))) (.branch 73 (.branch 72 (.leaf 636509070) (.leaf 621415123)) (.branch 74 (.leaf 606717161) (.leaf 592403011))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 578460954) (.branch 77 (.leaf 564879703) (.leaf 551648385))) (.branch 80 (.branch 79 (.leaf 538756524) (.leaf 526194021)) (.branch 81 (.leaf 513951142) (.leaf 502018497)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 490387029) (.leaf 479048000)) (.branch 85 (.leaf 467992976) (.leaf 457213814))) (.branch 88 (.branch 87 (.leaf 446702653) (.leaf 436451899)) (.branch 89 (.leaf 426454214) (.leaf 416702509)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 407189931) (.branch 92 (.leaf 397909855) (.leaf 388855873))) (.branch 95 (.branch 94 (.leaf 380021787) (.leaf 371401602)) (.branch 96 (.leaf 362989514) (.leaf 354779906)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 346767341) (.leaf 338946553)) (.branch 100 (.leaf 331312440) (.leaf 323860063))) (.branch 103 (.branch 102 (.leaf 316584631) (.leaf 309481505)) (.branch 104 (.leaf 302546185) (.leaf 295774310))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 289161650) (.leaf 282704100)) (.branch 108 (.leaf 276397681) (.leaf 270238530))) (.branch 111 (.branch 110 (.leaf 264222898) (.leaf 258347145)) (.branch 112 (.leaf 252607739) (.leaf 247001249)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 241524343) (.leaf 236173783)) (.branch 116 (.leaf 230946426) (.leaf 225839216))) (.branch 119 (.branch 118 (.leaf 220849183) (.leaf 215973441)) (.branch 120 (.leaf 211209183) (.leaf 206553681)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 224).prefactor = (4839574999439711/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 224).cutoff/(generalMeanRows 224).c)).2 =
    (355440903248657/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 224).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 224).q*(generalMeanRows 224).c/2-2 = (343/400:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable096.value]
  have hcontinuation : (generalMeanRows 224).q*(generalMeanRows 224).cutoff/2-2 = (862/415:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable117.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 224).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 224).criticalRate j.val*(generalMeanRows 224).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 224).c*(generalMeanRows 224).criticalPoint j.val)).2-
      (generalMeanRows 224).J/2-(generalMeanRows 224).error (generalMeanGrid j.val)+
      (generalMeanRows 224).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 224).c)).2-
      (generalMeanRows 224).J/2-(generalMeanRows 224).error 4 := by
  have he : (generalMeanRows 224).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 224) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 224)
    (generalMeanRows_prefactorDomain 224) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0224

/-! Kernel-checked entropy margins for general spectral rectangle 225. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0225
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5282019979) (.branch 2 (.leaf 5113684368) (.leaf 4952908105))) (.branch 5 (.branch 4 (.leaf 4799249576) (.leaf 4652298788)) (.branch 6 (.leaf 4511674604) (.leaf 4377022283)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4248011268) (.leaf 4124333207)) (.branch 10 (.leaf 4005700168) (.leaf 3891843023))) (.branch 13 (.branch 12 (.leaf 3782509995) (.leaf 3677465331)) (.branch 14 (.leaf 3576488102) (.leaf 3479371107))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3385919871) (.branch 17 (.leaf 3295951739) (.leaf 3209295032))) (.branch 20 (.branch 19 (.leaf 3125788284) (.leaf 3045279538)) (.branch 21 (.leaf 2967625696) (.leaf 2892691925)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2820351103) (.leaf 2750483315)) (.branch 25 (.leaf 2682975382) (.leaf 2617720425))) (.branch 28 (.branch 27 (.leaf 2554617465) (.leaf 2493571048)) (.branch 29 (.leaf 2434490898) (.leaf 2377291598)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2321892287) (.branch 32 (.leaf 2268216384) (.leaf 2216191330))) (.branch 35 (.branch 34 (.leaf 2165748342) (.leaf 2116822192)) (.branch 36 (.leaf 2069350993) (.leaf 2023276007)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1978541457) (.leaf 1935094356)) (.branch 40 (.leaf 1892884352) (.leaf 1851863569))) (.branch 43 (.branch 42 (.leaf 1811986472) (.leaf 1773209735)) (.branch 44 (.leaf 1735492115) (.leaf 1698794337))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1663078985) (.branch 47 (.leaf 1628310401) (.leaf 1594454587))) (.branch 50 (.branch 49 (.leaf 1561479117) (.leaf 1529353051)) (.branch 51 (.leaf 1498046854) (.leaf 1467532324)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1437782520) (.leaf 1408771694)) (.branch 55 (.leaf 1380475232) (.leaf 1352869591))) (.branch 58 (.branch 57 (.leaf 1325932247) (.leaf 1299641641)) (.branch 59 (.leaf 1273977129) (.leaf 1248918936))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1224448114) (.branch 62 (.leaf 1200546498) (.leaf 1177196668))) (.branch 65 (.branch 64 (.leaf 1154381911) (.leaf 1132086188)) (.branch 66 (.leaf 1110294099) (.leaf 1088990854)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1068162240) (.leaf 1047794598)) (.branch 70 (.leaf 1027874793) (.leaf 1008390190))) (.branch 73 (.branch 72 (.leaf 989328630) (.leaf 970678410)) (.branch 74 (.leaf 952428257) (.leaf 934567315))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 917085119) (.branch 77 (.leaf 899971580) (.leaf 883216970))) (.branch 80 (.branch 79 (.leaf 866811903) (.leaf 850747319)) (.branch 81 (.leaf 835014472) (.leaf 819604917)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 804510492) (.leaf 789723311)) (.branch 85 (.leaf 775235748) (.leaf 761040430))) (.branch 88 (.branch 87 (.leaf 747130222) (.leaf 733498219)) (.branch 89 (.leaf 720137737) (.leaf 707042305)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 694205650) (.branch 92 (.leaf 681621697) (.leaf 669284557))) (.branch 95 (.branch 94 (.leaf 657188517) (.leaf 645328039)) (.branch 96 (.leaf 633697749) (.leaf 622292431)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 611107022) (.leaf 600136604)) (.branch 100 (.leaf 589376402) (.leaf 578821775))) (.branch 103 (.branch 102 (.leaf 568468214) (.leaf 558311334)) (.branch 104 (.leaf 548346872) (.leaf 538570681))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 528978728) (.leaf 519567086)) (.branch 108 (.leaf 510331934) (.leaf 501269551))) (.branch 111 (.branch 110 (.leaf 492376315) (.leaf 483648696)) (.branch 112 (.leaf 475083256) (.leaf 466676643)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 458425593) (.leaf 450326919)) (.branch 116 (.leaf 442377519) (.leaf 434574363))) (.branch 119 (.branch 118 (.leaf 426914496) (.leaf 419395038)) (.branch 120 (.leaf 412013174) (.leaf 404766159)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 225).prefactor = (186030736030513/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 225).cutoff/(generalMeanRows 225).c)).2 =
    (87285787898849/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 225).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 225).q*(generalMeanRows 225).c/2-2 = (171/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable097.value]
  have hcontinuation : (generalMeanRows 225).q*(generalMeanRows 225).cutoff/2-2 = (536/249:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable118.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 225).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 225).criticalRate j.val*(generalMeanRows 225).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 225).c*(generalMeanRows 225).criticalPoint j.val)).2-
      (generalMeanRows 225).J/2-(generalMeanRows 225).error (generalMeanGrid j.val)+
      (generalMeanRows 225).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 225).c)).2-
      (generalMeanRows 225).J/2-(generalMeanRows 225).error 4 := by
  have he : (generalMeanRows 225).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 225) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 225)
    (generalMeanRows_prefactorDomain 225) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0225

/-! Kernel-checked entropy margins for general spectral rectangle 226. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0226
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5356173125) (.branch 2 (.leaf 5185463180) (.leaf 5022358443))) (.branch 5 (.branch 4 (.leaf 4866419047) (.leaf 4717236432)) (.branch 6 (.leaf 4574430612) (.leaf 4437647736)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4306557902) (.leaf 4180853202)) (.branch 10 (.leaf 4060245954) (.leaf 3944467109))) (.branch 13 (.branch 12 (.leaf 3833264814) (.leaf 3726403099)) (.branch 14 (.leaf 3623660696) (.leaf 3524829953))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3429715852) (.branch 17 (.leaf 3338135103) (.leaf 3249915320))) (.branch 20 (.branch 19 (.leaf 3164894265) (.leaf 3082919152)) (.branch 21 (.leaf 3003846007) (.leaf 2927539079)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2853870295) (.leaf 2782718761)) (.branch 25 (.leaf 2713970299) (.leaf 2647517011))) (.branch 28 (.branch 27 (.leaf 2583256889) (.leaf 2521093440)) (.branch 29 (.leaf 2460935347) (.leaf 2402696148)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2346293941) (.branch 32 (.leaf 2291651111) (.leaf 2238694066))) (.branch 35 (.branch 34 (.leaf 2187353004) (.leaf 2137561688)) (.branch 36 (.leaf 2089257236) (.leaf 2042379925)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1996873014) (.leaf 1952682565)) (.branch 40 (.leaf 1909757293) (.leaf 1868048408))) (.branch 43 (.branch 42 (.leaf 1827509481) (.leaf 1788096310)) (.branch 44 (.leaf 1749766795) (.leaf 1712480826))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1676200172) (.branch 47 (.leaf 1640888381) (.leaf 1606510681))) (.branch 50 (.branch 49 (.leaf 1573033892) (.leaf 1540426341)) (.branch 51 (.leaf 1508657783) (.leaf 1477699324)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1447523351) (.leaf 1418103465)) (.branch 55 (.leaf 1389414420) (.leaf 1361432061))) (.branch 58 (.branch 57 (.leaf 1334133272) (.leaf 1307495918)) (.branch 59 (.leaf 1281498801) (.leaf 1256121608))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1231344871) (.branch 62 (.leaf 1207149922) (.leaf 1183518855))) (.branch 65 (.branch 64 (.leaf 1160434489) (.leaf 1137880331)) (.branch 66 (.leaf 1115840545) (.leaf 1094299918)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1073243831) (.leaf 1052658232)) (.branch 70 (.leaf 1032529607) (.leaf 1012844957))) (.branch 73 (.branch 72 (.leaf 993591772) (.leaf 974758009)) (.branch 74 (.leaf 956332071) (.leaf 938302785))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 920659387) (.branch 77 (.leaf 903391495) (.leaf 886489103))) (.branch 80 (.branch 79 (.leaf 869942553) (.leaf 853742529)) (.branch 81 (.leaf 837880035) (.leaf 822346386)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 807133191) (.leaf 792232342)) (.branch 85 (.leaf 777636002) (.leaf 763336592))) (.branch 88 (.branch 87 (.leaf 749326782) (.leaf 735599478)) (.branch 89 (.leaf 722147817) (.leaf 708965152)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 696045046) (.branch 92 (.leaf 683381262) (.leaf 670967758))) (.branch 95 (.branch 94 (.leaf 658798675) (.leaf 646868333)) (.branch 96 (.leaf 635171222) (.leaf 623701996)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 612455467) (.leaf 601426600)) (.branch 100 (.leaf 590610503) (.leaf 580002426))) (.branch 103 (.branch 102 (.leaf 569597754) (.leaf 559392003)) (.branch 104 (.leaf 549380811) (.leaf 539559940))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 529925268) (.leaf 520472782)) (.branch 108 (.leaf 511198580) (.leaf 502098864))) (.branch 111 (.branch 110 (.leaf 493169936) (.leaf 484408195)) (.branch 112 (.leaf 475810134) (.leaf 467372336)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 459091473) (.leaf 450964300)) (.branch 116 (.leaf 442987656) (.leaf 435158455))) (.branch 119 (.branch 118 (.leaf 427473692) (.leaf 419930433)) (.branch 120 (.leaf 412525818) (.leaf 405257054)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 226).prefactor = (581442370523557/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 226).cutoff/(generalMeanRows 226).c)).2 =
    (424452748447531/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 226).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 226).q*(generalMeanRows 226).c/2-2 = (171/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable097.value]
  have hcontinuation : (generalMeanRows 226).q*(generalMeanRows 226).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable030.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 226).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 226).criticalRate j.val*(generalMeanRows 226).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 226).c*(generalMeanRows 226).criticalPoint j.val)).2-
      (generalMeanRows 226).J/2-(generalMeanRows 226).error (generalMeanGrid j.val)+
      (generalMeanRows 226).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 226).c)).2-
      (generalMeanRows 226).J/2-(generalMeanRows 226).error 4 := by
  have he : (generalMeanRows 226).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 226) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 226)
    (generalMeanRows_prefactorDomain 226) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0226

/-! Kernel-checked entropy margins for general spectral rectangle 227. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0227
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5067428357) (.branch 2 (.leaf 4895730961) (.leaf 4731782160))) (.branch 5 (.branch 4 (.leaf 4575135763) (.leaf 4425377226)) (.branch 6 (.leaf 4282120888) (.leaf 4145007511)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4013702071) (.leaf 3887891778)) (.branch 10 (.leaf 3767284297) (.leaf 3651606136))) (.branch 13 (.branch 12 (.leaf 3540601193) (.leaf 3434029433)) (.branch 14 (.leaf 3331665693) (.leaf 3233298588))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3138729515) (.branch 17 (.leaf 3047771742) (.leaf 2960249576))) (.branch 20 (.branch 19 (.leaf 2875997596) (.leaf 2794859953)) (.branch 21 (.leaf 2716689723) (.leaf 2641348315)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2568704916) (.leaf 2498635992)) (.branch 25 (.leaf 2431024812) (.leaf 2365761021))) (.branch 28 (.branch 27 (.leaf 2302740235) (.leaf 2241863666)) (.branch 29 (.leaf 2183037782) (.leaf 2126173978)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2071188284) (.branch 32 (.leaf 2018001081) (.leaf 1966536845))) (.branch 35 (.branch 34 (.leaf 1916723903) (.leaf 1868494206)) (.branch 36 (.leaf 1821783124) (.leaf 1776529240)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1732674174) (.leaf 1690162406)) (.branch 40 (.leaf 1648941116) (.leaf 1608960032))) (.branch 43 (.branch 42 (.leaf 1570171290) (.leaf 1532529297)) (.branch 44 (.leaf 1495990613) (.leaf 1460513827))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1426059452) (.branch 47 (.leaf 1392589819) (.leaf 1360068980))) (.branch 50 (.branch 49 (.leaf 1328462618) (.leaf 1297737960)) (.branch 51 (.leaf 1267863698) (.leaf 1238809908)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1210547985) (.leaf 1183050568)) (.branch 55 (.leaf 1156291482) (.leaf 1130245678))) (.branch 58 (.branch 57 (.leaf 1104889169) (.leaf 1080198987)) (.branch 59 (.leaf 1056153124) (.leaf 1032730486))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1009910854) (.branch 62 (.leaf 987674832) (.leaf 966003813))) (.branch 65 (.branch 64 (.leaf 944879940) (.leaf 924286069)) (.branch 66 (.leaf 904205734) (.leaf 884623117)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 865523017) (.leaf 846890819)) (.branch 70 (.leaf 828712469) (.leaf 810974447))) (.branch 73 (.branch 72 (.leaf 793663744) (.leaf 776767834)) (.branch 74 (.leaf 760274660) (.leaf 744172603))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 728450473) (.branch 77 (.leaf 713097480) (.leaf 698103223))) (.branch 80 (.branch 79 (.leaf 683457670) (.leaf 669151142)) (.branch 81 (.leaf 655174301) (.leaf 641518129)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 628173919) (.leaf 615133263)) (.branch 85 (.leaf 602388034) (.leaf 589930379))) (.branch 88 (.branch 87 (.leaf 577752705) (.leaf 565847670)) (.branch 89 (.leaf 554208172) (.leaf 542827337)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 531698516) (.branch 92 (.leaf 520815267) (.leaf 510171355))) (.branch 95 (.branch 94 (.leaf 499760741) (.leaf 489577570)) (.branch 96 (.leaf 479616171) (.leaf 469871046)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 460336863) (.leaf 451008450)) (.branch 100 (.leaf 441880792) (.leaf 432949020))) (.branch 103 (.branch 102 (.leaf 424208410) (.leaf 415654375)) (.branch 104 (.leaf 407282460) (.leaf 399088341))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 391067814) (.leaf 383216795)) (.branch 108 (.leaf 375531317) (.leaf 368007521))) (.branch 111 (.branch 110 (.leaf 360641656) (.leaf 353430075)) (.branch 112 (.leaf 346369228) (.leaf 339455664)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 332686024) (.leaf 326057038)) (.branch 116 (.leaf 319565525) (.leaf 313208385))) (.branch 119 (.branch 118 (.leaf 306982603) (.leaf 300885240)) (.branch 120 (.leaf 294913433) (.leaf 289064394)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 227).prefactor = (4717494738719263/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 227).cutoff/(generalMeanRows 227).c)).2 =
    (39219188622931/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 227).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 227).q*(generalMeanRows 227).c/2-2 = (193/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable071.value]
  have hcontinuation : (generalMeanRows 227).q*(generalMeanRows 227).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable030.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 227).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 227).criticalRate j.val*(generalMeanRows 227).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 227).c*(generalMeanRows 227).criticalPoint j.val)).2-
      (generalMeanRows 227).J/2-(generalMeanRows 227).error (generalMeanGrid j.val)+
      (generalMeanRows 227).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 227).c)).2-
      (generalMeanRows 227).J/2-(generalMeanRows 227).error 4 := by
  have he : (generalMeanRows 227).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 227) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 227)
    (generalMeanRows_prefactorDomain 227) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0227

/-! Kernel-checked entropy margins for general spectral rectangle 228. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0228
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5339914537) (.branch 2 (.leaf 5172552061) (.leaf 5012714144))) (.branch 5 (.branch 4 (.leaf 4859958305) (.leaf 4713873874)) (.branch 6 (.leaf 4574079210) (.leaf 4440219223)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4311963150) (.leaf 4189002558)) (.branch 10 (.leaf 4071049552) (.leaf 3957835142))) (.branch 13 (.branch 12 (.leaf 3849107781) (.leaf 3744632031)) (.branch 14 (.leaf 3644187350) (.leaf 3547566986))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3454576976) (.branch 17 (.leaf 3365035222) (.leaf 3278770648))) (.branch 20 (.branch 19 (.leaf 3195622430) (.leaf 3115439282)) (.branch 21 (.leaf 3038078807) (.leaf 2963406894)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2891297164) (.leaf 2821630459)) (.branch 25 (.leaf 2754294367) (.leaf 2689182786))) (.branch 28 (.branch 27 (.leaf 2626195520) (.leaf 2565237899)) (.branch 29 (.leaf 2506220435) (.leaf 2449058495)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2393672001) (.branch 32 (.leaf 2339985150) (.leaf 2287926151))) (.branch 35 (.branch 34 (.leaf 2237426988) (.leaf 2188423187)) (.branch 36 (.leaf 2140853606) (.leaf 2094660241)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2049788038) (.leaf 2006184724)) (.branch 40 (.leaf 1963800641) (.leaf 1922588602))) (.branch 43 (.branch 42 (.leaf 1882503744) (.leaf 1843503396)) (.branch 44 (.leaf 1805546961) (.leaf 1768595793))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1732613090) (.branch 47 (.leaf 1697563796) (.leaf 1663414497))) (.branch 50 (.branch 49 (.leaf 1630133339) (.leaf 1597689937)) (.branch 51 (.leaf 1566055298) (.leaf 1535201748)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1505102858) (.leaf 1475733378)) (.branch 55 (.leaf 1447069178) (.leaf 1419087185))) (.branch 58 (.branch 57 (.leaf 1391765333) (.leaf 1365082504)) (.branch 59 (.leaf 1339018484) (.leaf 1313553916))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1288670254) (.branch 62 (.leaf 1264349723) (.leaf 1240575283))) (.branch 65 (.branch 64 (.leaf 1217330586) (.leaf 1194599948)) (.branch 66 (.leaf 1172368311) (.leaf 1150621217)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1129344774) (.leaf 1108525631)) (.branch 70 (.leaf 1088150953) (.leaf 1068208392))) (.branch 73 (.branch 72 (.leaf 1048686069) (.leaf 1029572548)) (.branch 74 (.leaf 1010856817) (.leaf 992528268))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 974576678) (.branch 77 (.leaf 956992190) (.leaf 939765298))) (.branch 80 (.branch 79 (.leaf 922886832) (.leaf 906347940)) (.branch 81 (.leaf 890140074) (.leaf 874254981)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 858684683) (.leaf 843421472)) (.branch 85 (.leaf 828457891) (.leaf 813786730))) (.branch 88 (.branch 87 (.leaf 799401012) (.leaf 785293983)) (.branch 89 (.leaf 771459102) (.leaf 757890036)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 744580646) (.branch 92 (.leaf 731524983) (.leaf 718717279))) (.branch 95 (.branch 94 (.leaf 706151940) (.leaf 693823538)) (.branch 96 (.leaf 681726804) (.leaf 669856625)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 658208034) (.leaf 646776207)) (.branch 100 (.leaf 635556457) (.leaf 624544227))) (.branch 103 (.branch 102 (.leaf 613735087) (.leaf 603124730)) (.branch 104 (.leaf 592708964) (.leaf 582483713))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 572445007) (.leaf 562588983)) (.branch 108 (.leaf 552911877) (.leaf 543410025))) (.branch 111 (.branch 110 (.leaf 534079856) (.leaf 524917891)) (.branch 112 (.leaf 515920737) (.leaf 507085088)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 498407720) (.leaf 489885486)) (.branch 116 (.leaf 481515318) (.leaf 473294222))) (.branch 119 (.branch 118 (.leaf 465219275) (.leaf 457287624)) (.branch 120 (.leaf 449496483) (.leaf 441843132)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 228).prefactor = (2325067211943427/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 228).cutoff/(generalMeanRows 228).c)).2 =
    (450701753086723/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 228).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 228).q*(generalMeanRows 228).c/2-2 = (331/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable116.value]
  have hcontinuation : (generalMeanRows 228).q*(generalMeanRows 228).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable092.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 228).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 228).criticalRate j.val*(generalMeanRows 228).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 228).c*(generalMeanRows 228).criticalPoint j.val)).2-
      (generalMeanRows 228).J/2-(generalMeanRows 228).error (generalMeanGrid j.val)+
      (generalMeanRows 228).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 228).c)).2-
      (generalMeanRows 228).J/2-(generalMeanRows 228).error 4 := by
  have he : (generalMeanRows 228).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 228) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 228)
    (generalMeanRows_prefactorDomain 228) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0228

/-! Kernel-checked entropy margins for general spectral rectangle 229. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0229
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5280561976) (.branch 2 (.leaf 5112309789) (.leaf 4951642697))) (.branch 5 (.branch 4 (.leaf 4798115327) (.leaf 4651314297)) (.branch 6 (.leaf 4510855418) (.leaf 4376381203)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4247558630) (.leaf 4124077134)) (.branch 10 (.leaf 4005646804) (.leaf 3891996745))) (.branch 13 (.branch 12 (.leaf 3782873602) (.leaf 3678040223)) (.branch 14 (.leaf 3577274437) (.leaf 3480367947))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3387125315) (.branch 17 (.leaf 3297363041) (.leaf 3210908710))) (.branch 20 (.branch 19 (.leaf 3127600222) (.leaf 3047285071)) (.branch 21 (.leaf 2969819694) (.leaf 2895068866)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2822905140) (.leaf 2753208334)) (.branch 25 (.leaf 2685865058) (.leaf 2620768270))) (.branch 28 (.branch 27 (.leaf 2557816869) (.leaf 2496915321)) (.branch 29 (.leaf 2437973305) (.leaf 2380905388)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2325630722) (.branch 32 (.leaf 2272072765) (.leaf 2220159014))) (.branch 35 (.branch 34 (.leaf 2169820765) (.leaf 2120992885)) (.branch 36 (.leaf 2073613595) (.leaf 2027624278)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1982969289) (.leaf 1939595782)) (.branch 40 (.leaf 1897453552) (.leaf 1856494879))) (.branch 43 (.branch 42 (.leaf 1816674387) (.leaf 1777948912)) (.branch 44 (.leaf 1740277377) (.leaf 1703620677))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1667941563) (.branch 47 (.leaf 1633204548) (.leaf 1599375804))) (.branch 50 (.branch 49 (.leaf 1566423073) (.leaf 1534315582)) (.branch 51 (.leaf 1503023964) (.leaf 1472520179)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1442777448) (.leaf 1413770184)) (.branch 55 (.leaf 1385473926) (.leaf 1357865287))) (.branch 58 (.branch 57 (.leaf 1330921891) (.leaf 1304622324)) (.branch 59 (.leaf 1278946087) (.leaf 1253873543))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1229385880) (.branch 62 (.leaf 1205465063) (.leaf 1182093799))) (.branch 65 (.branch 64 (.leaf 1159255501) (.leaf 1136934248)) (.branch 66 (.leaf 1115114757) (.leaf 1093782349)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1072922921) (.leaf 1052522916)) (.branch 70 (.leaf 1032569302) (.leaf 1013049540))) (.branch 73 (.branch 72 (.leaf 993951564) (.leaf 975263762)) (.branch 74 (.leaf 956974947) (.leaf 939074345))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 921551571) (.branch 77 (.leaf 904396614) (.leaf 887599816))) (.branch 80 (.branch 79 (.leaf 871151863) (.leaf 855043762)) (.branch 81 (.leaf 839266832) (.leaf 823812686)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 808673224) (.leaf 793840613)) (.branch 85 (.leaf 779307282) (.leaf 765065907))) (.branch 88 (.branch 87 (.leaf 751109402) (.leaf 737430908)) (.branch 89 (.leaf 724023785) (.leaf 710881601)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 697998124) (.branch 92 (.leaf 685367317) (.leaf 672983324))) (.branch 95 (.branch 94 (.leaf 660840467) (.leaf 648933239)) (.branch 96 (.leaf 637256295) (.leaf 625804448)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 614572660) (.leaf 603556039)) (.branch 100 (.leaf 592749833) (.leaf 582149423))) (.branch 103 (.branch 102 (.leaf 571750321) (.leaf 561548160)) (.branch 104 (.leaf 551538696) (.leaf 541717798))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 532081449) (.leaf 522625737)) (.branch 108 (.leaf 513346853) (.leaf 504241091))) (.branch 111 (.branch 110 (.leaf 495304837) (.leaf 486534574)) (.branch 112 (.leaf 477926872) (.leaf 469478390)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 461185870) (.leaf 453046134)) (.branch 116 (.leaf 445056085) (.leaf 437212700))) (.branch 119 (.branch 118 (.leaf 429513029) (.leaf 421954195)) (.branch 120 (.leaf 414533390) (.leaf 407247870)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 229).prefactor = (234072065176519/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 229).cutoff/(generalMeanRows 229).c)).2 =
    (442471253950209/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 229).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 229).q*(generalMeanRows 229).c/2-2 = (171/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable097.value]
  have hcontinuation : (generalMeanRows 229).q*(generalMeanRows 229).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable092.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 229).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 229).criticalRate j.val*(generalMeanRows 229).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 229).c*(generalMeanRows 229).criticalPoint j.val)).2-
      (generalMeanRows 229).J/2-(generalMeanRows 229).error (generalMeanGrid j.val)+
      (generalMeanRows 229).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 229).c)).2-
      (generalMeanRows 229).J/2-(generalMeanRows 229).error 4 := by
  have he : (generalMeanRows 229).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 229) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 229)
    (generalMeanRows_prefactorDomain 229) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0229

/-! Kernel-checked entropy margins for general spectral rectangle 230. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0230
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5318150624) (.branch 2 (.leaf 5148663545) (.leaf 4986787522))) (.branch 5 (.branch 4 (.leaf 4832077922) (.leaf 4684121945)) (.branch 6 (.leaf 4542535849) (.leaf 4406962464)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4277068974) (.leaf 4152544917)) (.branch 10 (.leaf 4033100391) (.leaf 3918464429))) (.branch 13 (.branch 12 (.leaf 3808383529) (.leaf 3702620327)) (.branch 14 (.leaf 3600952383) (.leaf 3503171077))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3409080606) (.branch 17 (.leaf 3318497065) (.leaf 3231247599))) (.branch 20 (.branch 19 (.leaf 3147169639) (.leaf 3066110189)) (.branch 21 (.leaf 2987925171) (.leaf 2912478829)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2839643173) (.leaf 2769297468)) (.branch 25 (.leaf 2701327760) (.leaf 2635626439))) (.branch 28 (.branch 27 (.leaf 2572091836) (.leaf 2510627842)) (.branch 29 (.leaf 2451143566) (.leaf 2393553005)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2337774745) (.branch 32 (.leaf 2283731683) (.leaf 2231350761))) (.branch 35 (.branch 34 (.leaf 2180562728) (.leaf 2131301908)) (.branch 36 (.leaf 2083505992) (.leaf 2037115838)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1992075290) (.leaf 1948330998)) (.branch 40 (.leaf 1905832264) (.leaf 1864530886))) (.branch 43 (.branch 42 (.leaf 1824381018) (.leaf 1785339036)) (.branch 44 (.leaf 1747363416) (.leaf 1710414613))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1674454958) (.branch 47 (.leaf 1639448546) (.leaf 1605361148))) (.branch 50 (.branch 49 (.leaf 1572160116) (.leaf 1539814297)) (.branch 51 (.leaf 1508293956) (.leaf 1477570698)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1447617396) (.leaf 1418408127)) (.branch 55 (.leaf 1389918108) (.leaf 1362123636))) (.branch 58 (.branch 57 (.leaf 1335002033) (.leaf 1308531590)) (.branch 59 (.leaf 1282691525) (.leaf 1257461926))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1232823717) (.branch 62 (.leaf 1208758606) (.leaf 1185249056))) (.branch 65 (.branch 64 (.leaf 1162278239) (.leaf 1139830006)) (.branch 66 (.leaf 1117888853) (.leaf 1096439887)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1075468799) (.leaf 1054961836)) (.branch 70 (.leaf 1034905773) (.leaf 1015287889))) (.branch 73 (.branch 72 (.leaf 996095943) (.leaf 977318149)) (.branch 74 (.leaf 958943160) (.leaf 940960044))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 923358264) (.branch 77 (.leaf 906127663) (.leaf 889258447))) (.branch 80 (.branch 79 (.leaf 872741163) (.leaf 856566692)) (.branch 81 (.leaf 840726228) (.leaf 825211267)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 810013592) (.leaf 795125262)) (.branch 85 (.leaf 780538600) (.leaf 766246181))) (.branch 88 (.branch 87 (.leaf 752240822) (.leaf 738515573)) (.branch 89 (.leaf 725063701) (.leaf 711878692)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 698954231) (.branch 92 (.leaf 686284200) (.leaf 673862669))) (.branch 95 (.branch 94 (.leaf 661683889) (.leaf 649742282)) (.branch 96 (.leaf 638032437) (.leaf 626549103)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 615287182) (.leaf 604241723)) (.branch 100 (.leaf 593407918) (.leaf 582781094))) (.branch 103 (.branch 102 (.leaf 572356711) (.leaf 562130355)) (.branch 104 (.leaf 552097733) (.leaf 542254670))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 532597105) (.leaf 523121085)) (.branch 108 (.leaf 513822761) (.leaf 504698389))) (.branch 111 (.branch 110 (.leaf 495744321) (.leaf 486957002)) (.branch 112 (.leaf 478332972) (.leaf 469868855)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 461561365) (.leaf 453407294)) (.branch 116 (.leaf 445403517) (.leaf 437546985))) (.branch 119 (.branch 118 (.leaf 429834723) (.leaf 422263829)) (.branch 120 (.leaf 414831471) (.leaf 407534884)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 230).prefactor = (4682581089689797/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 230).cutoff/(generalMeanRows 230).c)).2 =
    (87285787898849/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 230).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 230).q*(generalMeanRows 230).c/2-2 = (171/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable097.value]
  have hcontinuation : (generalMeanRows 230).q*(generalMeanRows 230).cutoff/2-2 = (536/249:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable118.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 230).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 230).criticalRate j.val*(generalMeanRows 230).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 230).c*(generalMeanRows 230).criticalPoint j.val)).2-
      (generalMeanRows 230).J/2-(generalMeanRows 230).error (generalMeanGrid j.val)+
      (generalMeanRows 230).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 230).c)).2-
      (generalMeanRows 230).J/2-(generalMeanRows 230).error 4 := by
  have he : (generalMeanRows 230).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 230) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 230)
    (generalMeanRows_prefactorDomain 230) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0230

/-! Kernel-checked entropy margins for general spectral rectangle 231. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0231
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5260581447) (.branch 2 (.leaf 5090222736) (.leaf 4927536704))) (.branch 5 (.branch 4 (.leaf 4772075722) (.leaf 4623424179)) (.branch 6 (.leaf 4481195692) (.leaf 4345030608)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4214593768) (.leaf 4089572502)) (.branch 10 (.leaf 3969674820) (.leaf 3854627779))) (.branch 13 (.branch 12 (.leaf 3744176008) (.leaf 3638080368)) (.branch 14 (.leaf 3536116733) (.leaf 3438074882))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3343757490) (.branch 17 (.leaf 3252979200) (.leaf 3165565775))) (.branch 20 (.branch 19 (.leaf 3081353329) (.leaf 3000187604)) (.branch 21 (.leaf 2921923321) (.leaf 2846423574)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2773559273) (.leaf 2703208628)) (.branch 25 (.leaf 2635256679) (.leaf 2569594847))) (.branch 28 (.branch 27 (.leaf 2506120536) (.leaf 2444736748)) (.branch 29 (.leaf 2385351736) (.leaf 2327878679)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2272235373) (.branch 32 (.leaf 2218343958) (.leaf 2166130648))) (.branch 35 (.branch 34 (.leaf 2115525489) (.leaf 2066462132)) (.branch 36 (.leaf 2018877619) (.leaf 1972712182)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1927909062) (.leaf 1884414331)) (.branch 40 (.leaf 1842176730) (.leaf 1801147519))) (.branch 43 (.branch 42 (.leaf 1761280332) (.leaf 1722531043)) (.branch 44 (.leaf 1684857646) (.leaf 1648220129))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1612580373) (.branch 47 (.leaf 1577902040) (.leaf 1544150481))) (.branch 50 (.branch 49 (.leaf 1511292643) (.leaf 1479296985)) (.branch 51 (.leaf 1448133393) (.leaf 1417773109)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1388188654) (.leaf 1359353768)) (.branch 55 (.leaf 1331243339) (.leaf 1303833347))) (.branch 58 (.branch 57 (.leaf 1277100809) (.leaf 1251023723)) (.branch 59 (.leaf 1225581019) (.leaf 1200752514))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1176518862) (.branch 62 (.leaf 1152861519) (.leaf 1129762697))) (.branch 65 (.branch 64 (.leaf 1107205331) (.leaf 1085173040)) (.branch 66 (.leaf 1063650098) (.leaf 1042621396)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1022072419) (.leaf 1001989213)) (.branch 70 (.leaf 982358360) (.leaf 963166952))) (.branch 73 (.branch 72 (.leaf 944402567) (.leaf 926053248)) (.branch 74 (.leaf 908107480) (.leaf 890554167))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 873382620) (.branch 77 (.leaf 856582530) (.leaf 840143959))) (.branch 80 (.branch 79 (.leaf 824057315) (.leaf 808313345)) (.branch 81 (.leaf 792903114) (.leaf 777817992)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 763049644) (.leaf 748590014)) (.branch 85 (.leaf 734431314) (.leaf 720566013))) (.branch 88 (.branch 87 (.leaf 706986825) (.leaf 693686700)) (.branch 89 (.leaf 680658814) (.leaf 667896560)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 655393537) (.branch 92 (.leaf 643143543) (.leaf 631140568))) (.branch 95 (.branch 94 (.leaf 619378787) (.leaf 607852548)) (.branch 96 (.leaf 596556369) (.leaf 585484933)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 574633077) (.leaf 563995788)) (.branch 100 (.leaf 553568201) (.leaf 543345586))) (.branch 103 (.branch 102 (.leaf 533323349) (.leaf 523497026)) (.branch 104 (.leaf 513862276) (.leaf 504414877))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 495150724) (.leaf 486065824)) (.branch 108 (.leaf 477156289) (.leaf 468418336))) (.branch 111 (.branch 110 (.leaf 459848283) (.leaf 451442542)) (.branch 112 (.leaf 443197621) (.leaf 435110116)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 427176711) (.leaf 419394175)) (.branch 116 (.leaf 411759357) (.leaf 404269186))) (.branch 119 (.branch 118 (.leaf 396920667) (.leaf 389710877)) (.branch 120 (.leaf 382636967) (.leaf 375696156)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 231).prefactor = (942922277442329/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 231).cutoff/(generalMeanRows 231).c)).2 =
    (107066407213771/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 231).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 231).q*(generalMeanRows 231).c/2-2 = (353/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable084.value]
  have hcontinuation : (generalMeanRows 231).q*(generalMeanRows 231).cutoff/2-2 = (536/249:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable118.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 231).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 231).criticalRate j.val*(generalMeanRows 231).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 231).c*(generalMeanRows 231).criticalPoint j.val)).2-
      (generalMeanRows 231).J/2-(generalMeanRows 231).error (generalMeanGrid j.val)+
      (generalMeanRows 231).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 231).c)).2-
      (generalMeanRows 231).J/2-(generalMeanRows 231).error 4 := by
  have he : (generalMeanRows 231).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 231) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 231)
    (generalMeanRows_prefactorDomain 231) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0231

/-! Kernel-checked entropy margins for general spectral rectangle 232. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0232
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5316113188) (.branch 2 (.leaf 5146728249) (.leaf 4984979471))) (.branch 5 (.branch 4 (.leaf 4830418483) (.leaf 4682629120)) (.branch 6 (.leaf 4541224606) (.leaf 4405845048)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4276155181) (.leaf 4151842350)) (.branch 10 (.leaf 4032614692) (.leaf 3918199487))) (.branch 13 (.branch 12 (.leaf 3808341677) (.leaf 3702802510)) (.branch 14 (.leaf 3601358322) (.leaf 3503799412))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3409929027) (.branch 17 (.leaf 3319562431) (.leaf 3232526049))) (.branch 20 (.branch 19 (.leaf 3148656689) (.leaf 3067800819)) (.branch 21 (.leaf 2989813909) (.leaf 2914559824)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2841910258) (.leaf 2771744221)) (.branch 25 (.leaf 2703947558) (.leaf 2638412507))) (.branch 28 (.branch 27 (.leaf 2575037288) (.leaf 2513725723)) (.branch 29 (.leaf 2454386881) (.leaf 2396934756)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2341287956) (.branch 32 (.leaf 2287369421) (.leaf 2235106163))) (.branch 35 (.branch 34 (.leaf 2184429014) (.leaf 2135272401)) (.branch 36 (.leaf 2087574132) (.leaf 2041275193)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1996319565) (.leaf 1952654048)) (.branch 40 (.leaf 1910228097) (.leaf 1868993671))) (.branch 43 (.branch 42 (.leaf 1828905088) (.leaf 1789918895)) (.branch 44 (.leaf 1751993739) (.leaf 1715090248))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1679170926) (.branch 47 (.leaf 1644200045) (.leaf 1610143550))) (.branch 50 (.branch 49 (.leaf 1576968966) (.leaf 1544645312)) (.branch 51 (.leaf 1513143024) (.leaf 1482433873)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1452490901) (.leaf 1423288346)) (.branch 55 (.leaf 1394801585) (.leaf 1367007071))) (.branch 58 (.branch 57 (.leaf 1339882279) (.leaf 1313405652)) (.branch 59 (.leaf 1287556550) (.leaf 1262315206))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1237662680) (.branch 62 (.leaf 1213580817) (.leaf 1190052208))) (.branch 65 (.branch 64 (.leaf 1167060151) (.leaf 1144588621)) (.branch 66 (.leaf 1122622231) (.leaf 1101146203)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1080146339) (.leaf 1059608993)) (.branch 70 (.leaf 1039521041) (.leaf 1019869863))) (.branch 73 (.branch 72 (.leaf 1000643311) (.leaf 981829693)) (.branch 74 (.leaf 963417750) (.leaf 945396633))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 927755887) (.branch 77 (.leaf 910485435) (.leaf 893575553))) (.branch 80 (.branch 79 (.leaf 877016865) (.leaf 860800317)) (.branch 81 (.leaf 844917169) (.leaf 829358979)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 814117590) (.leaf 799185119)) (.branch 85 (.leaf 784553943) (.leaf 770216688))) (.branch 88 (.branch 87 (.leaf 756166221) (.leaf 742395637)) (.branch 89 (.leaf 728898251) (.leaf 715667588)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 702697374) (.branch 92 (.leaf 689981530) (.leaf 677514162))) (.branch 95 (.branch 94 (.leaf 665289554) (.leaf 653302161)) (.branch 96 (.leaf 641546603) (.leaf 630017656)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 618710250) (.leaf 607619460)) (.branch 100 (.leaf 596740502) (.leaf 586068726))) (.branch 103 (.branch 102 (.leaf 575599611) (.leaf 565328765)) (.branch 104 (.leaf 555251912) (.leaf 545364896))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 535663670) (.leaf 526144298)) (.branch 108 (.leaf 516802944) (.leaf 507635877))) (.branch 111 (.branch 110 (.leaf 498639461) (.leaf 489810152)) (.branch 112 (.leaf 481144500) (.leaf 472639138)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 464290789) (.leaf 456096253)) (.branch 116 (.leaf 448052411) (.leaf 440156220))) (.branch 119 (.branch 118 (.leaf 432404712) (.leaf 424794988)) (.branch 120 (.leaf 417324223) (.leaf 409989653)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 232).prefactor = (2356479477864383/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 232).cutoff/(generalMeanRows 232).c)).2 =
    (442471253950209/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 232).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 232).q*(generalMeanRows 232).c/2-2 = (171/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable097.value]
  have hcontinuation : (generalMeanRows 232).q*(generalMeanRows 232).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable092.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 232).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 232).criticalRate j.val*(generalMeanRows 232).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 232).c*(generalMeanRows 232).criticalPoint j.val)).2-
      (generalMeanRows 232).J/2-(generalMeanRows 232).error (generalMeanGrid j.val)+
      (generalMeanRows 232).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 232).c)).2-
      (generalMeanRows 232).J/2-(generalMeanRows 232).error 4 := by
  have he : (generalMeanRows 232).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 232) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 232)
    (generalMeanRows_prefactorDomain 232) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0232

/-! Kernel-checked entropy margins for general spectral rectangle 233. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0233
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5165295887) (.branch 2 (.leaf 4995382448) (.leaf 4833175537))) (.branch 5 (.branch 4 (.leaf 4678223837) (.leaf 4530108389)) (.branch 6 (.leaf 4388439767) (.leaf 4252855552)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4123018079) (.leaf 3998612400)) (.branch 10 (.leaf 3879344460) (.leaf 3764939443))) (.branch 13 (.branch 12 (.leaf 3655140284) (.leaf 3549706307)) (.branch 14 (.leaf 3448411998) (.leaf 3351045882))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3257409500) (.branch 17 (.leaf 3167316471) (.leaf 3080591638))) (.branch 20 (.branch 19 (.leaf 2997070283) (.leaf 2916597403)) (.branch 21 (.leaf 2839027049) (.leaf 2764221713)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2692051767) (.leaf 2622394941)) (.branch 25 (.leaf 2555135842) (.leaf 2490165510))) (.branch 28 (.branch 27 (.leaf 2427381008) (.leaf 2366685038)) (.branch 29 (.leaf 2307985584) (.leaf 2251195588)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2196232641) (.branch 32 (.leaf 2143018699) (.leaf 2091479818))) (.branch 35 (.branch 34 (.leaf 2041545904) (.leaf 1993150490)) (.branch 36 (.leaf 1946230512) (.leaf 1900726116)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1856580466) (.leaf 1813739570)) (.branch 40 (.leaf 1772152115) (.leaf 1731769318))) (.branch 43 (.branch 42 (.leaf 1692544777) (.leaf 1654434337)) (.branch 44 (.leaf 1617395969) (.leaf 1581389646))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1546377235) (.branch 47 (.leaf 1512322389) (.leaf 1479190457))) (.branch 50 (.branch 49 (.leaf 1446948385) (.leaf 1415564630)) (.branch 51 (.leaf 1385009084) (.leaf 1355252993)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1326268886) (.leaf 1298030510)) (.branch 55 (.leaf 1270512761) (.leaf 1243691631))) (.branch 58 (.branch 57 (.leaf 1217544145) (.leaf 1192048312)) (.branch 59 (.leaf 1167183074) (.leaf 1142928256))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1119264526) (.branch 62 (.leaf 1096173348) (.leaf 1073636947))) (.branch 65 (.branch 64 (.leaf 1051638266) (.leaf 1030160936)) (.branch 66 (.leaf 1009189238) (.leaf 988708076)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 968702941) (.leaf 949159889)) (.branch 70 (.leaf 930065509) (.leaf 911406902))) (.branch 73 (.branch 72 (.leaf 893171654) (.leaf 875347813)) (.branch 74 (.leaf 857923871) (.leaf 840888741))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 824231737) (.branch 77 (.leaf 807942557) (.leaf 792011268))) (.branch 80 (.branch 79 (.leaf 776428285) (.leaf 761184358)) (.branch 81 (.leaf 746270556) (.leaf 731678256)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 717399127) (.leaf 703425115)) (.branch 85 (.leaf 689748439) (.leaf 676361570))) (.branch 88 (.branch 87 (.leaf 663257228) (.leaf 650428366)) (.branch 89 (.leaf 637868164) (.leaf 625570019)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 613527535) (.branch 92 (.leaf 601734514) (.leaf 590184950))) (.branch 95 (.branch 94 (.leaf 578873022) (.leaf 567793084)) (.branch 96 (.leaf 556939658) (.leaf 546307432)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 535891247) (.leaf 525686098)) (.branch 100 (.leaf 515687122) (.leaf 505889598))) (.branch 103 (.branch 102 (.leaf 496288937) (.leaf 486880680)) (.branch 104 (.leaf 477660494) (.leaf 468624164))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 459767592) (.leaf 451086791)) (.branch 108 (.leaf 442577883) (.leaf 434237091))) (.branch 111 (.branch 110 (.leaf 426060742) (.leaf 418045258)) (.branch 112 (.leaf 410187154) (.leaf 402483036)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 394929599) (.leaf 387523621)) (.branch 116 (.leaf 380261961) (.leaf 373141558))) (.branch 119 (.branch 118 (.leaf 366159429) (.leaf 359312663)) (.branch 120 (.leaf 352598422) (.leaf 346013936)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 233).prefactor = (1186172199875359/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 233).cutoff/(generalMeanRows 233).c)).2 =
    (106552683269607/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 233).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 233).q*(generalMeanRows 233).c/2-2 = (91/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable102.value]
  have hcontinuation : (generalMeanRows 233).q*(generalMeanRows 233).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable092.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 233).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 233).criticalRate j.val*(generalMeanRows 233).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 233).c*(generalMeanRows 233).criticalPoint j.val)).2-
      (generalMeanRows 233).J/2-(generalMeanRows 233).error (generalMeanGrid j.val)+
      (generalMeanRows 233).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 233).c)).2-
      (generalMeanRows 233).J/2-(generalMeanRows 233).error 4 := by
  have he : (generalMeanRows 233).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 233) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 233)
    (generalMeanRows_prefactorDomain 233) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0233

/-! Kernel-checked entropy margins for general spectral rectangle 234. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0234
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5113803067) (.branch 2 (.leaf 4942983383) (.leaf 4779906936))) (.branch 5 (.branch 4 (.leaf 4624123021) (.leaf 4475213119)) (.branch 6 (.leaf 4332788085) (.leaf 4196485641)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4065968131) (.leaf 3940920503)) (.branch 10 (.leaf 3821048494) (.leaf 3706076989))) (.branch 13 (.branch 12 (.leaf 3595748538) (.leaf 3489822010)) (.branch 14 (.leaf 3388071372) (.leaf 3290284571))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3196262522) (.branch 17 (.leaf 3105818176) (.leaf 3018775670))) (.branch 20 (.branch 19 (.leaf 2934969550) (.leaf 2854244051)) (.branch 21 (.leaf 2776452440) (.leaf 2701456410)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2629125516) (.leaf 2559336666)) (.branch 25 (.leaf 2491973636) (.leaf 2426926633))) (.branch 28 (.branch 27 (.leaf 2364091883) (.leaf 2303371254)) (.branch 29 (.leaf 2244671898) (.leaf 2187905932)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2132990127) (.branch 32 (.leaf 2079845626) (.leaf 2028397683))) (.branch 35 (.branch 34 (.leaf 1978575416) (.leaf 1930311573)) (.branch 36 (.leaf 1883542327) (.leaf 1838207067)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1794248218) (.leaf 1751611061)) (.branch 40 (.leaf 1710243575) (.leaf 1670096279))) (.branch 43 (.branch 42 (.leaf 1631122091) (.leaf 1593276194)) (.branch 44 (.leaf 1556515909) (.leaf 1520800578))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1486091450) (.branch 47 (.leaf 1452351582) (.leaf 1419545737))) (.branch 50 (.branch 49 (.leaf 1387640293) (.leaf 1356603159)) (.branch 51 (.leaf 1326403688) (.leaf 1297012608)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1268401944) (.leaf 1240544953)) (.branch 55 (.leaf 1213416059) (.leaf 1186990793))) (.branch 58 (.branch 57 (.leaf 1161245737) (.leaf 1136158471)) (.branch 59 (.leaf 1111707520) (.leaf 1087872308))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1064633114) (.branch 62 (.leaf 1041971028) (.leaf 1019867911))) (.branch 65 (.branch 64 (.leaf 998306360) (.leaf 977269667)) (.branch 66 (.leaf 956741789) (.leaf 936707316)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 917151439) (.leaf 898059923)) (.branch 70 (.leaf 879419077) (.leaf 861215735))) (.branch 73 (.branch 72 (.leaf 843437222) (.leaf 826071341)) (.branch 74 (.leaf 809106343) (.leaf 792530912))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 776334143) (.branch 77 (.leaf 760505524) (.leaf 745034918))) (.branch 80 (.branch 79 (.leaf 729912545) (.leaf 715128971)) (.branch 81 (.leaf 700675088) (.leaf 686542101)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 672721517) (.leaf 659205127)) (.branch 85 (.leaf 645985000) (.leaf 633053466))) (.branch 88 (.branch 87 (.leaf 620403109) (.leaf 608026754)) (.branch 89 (.leaf 595917457) (.leaf 584068499)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 572473370) (.branch 92 (.leaf 561125768) (.leaf 550019587))) (.branch 95 (.branch 94 (.leaf 539148909) (.leaf 528507997)) (.branch 96 (.leaf 518091289) (.leaf 507893391)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 497909067) (.leaf 488133239)) (.branch 100 (.leaf 478560977) (.leaf 469187494))) (.branch 103 (.branch 102 (.leaf 460008142) (.leaf 451018405)) (.branch 104 (.leaf 442213896) (.leaf 433590351))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 425143625) (.leaf 416869688)) (.branch 108 (.leaf 408764620) (.leaf 400824611))) (.branch 111 (.branch 110 (.leaf 393045949) (.leaf 385425027)) (.branch 112 (.leaf 377958329) (.leaf 370642438)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 363474021) (.leaf 356449835)) (.branch 116 (.leaf 349566721) (.leaf 342821600))) (.branch 119 (.branch 118 (.leaf 336211473) (.leaf 329733417)) (.branch 120 (.leaf 323384581) (.leaf 317162186)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 234).prefactor = (4746860781838207/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 234).cutoff/(generalMeanRows 234).c)).2 =
    (1030340617313/2500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 234).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 234).q*(generalMeanRows 234).c/2-2 = (3/4:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable019.value]
  have hcontinuation : (generalMeanRows 234).q*(generalMeanRows 234).cutoff/2-2 = (536/249:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable118.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 234).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 234).criticalRate j.val*(generalMeanRows 234).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 234).c*(generalMeanRows 234).criticalPoint j.val)).2-
      (generalMeanRows 234).J/2-(generalMeanRows 234).error (generalMeanGrid j.val)+
      (generalMeanRows 234).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 234).c)).2-
      (generalMeanRows 234).J/2-(generalMeanRows 234).error 4 := by
  have he : (generalMeanRows 234).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 234) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 234)
    (generalMeanRows_prefactorDomain 234) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0234

/-! Kernel-checked entropy margins for general spectral rectangle 235. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0235
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5059900378) (.branch 2 (.leaf 4888325654) (.leaf 4724555563))) (.branch 5 (.branch 4 (.leaf 4568136267) (.leaf 4418646306)) (.branch 6 (.leaf 4275693771) (.leaf 4138913788)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4007966251) (.leaf 3882533801)) (.branch 10 (.leaf 3762319991) (.leaf 3647047645))) (.branch 13 (.branch 12 (.leaf 3536457359) (.leaf 3430306153)) (.branch 14 (.leaf 3328366237) (.leaf 3230423890))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3136278442) (.branch 17 (.leaf 3045741337) (.leaf 2958635278))) (.branch 20 (.branch 19 (.leaf 2874793442) (.leaf 2794058761)) (.branch 21 (.leaf 2716283258) (.leaf 2641327437)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2569059721) (.leaf 2499355933)) (.branch 25 (.leaf 2432098812) (.leaf 2367177573))) (.branch 28 (.branch 27 (.leaf 2304487492) (.leaf 2243929528)) (.branch 29 (.leaf 2185409964) (.leaf 2128840079)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2074135844) (.branch 32 (.leaf 2021217636) (.leaf 1970009972))) (.branch 35 (.branch 34 (.leaf 1920441260) (.leaf 1872443574)) (.branch 36 (.leaf 1825952432) (.leaf 1780906599)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1737247898) (.leaf 1694921034)) (.branch 40 (.leaf 1653873429) (.leaf 1614055069))) (.branch 43 (.branch 42 (.leaf 1575418359) (.leaf 1537917990)) (.branch 44 (.leaf 1501510809) (.leaf 1466155700))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1431813476) (.branch 47 (.leaf 1398446772) (.leaf 1366019945))) (.branch 50 (.branch 49 (.leaf 1334498984) (.leaf 1303851421)) (.branch 51 (.leaf 1274046251) (.leaf 1245053852)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1216845917) (.leaf 1189395380)) (.branch 55 (.leaf 1162676359) (.leaf 1136664086))) (.branch 58 (.branch 57 (.leaf 1111334859) (.leaf 1086665982)) (.branch 59 (.leaf 1062635716) (.leaf 1039223232))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1016408566) (.branch 62 (.leaf 994172571) (.leaf 972496885))) (.branch 65 (.branch 64 (.leaf 951363887) (.leaf 930756662)) (.branch 66 (.leaf 910658967) (.leaf 891055199)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 871930367) (.leaf 853270058)) (.branch 70 (.leaf 835060413) (.leaf 817288100))) (.branch 73 (.branch 72 (.leaf 799940292) (.leaf 783004640)) (.branch 74 (.leaf 766469253) (.leaf 750322677))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 734553875) (.branch 77 (.leaf 719152211) (.leaf 704107425))) (.branch 80 (.branch 79 (.leaf 689409626) (.leaf 675049266)) (.branch 81 (.leaf 661017134) (.leaf 647304334)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 633902276) (.leaf 620802662)) (.branch 85 (.leaf 607997473) (.leaf 595478956))) (.branch 88 (.branch 87 (.leaf 583239615) (.leaf 571272201)) (.branch 89 (.leaf 559569699) (.leaf 548125321)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 536932494) (.branch 92 (.leaf 525984856) (.leaf 515276241))) (.branch 95 (.branch 94 (.leaf 504800677) (.leaf 494552377)) (.branch 96 (.leaf 484525730) (.leaf 474715295)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 465115796) (.leaf 455722113)) (.branch 100 (.leaf 446529278) (.leaf 437532469))) (.branch 103 (.branch 102 (.leaf 428727006) (.leaf 420108342)) (.branch 104 (.leaf 411672061) (.leaf 403413874))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 395329612) (.leaf 387415222)) (.branch 108 (.leaf 379666765) (.leaf 372080411))) (.branch 111 (.branch 110 (.leaf 364652434) (.leaf 357379209)) (.branch 112 (.leaf 350257211) (.leaf 343283008)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 336453258) (.leaf 329764711)) (.branch 116 (.leaf 323214200) (.leaf 316798641))) (.branch 119 (.branch 118 (.leaf 310515029) (.leaf 304360439)) (.branch 120 (.leaf 298332018) (.leaf 292426988)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 235).prefactor = (4779330772261187/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 235).cutoff/(generalMeanRows 235).c)).2 =
    (16166723091041/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 235).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 235).q*(generalMeanRows 235).c/2-2 = (193/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable071.value]
  have hcontinuation : (generalMeanRows 235).q*(generalMeanRows 235).cutoff/2-2 = (536/249:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable118.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 235).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 235).criticalRate j.val*(generalMeanRows 235).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 235).c*(generalMeanRows 235).criticalPoint j.val)).2-
      (generalMeanRows 235).J/2-(generalMeanRows 235).error (generalMeanGrid j.val)+
      (generalMeanRows 235).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 235).c)).2-
      (generalMeanRows 235).J/2-(generalMeanRows 235).error 4 := by
  have he : (generalMeanRows 235).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 235) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 235)
    (generalMeanRows_prefactorDomain 235) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0235

/-! Kernel-checked entropy margins for general spectral rectangle 236. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0236
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5207057093) (.branch 2 (.leaf 5035789092) (.leaf 4872228505))) (.branch 5 (.branch 4 (.leaf 4715928449) (.leaf 4566473888)) (.branch 6 (.leaf 4423478847) (.leaf 4286583935)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4155454121) (.leaf 4029776747)) (.branch 10 (.leaf 3909259720) (.leaf 3793629904))) (.branch 13 (.branch 12 (.leaf 3682631644) (.leaf 3576025440)) (.branch 14 (.leaf 3473586738) (.leaf 3375104828))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3280381840) (.branch 17 (.leaf 3189231828) (.leaf 3101479927))) (.branch 20 (.branch 19 (.leaf 3016961582) (.leaf 2935521844)) (.branch 21 (.leaf 2857014713) (.leaf 2781302544)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2708255488) (.leaf 2637750989)) (.branch 25 (.leaf 2569673303) (.leaf 2503913067))) (.branch 28 (.branch 27 (.leaf 2440366895) (.leaf 2378936995)) (.branch 29 (.leaf 2319530829) (.leaf 2262060786)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2206443878) (.branch 32 (.leaf 2152601464) (.leaf 2100458986))) (.branch 35 (.branch 34 (.leaf 2049945727) (.leaf 2000994582)) (.branch 36 (.leaf 1953541849) (.leaf 1907527030)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1862892643) (.leaf 1819584052)) (.branch 40 (.leaf 1777549305) (.leaf 1736738979))) (.branch 43 (.branch 42 (.leaf 1697106042) (.leaf 1658605718)) (.branch 44 (.leaf 1621195360) (.leaf 1584834336))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1549483915) (.branch 47 (.leaf 1515107170) (.leaf 1481668872))) (.branch 50 (.branch 49 (.leaf 1449135406) (.leaf 1417474683)) (.branch 51 (.leaf 1386656056) (.leaf 1356650248)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1327429280) (.leaf 1298966399)) (.branch 55 (.leaf 1271236022) (.leaf 1244213667))) (.branch 58 (.branch 57 (.leaf 1217875906) (.leaf 1192200305)) (.branch 59 (.leaf 1167165375) (.leaf 1142750525))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1118936021) (.branch 62 (.leaf 1095702937) (.leaf 1073033119))) (.branch 65 (.branch 64 (.leaf 1050909146) (.leaf 1029314297)) (.branch 66 (.leaf 1008232512) (.leaf 987648366)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 967547034) (.leaf 947914265)) (.branch 70 (.leaf 928736355) (.leaf 910000120))) (.branch 73 (.branch 72 (.leaf 891692872) (.leaf 873802397)) (.branch 74 (.leaf 856316935) (.leaf 839225153))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 822516133) (.branch 77 (.leaf 806179348) (.leaf 790204647))) (.branch 80 (.branch 79 (.leaf 774582239) (.leaf 759302675)) (.branch 81 (.leaf 744356834) (.leaf 729735907)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 715431389) (.leaf 701435058)) (.branch 85 (.leaf 687738970) (.leaf 674335443))) (.branch 88 (.branch 87 (.leaf 661217048) (.leaf 648376596)) (.branch 89 (.leaf 635807133) (.leaf 623501925)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 611454451) (.branch 92 (.leaf 599658396) (.leaf 588107641))) (.branch 95 (.branch 94 (.leaf 576796256) (.leaf 565718490)) (.branch 96 (.leaf 554868769) (.leaf 544241685)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 533831991) (.leaf 523634594)) (.branch 100 (.leaf 513644551) (.leaf 503857061))) (.branch 103 (.branch 102 (.leaf 494267463) (.leaf 484871227)) (.branch 104 (.leaf 475663951) (.leaf 466641358))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 457799288) (.leaf 449133697)) (.branch 108 (.leaf 440640650) (.leaf 432316320))) (.branch 111 (.branch 110 (.leaf 424156983) (.leaf 416159013)) (.branch 112 (.leaf 408318883) (.leaf 400633154)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 393098482) (.leaf 385711605)) (.branch 116 (.leaf 378469348) (.leaf 371368616))) (.branch 119 (.branch 118 (.leaf 364406392) (.leaf 357579734)) (.branch 120 (.leaf 350885777) (.leaf 344321723)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 236).prefactor = (2358061627831251/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 236).cutoff/(generalMeanRows 236).c)).2 =
    (25885149660141/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 236).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 236).q*(generalMeanRows 236).c/2-2 = (91/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable102.value]
  have hcontinuation : (generalMeanRows 236).q*(generalMeanRows 236).cutoff/2-2 = (1066/501:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable119.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 236).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 236).criticalRate j.val*(generalMeanRows 236).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 236).c*(generalMeanRows 236).criticalPoint j.val)).2-
      (generalMeanRows 236).J/2-(generalMeanRows 236).error (generalMeanGrid j.val)+
      (generalMeanRows 236).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 236).c)).2-
      (generalMeanRows 236).J/2-(generalMeanRows 236).error 4 := by
  have he : (generalMeanRows 236).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 236) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 236)
    (generalMeanRows_prefactorDomain 236) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0236

/-! Kernel-checked entropy margins for general spectral rectangle 237. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0237
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5064237882) (.branch 2 (.leaf 4892571971) (.leaf 4728684176))) (.branch 5 (.branch 4 (.leaf 4572124418) (.leaf 4422474634)) (.branch 6 (.leaf 4279345981) (.leaf 4142376343)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4011228100) (.leaf 3885586124)) (.branch 10 (.leaf 3765155970) (.leaf 3649662255))) (.branch 13 (.branch 12 (.leaf 3538847176) (.leaf 3432469180)) (.branch 14 (.leaf 3330301743) (.leaf 3232132271))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3137761084) (.branch 17 (.leaf 3047000497) (.leaf 2959673977))) (.branch 20 (.branch 19 (.leaf 2875615366) (.leaf 2794668167)) (.branch 21 (.leaf 2716684899) (.leaf 2641526482)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2569061692) (.leaf 2499166642)) (.branch 25 (.leaf 2431724308) (.leaf 2366624093))) (.branch 28 (.branch 27 (.leaf 2303761416) (.leaf 2243037338)) (.branch 29 (.leaf 2184358210) (.leaf 2127635347)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2072784728) (.branch 32 (.leaf 2019726711) (.leaf 1968385772))) (.branch 35 (.branch 34 (.leaf 1918690261) (.leaf 1870572172)) (.branch 36 (.leaf 1823966933) (.leaf 1778813201)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1735052684) (.leaf 1692629958)) (.branch 40 (.leaf 1651492311) (.leaf 1611589588))) (.branch 43 (.branch 42 (.leaf 1572874047) (.leaf 1535300224)) (.branch 44 (.leaf 1498824813) (.leaf 1463406541))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1429006059) (.branch 47 (.leaf 1395585841) (.leaf 1363110085))) (.branch 50 (.branch 49 (.leaf 1331544616) (.leaf 1300856808)) (.branch 51 (.leaf 1271015495) (.leaf 1241990900)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1213754557) (.leaf 1186279250)) (.branch 55 (.leaf 1159538942) (.leaf 1133508721))) (.branch 58 (.branch 57 (.leaf 1108164736) (.leaf 1083484151)) (.branch 59 (.leaf 1059445088) (.leaf 1036026583))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1013208536) (.branch 62 (.leaf 990971677) (.leaf 969297515))) (.branch 65 (.branch 64 (.leaf 948168309) (.leaf 927567026)) (.branch 66 (.leaf 907477310) (.leaf 887883446)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 868770337) (.leaf 850123466)) (.branch 70 (.leaf 831928875) (.leaf 814173135))) (.branch 73 (.branch 72 (.leaf 796843328) (.leaf 779927013)) (.branch 74 (.leaf 763412216) (.leaf 747287398))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 731541445) (.branch 77 (.leaf 716163641) (.leaf 701143657))) (.branch 80 (.branch 79 (.leaf 686471529) (.leaf 672137643)) (.branch 81 (.leaf 658132723) (.leaf 644447812)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 631074261) (.leaf 618003715)) (.branch 85 (.leaf 605228101) (.leaf 592739615))) (.branch 88 (.branch 87 (.leaf 580530714) (.leaf 568594100)) (.branch 89 (.leaf 556922715) (.leaf 545509727)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 534348525) (.branch 92 (.leaf 523432707) (.leaf 512756072))) (.branch 95 (.branch 94 (.leaf 502312615) (.leaf 492096513)) (.branch 96 (.leaf 482102127) (.leaf 472323986)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 462756785) (.leaf 453395380)) (.branch 100 (.leaf 444234779) (.leaf 435270135))) (.branch 103 (.branch 102 (.leaf 426496747) (.leaf 417910048)) (.branch 104 (.leaf 409505603) (.leaf 401279103))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 393226364) (.leaf 385343317)) (.branch 108 (.leaf 377626009) (.leaf 370070594))) (.branch 111 (.branch 110 (.leaf 362673336) (.leaf 355430597)) (.branch 112 (.leaf 348338840) (.leaf 341394624)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 334594599) (.leaf 327935504)) (.branch 116 (.leaf 321414165) (.leaf 315027491))) (.branch 119 (.branch 118 (.leaf 308772472) (.leaf 302646174)) (.branch 120 (.leaf 296645742) (.leaf 290768391)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 237).prefactor = (474890508849231/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 237).cutoff/(generalMeanRows 237).c)).2 =
    (398162053215813/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 237).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 237).q*(generalMeanRows 237).c/2-2 = (193/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable071.value]
  have hcontinuation : (generalMeanRows 237).q*(generalMeanRows 237).cutoff/2-2 = (1066/501:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable119.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 237).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 237).criticalRate j.val*(generalMeanRows 237).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 237).c*(generalMeanRows 237).criticalPoint j.val)).2-
      (generalMeanRows 237).J/2-(generalMeanRows 237).error (generalMeanGrid j.val)+
      (generalMeanRows 237).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 237).c)).2-
      (generalMeanRows 237).J/2-(generalMeanRows 237).error 4 := by
  have he : (generalMeanRows 237).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 237) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 237)
    (generalMeanRows_prefactorDomain 237) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0237

/-! Kernel-checked entropy margins for general spectral rectangle 238. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0238
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5016550955) (.branch 2 (.leaf 4844097113) (.leaf 4679454429))) (.branch 5 (.branch 4 (.leaf 4522173461) (.leaf 4371836619)) (.branch 6 (.leaf 4228055379) (.leaf 4090467812)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3958736357) (.leaf 3832545835)) (.branch 10 (.leaf 3711601652) (.leaf 3595628184))) (.branch 13 (.branch 12 (.leaf 3484367307) (.leaf 3377577075)) (.branch 14 (.leaf 3275030510) (.leaf 3176514505))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3081828821) (.branch 17 (.leaf 2990785173) (.leaf 2903206386))) (.branch 20 (.branch 19 (.leaf 2818925632) (.leaf 2737785720)) (.branch 21 (.leaf 2659638447) (.leaf 2584344000)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2511770401) (.leaf 2441793004)) (.branch 25 (.leaf 2374294015) (.leaf 2309162063))) (.branch 28 (.branch 27 (.leaf 2246291790) (.leaf 2185583480)) (.branch 29 (.leaf 2126942709) (.leaf 2070280023)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2015510632) (.branch 32 (.leaf 1962554138) (.leaf 1911334264))) (.branch 35 (.branch 34 (.leaf 1861778620) (.leaf 1813818469)) (.branch 36 (.leaf 1767388518) (.leaf 1722426717)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1678874078) (.leaf 1636674496)) (.branch 40 (.leaf 1595774591) (.leaf 1556123552))) (.branch 43 (.branch 42 (.leaf 1517673000) (.leaf 1480376845)) (.branch 44 (.leaf 1444191171) (.leaf 1409074110))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1374985735) (.branch 47 (.leaf 1341887954) (.leaf 1309744416))) (.branch 50 (.branch 49 (.leaf 1278520414) (.leaf 1248182801)) (.branch 51 (.leaf 1218699909) (.leaf 1190041470)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1162178547) (.leaf 1135083462)) (.branch 55 (.leaf 1108729734) (.leaf 1083092020))) (.branch 58 (.branch 57 (.leaf 1058146053) (.leaf 1033868592)) (.branch 59 (.leaf 1010237371) (.leaf 987231049))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 964829164) (.branch 62 (.leaf 943012093) (.leaf 921761009))) (.branch 65 (.branch 64 (.leaf 901057843) (.leaf 880885249)) (.branch 66 (.leaf 861226569) (.leaf 842065797)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 823387554) (.leaf 805177056)) (.branch 70 (.leaf 787420084) (.leaf 770102964))) (.branch 73 (.branch 72 (.leaf 753212534) (.leaf 736736129)) (.branch 74 (.leaf 720661553) (.leaf 704977057))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 689671325) (.branch 77 (.leaf 674733449) (.leaf 660152914))) (.branch 80 (.branch 79 (.leaf 645919580) (.leaf 632023665)) (.branch 81 (.leaf 618455731) (.leaf 605206667)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 592267678) (.leaf 579630269)) (.branch 85 (.leaf 567286235) (.leaf 555227645))) (.branch 88 (.branch 87 (.leaf 543446834) (.leaf 531936391)) (.branch 89 (.leaf 520689150) (.leaf 509698176)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 498956760) (.branch 92 (.leaf 488458408) (.leaf 478196833))) (.branch 95 (.branch 94 (.leaf 468165945) (.leaf 458359848)) (.branch 96 (.leaf 448772827) (.leaf 439399343)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 430234028) (.leaf 421271677)) (.branch 100 (.leaf 412507241) (.leaf 403935822))) (.branch 103 (.branch 102 (.leaf 395552670) (.leaf 387353171)) (.branch 104 (.leaf 379332850) (.leaf 371487359))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 363812478) (.leaf 356304106)) (.branch 108 (.leaf 348958260) (.leaf 341771067))) (.branch 111 (.branch 110 (.leaf 334738766) (.leaf 327857699)) (.branch 112 (.leaf 321124309) (.leaf 314535138)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 308086821) (.leaf 301776085)) (.branch 116 (.leaf 295599746) (.leaf 289554703))) (.branch 119 (.branch 118 (.leaf 283637940) (.leaf 277846520)) (.branch 120 (.leaf 272177583) (.leaf 266628344)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 238).prefactor = (2375411252596741/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 238).cutoff/(generalMeanRows 238).c)).2 =
    (96071676680549/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 238).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 238).q*(generalMeanRows 238).c/2-2 = (397/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable105.value]
  have hcontinuation : (generalMeanRows 238).q*(generalMeanRows 238).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable030.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 238).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 238).criticalRate j.val*(generalMeanRows 238).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 238).c*(generalMeanRows 238).criticalPoint j.val)).2-
      (generalMeanRows 238).J/2-(generalMeanRows 238).error (generalMeanGrid j.val)+
      (generalMeanRows 238).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 238).c)).2-
      (generalMeanRows 238).J/2-(generalMeanRows 238).error 4 := by
  have he : (generalMeanRows 238).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 238) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 238)
    (generalMeanRows_prefactorDomain 238) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0238

/-! Kernel-checked entropy margins for general spectral rectangle 239. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0239
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4966670214) (.branch 2 (.leaf 4793492560) (.leaf 4628188607))) (.branch 5 (.branch 4 (.leaf 4470305613) (.leaf 4319422891)) (.branch 6 (.leaf 4175149012) (.leaf 4037119313)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3904993660) (.leaf 3778454447)) (.branch 10 (.leaf 3657204791) (.leaf 3540966900))) (.branch 13 (.branch 12 (.leaf 3429480603) (.leaf 3322502016)) (.branch 14 (.leaf 3219802321) (.leaf 3121166666))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3026393158) (.branch 17 (.leaf 2935291935) (.leaf 2847684327))) (.branch 20 (.branch 19 (.leaf 2763402081) (.leaf 2682286648)) (.branch 21 (.leaf 2604188534) (.leaf 2528966693)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2456487972) (.leaf 2386626601)) (.branch 25 (.leaf 2319263716) (.leaf 2254286921))) (.branch 28 (.branch 27 (.leaf 2191589882) (.leaf 2131071946)) (.branch 29 (.leaf 2072637794) (.leaf 2016197116)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1961664305) (.branch 32 (.leaf 1908958175) (.leaf 1858001702))) (.branch 35 (.branch 34 (.leaf 1808721775) (.leaf 1761048966)) (.branch 36 (.leaf 1714917324) (.leaf 1670264165)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1627029894) (.leaf 1585157825)) (.branch 40 (.leaf 1544594020) (.leaf 1505287134))) (.branch 43 (.branch 42 (.leaf 1467188272) (.leaf 1430250856)) (.branch 44 (.leaf 1394430495) (.leaf 1359684869))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1325973618) (.branch 47 (.leaf 1293258233) (.leaf 1261501962))) (.branch 50 (.branch 49 (.leaf 1230669715) (.leaf 1200727979)) (.branch 51 (.leaf 1171644731) (.leaf 1143389367)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1115932623) (.leaf 1089246512)) (.branch 55 (.leaf 1063304254) (.leaf 1038080219))) (.branch 58 (.branch 57 (.leaf 1013549867) (.leaf 989689695)) (.branch 59 (.leaf 966477183) (.leaf 943890749))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 921909702) (.branch 62 (.leaf 900514196) (.leaf 879685192))) (.branch 65 (.branch 64 (.leaf 859404419) (.leaf 839654336)) (.branch 66 (.leaf 820418100) (.leaf 801679527)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 783423068) (.leaf 765633777)) (.branch 70 (.leaf 748297281) (.leaf 731399756))) (.branch 73 (.branch 72 (.leaf 714927901) (.leaf 698868915)) (.branch 74 (.leaf 683210472) (.leaf 667940703))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 653048175) (.branch 77 (.leaf 638521869) (.leaf 624351163))) (.branch 80 (.branch 79 (.leaf 610525818) (.leaf 597035957)) (.branch 81 (.leaf 583872049) (.leaf 571024901)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 558485634) (.leaf 546245677)) (.branch 85 (.leaf 534296752) (.leaf 522630859))) (.branch 88 (.branch 87 (.leaf 511240268) (.leaf 500117509)) (.branch 89 (.leaf 489255356) (.leaf 478646822)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 468285146) (.branch 92 (.leaf 458163787) (.leaf 448276414))) (.branch 95 (.branch 94 (.leaf 438616897) (.leaf 429179300)) (.branch 96 (.leaf 419957872) (.leaf 410947043)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 402141413) (.leaf 393535750)) (.branch 100 (.leaf 385124980) (.leaf 376904182))) (.branch 103 (.branch 102 (.leaf 368868584) (.leaf 361013555)) (.branch 104 (.leaf 353334601) (.leaf 345827362))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 338487603) (.leaf 331311213)) (.branch 108 (.leaf 324294199) (.leaf 317432682))) (.branch 111 (.branch 110 (.leaf 310722893) (.leaf 304161172)) (.branch 112 (.leaf 297743957) (.leaf 291467789)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 285329303) (.leaf 279325228)) (.branch 116 (.leaf 273452382) (.leaf 267707668))) (.branch 119 (.branch 118 (.leaf 262088074) (.leaf 256590669)) (.branch 120 (.leaf 251212600) (.leaf 245951091)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 239).prefactor = (4784385722914539/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 239).cutoff/(generalMeanRows 239).c)).2 =
    (37644352926117/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 239).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 239).q*(generalMeanRows 239).c/2-2 = (102/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable107.value]
  have hcontinuation : (generalMeanRows 239).q*(generalMeanRows 239).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable030.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 239).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 239).criticalRate j.val*(generalMeanRows 239).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 239).c*(generalMeanRows 239).criticalPoint j.val)).2-
      (generalMeanRows 239).J/2-(generalMeanRows 239).error (generalMeanGrid j.val)+
      (generalMeanRows 239).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 239).c)).2-
      (generalMeanRows 239).J/2-(generalMeanRows 239).error 4 := by
  have he : (generalMeanRows 239).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 239) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 239)
    (generalMeanRows_prefactorDomain 239) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0239

/-! Kernel-checked entropy margins for general spectral rectangle 240. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0240
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5012360190) (.branch 2 (.leaf 4839955966) (.leaf 4675391831))) (.branch 5 (.branch 4 (.leaf 4518214488) (.leaf 4368002856)) (.branch 6 (.leaf 4224365256) (.leaf 4086936907)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3955377679) (.leaf 3829370073)) (.branch 10 (.leaf 3708617410) (.leaf 3592842192))) (.branch 13 (.branch 12 (.leaf 3481784616) (.leaf 3375201231)) (.branch 14 (.leaf 3272863718) (.leaf 3174557775))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3080082101) (.branch 17 (.leaf 2989247471) (.leaf 2901875885))) (.branch 20 (.branch 19 (.leaf 2817799787) (.leaf 2736861352)) (.branch 21 (.leaf 2658911828) (.leaf 2583810927)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2511426267) (.leaf 2441632860)) (.branch 25 (.leaf 2374312625) (.leaf 2309353959))) (.branch 28 (.branch 27 (.leaf 2246651315) (.leaf 2186104832)) (.branch 29 (.leaf 2127619977) (.leaf 2071107220)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2016481730) (.branch 32 (.leaf 1963663088) (.leaf 1912575025))) (.branch 35 (.branch 34 (.leaf 1863145180) (.leaf 1815304861)) (.branch 36 (.leaf 1768988839) (.leaf 1724135144)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1680684877) (.leaf 1638582035)) (.branch 40 (.leaf 1597773350) (.leaf 1558208132))) (.branch 43 (.branch 42 (.leaf 1519838125) (.leaf 1482617374)) (.branch 44 (.leaf 1446502099) (.leaf 1411450571))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1377423006) (.branch 47 (.leaf 1344381460) (.leaf 1312289725))) (.branch 50 (.branch 49 (.leaf 1281113241) (.leaf 1250819011)) (.branch 51 (.leaf 1221375511) (.leaf 1192752620)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1164921546) (.leaf 1137854753)) (.branch 55 (.leaf 1111525904) (.leaf 1085909792))) (.branch 58 (.branch 57 (.leaf 1060982289) (.leaf 1036720287)) (.branch 59 (.leaf 1013101653) (.leaf 990105172))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 967710511) (.branch 62 (.leaf 945898167) (.leaf 924649435))) (.branch 65 (.branch 64 (.leaf 903946361) (.leaf 883771711)) (.branch 66 (.leaf 864108937) (.leaf 844942140)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 826256045) (.leaf 808035966)) (.branch 70 (.leaf 790267782) (.leaf 772937911))) (.branch 73 (.branch 72 (.leaf 756033283) (.leaf 739541318)) (.branch 74 (.leaf 723449902) (.leaf 707747371))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 692422484) (.branch 77 (.leaf 677464408) (.leaf 662862700))) (.branch 80 (.branch 79 (.leaf 648607289) (.leaf 634688458)) (.branch 81 (.leaf 621096833) (.leaf 607823364)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 594859315) (.leaf 582196245)) (.branch 85 (.leaf 569826002) (.leaf 557740707))) (.branch 88 (.branch 87 (.leaf 545932743) (.leaf 534394746)) (.branch 89 (.leaf 523119593) (.leaf 512100391)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 501330473) (.branch 92 (.leaf 490803381) (.leaf 480512865))) (.branch 95 (.branch 94 (.leaf 470452870) (.leaf 460617532)) (.branch 96 (.leaf 451001166) (.leaf 441598264)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 432403485) (.leaf 423411651)) (.branch 100 (.leaf 414617736) (.leaf 406016868))) (.branch 103 (.branch 102 (.leaf 397604316) (.leaf 389375490)) (.branch 104 (.leaf 381325932) (.leaf 373451315))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 365747433) (.leaf 358210204)) (.branch 108 (.leaf 350835657) (.leaf 343619937))) (.branch 111 (.branch 110 (.leaf 336559294) (.leaf 329650083)) (.branch 112 (.leaf 322888758) (.leaf 316271870)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 309796067) (.leaf 303458083)) (.branch 116 (.leaf 297254742) (.leaf 291182952))) (.branch 119 (.branch 118 (.leaf 285239703) (.leaf 279422065)) (.branch 120 (.leaf 273727183) (.leaf 268152278)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 240).prefactor = (2390957394129869/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 240).cutoff/(generalMeanRows 240).c)).2 =
    (3902568737087/10000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 240).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 240).q*(generalMeanRows 240).c/2-2 = (397/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable105.value]
  have hcontinuation : (generalMeanRows 240).q*(generalMeanRows 240).cutoff/2-2 = (1066/501:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable119.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 240).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 240).criticalRate j.val*(generalMeanRows 240).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 240).c*(generalMeanRows 240).criticalPoint j.val)).2-
      (generalMeanRows 240).J/2-(generalMeanRows 240).error (generalMeanGrid j.val)+
      (generalMeanRows 240).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 240).c)).2-
      (generalMeanRows 240).J/2-(generalMeanRows 240).error 4 := by
  have he : (generalMeanRows 240).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 240) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 240)
    (generalMeanRows_prefactorDomain 240) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0240

/-! Kernel-checked entropy margins for general spectral rectangle 241. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0241
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5079631829) (.branch 2 (.leaf 4907413451) (.leaf 4743013640))) (.branch 5 (.branch 4 (.leaf 4585978864) (.leaf 4435887903)) (.branch 6 (.leaf 4292349022) (.leaf 4154997460)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4023493174) (.leaf 3897518816)) (.branch 10 (.leaf 3776777914) (.leaf 3660993222))) (.branch 13 (.branch 12 (.leaf 3549905237) (.leaf 3443270843)) (.branch 14 (.leaf 3340862092) (.leaf 3242465082))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3147878938) (.branch 17 (.leaf 3056914882) (.leaf 2969395381))) (.branch 20 (.branch 19 (.leaf 2885153360) (.leaf 2804031491)) (.branch 21 (.leaf 2725881524) (.leaf 2650563688)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2577946119) (.leaf 2507904352)) (.branch 25 (.leaf 2440320834) (.leaf 2375084486))) (.branch 28 (.branch 27 (.leaf 2312090289) (.leaf 2251238906)) (.branch 29 (.leaf 2192436324) (.leaf 2135593532)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2080626208) (.branch 32 (.leaf 2027454441) (.leaf 1976002463))) (.branch 35 (.branch 34 (.leaf 1926198402) (.leaf 1877974053)) (.branch 36 (.leaf 1831264664) (.leaf 1786008729)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1742147811) (.leaf 1699626356)) (.branch 40 (.leaf 1658391534) (.leaf 1618393085))) (.branch 43 (.branch 42 (.leaf 1579583174) (.leaf 1541916256)) (.branch 44 (.leaf 1505348948) (.leaf 1469839912))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1435349743) (.branch 47 (.leaf 1401840864) (.leaf 1369277427))) (.branch 50 (.branch 49 (.leaf 1337625221) (.leaf 1306851583)) (.branch 51 (.leaf 1276925321) (.leaf 1247816629)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1219497023) (.leaf 1191939268)) (.branch 55 (.leaf 1165117311) (.leaf 1139006227))) (.branch 58 (.branch 57 (.leaf 1113582157) (.leaf 1088822254)) (.branch 59 (.leaf 1064704634) (.leaf 1041208327))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1018313232) (.branch 62 (.leaf 996000073) (.leaf 974250360))) (.branch 65 (.branch 64 (.leaf 953046349) (.leaf 932371008)) (.branch 66 (.leaf 912207980) (.leaf 892541553)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 873356628) (.leaf 854638692)) (.branch 70 (.leaf 836373787) (.leaf 818548487))) (.branch 73 (.branch 72 (.leaf 801149873) (.leaf 784165509)) (.branch 74 (.leaf 767583419) (.leaf 751392068))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 735580342) (.branch 77 (.leaf 720137528) (.leaf 705053295))) (.branch 80 (.branch 79 (.leaf 690317682) (.leaf 675921074)) (.branch 81 (.leaf 661854196) (.leaf 648108091)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 634674108) (.leaf 621543894)) (.branch 85 (.leaf 608709373) (.leaf 596162742))) (.branch 88 (.branch 87 (.leaf 583896453) (.leaf 571903209)) (.branch 89 (.leaf 560175948) (.leaf 548707838)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 537492263) (.branch 92 (.leaf 526522819) (.leaf 515793302))) (.branch 95 (.branch 94 (.leaf 505297702) (.leaf 495030196)) (.branch 96 (.leaf 484985136) (.leaf 475157050)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 465540628) (.leaf 456130721)) (.branch 100 (.leaf 446922331) (.leaf 437910609))) (.branch 103 (.branch 102 (.leaf 429090845) (.leaf 420458469)) (.branch 104 (.leaf 412009039) (.leaf 403738242))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 395641886) (.leaf 387715897)) (.branch 108 (.leaf 379956316) (.leaf 372359290))) (.branch 111 (.branch 110 (.leaf 364921076) (.leaf 357638031)) (.branch 112 (.leaf 350506610) (.leaf 343523366)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 336684941) (.leaf 329988069)) (.branch 116 (.leaf 323429568) (.leaf 317006339))) (.branch 119 (.branch 118 (.leaf 310715366) (.leaf 304553708)) (.branch 120 (.leaf 298518502) (.leaf 292606957)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 241).prefactor = (119515925237469/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 241).cutoff/(generalMeanRows 241).c)).2 =
    (401160556212071/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 241).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 241).q*(generalMeanRows 241).c/2-2 = (193/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable071.value]
  have hcontinuation : (generalMeanRows 241).q*(generalMeanRows 241).cutoff/2-2 = (2138/999:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable120.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 241).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 241).criticalRate j.val*(generalMeanRows 241).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 241).c*(generalMeanRows 241).criticalPoint j.val)).2-
      (generalMeanRows 241).J/2-(generalMeanRows 241).error (generalMeanGrid j.val)+
      (generalMeanRows 241).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 241).c)).2-
      (generalMeanRows 241).J/2-(generalMeanRows 241).error 4 := by
  have he : (generalMeanRows 241).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 241) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 241)
    (generalMeanRows_prefactorDomain 241) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0241

/-! Kernel-checked entropy margins for general spectral rectangle 242. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0242
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5009841042) (.branch 2 (.leaf 4837483998) (.leaf 4672980382))) (.branch 5 (.branch 4 (.leaf 4515875016) (.leaf 4365745120)) (.branch 6 (.leaf 4222197483) (.leaf 4084865941)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3953409120) (.leaf 3827508403)) (.branch 10 (.leaf 3706866108) (.leaf 3591203838))) (.branch 13 (.branch 12 (.leaf 3480260985) (.leaf 3373793383)) (.branch 14 (.leaf 3271572076) (.leaf 3173382196))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3079021944) (.branch 17 (.leaf 2988301656) (.leaf 2901042946))) (.branch 20 (.branch 19 (.leaf 2817077923) (.leaf 2736248473)) (.branch 21 (.leaf 2658405593) (.leaf 2583408784)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2511125485) (.leaf 2441430558)) (.branch 25 (.leaf 2374205804) (.leaf 2309339520))) (.branch 28 (.branch 27 (.leaf 2246726087) (.leaf 2186265589)) (.branch 29 (.leaf 2127863457) (.leaf 2071430141)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2016880803) (.branch 32 (.leaf 1964135031) (.leaf 1913116576))) (.branch 35 (.branch 34 (.leaf 1863753102) (.leaf 1815975956)) (.branch 36 (.leaf 1769719953) (.leaf 1724923173)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1681526775) (.leaf 1639474818)) (.branch 40 (.leaf 1598714099) (.leaf 1559193998))) (.branch 43 (.branch 42 (.leaf 1520866332) (.leaf 1483685220)) (.branch 44 (.leaf 1447606958) (.leaf 1412589895))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1378594328) (.branch 47 (.leaf 1345582390) (.leaf 1313517953))) (.branch 50 (.branch 49 (.leaf 1282366539) (.leaf 1252095227)) (.branch 51 (.leaf 1222672574) (.leaf 1194068538)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1166254401) (.leaf 1139202707)) (.branch 55 (.leaf 1112887191) (.leaf 1087282721))) (.branch 58 (.branch 57 (.leaf 1062365241) (.leaf 1038111714)) (.branch 59 (.leaf 1014500075) (.leaf 991509179))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 969118755) (.branch 62 (.leaf 947309368) (.leaf 926062372))) (.branch 65 (.branch 64 (.leaf 905359875) (.leaf 885184703)) (.branch 66 (.leaf 865520363) (.leaf 846351013)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 827661428) (.leaf 809436977)) (.branch 70 (.leaf 791663588) (.leaf 774327726))) (.branch 73 (.branch 72 (.leaf 757416367) (.leaf 740916978)) (.branch 74 (.leaf 724817487) (.leaf 709106271))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 693772128) (.branch 77 (.leaf 678804265) (.leaf 664192275))) (.branch 80 (.branch 79 (.leaf 649926121) (.leaf 635996122)) (.branch 81 (.leaf 622392935) (.leaf 609107541)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 596131233) (.leaf 583455600)) (.branch 85 (.leaf 571072515) (.leaf 558974127))) (.branch 88 (.branch 87 (.leaf 547152842) (.leaf 535601321)) (.branch 89 (.leaf 524312461) (.leaf 513279393)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 502495468) (.branch 92 (.leaf 491954249) (.leaf 481649503))) (.branch 95 (.branch 94 (.leaf 471575194) (.leaf 461725472)) (.branch 96 (.leaf 452094670) (.leaf 442677294)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 433468017) (.leaf 424461672)) (.branch 100 (.leaf 415653250) (.leaf 407037887))) (.branch 103 (.branch 102 (.leaf 398610864) (.leaf 390367602)) (.branch 104 (.leaf 382303654) (.leaf 374414699))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 366696542) (.leaf 359145108)) (.branch 108 (.leaf 351756436) (.leaf 344526675))) (.branch 111 (.branch 110 (.leaf 337452082) (.leaf 330529019)) (.branch 112 (.leaf 323753946) (.leaf 317123420)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 310634090) (.leaf 304282699)) (.branch 116 (.leaf 298066073) (.leaf 291981124))) (.branch 119 (.branch 118 (.leaf 286024845) (.leaf 280194310)) (.branch 120 (.leaf 274486667) (.leaf 268899137)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 242).prefactor = (2398545322121211/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 242).cutoff/(generalMeanRows 242).c)).2 =
    (196627688352479/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 242).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 242).q*(generalMeanRows 242).c/2-2 = (397/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable105.value]
  have hcontinuation : (generalMeanRows 242).q*(generalMeanRows 242).cutoff/2-2 = (2138/999:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable120.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 242).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 242).criticalRate j.val*(generalMeanRows 242).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 242).c*(generalMeanRows 242).criticalPoint j.val)).2-
      (generalMeanRows 242).J/2-(generalMeanRows 242).error (generalMeanGrid j.val)+
      (generalMeanRows 242).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 242).c)).2-
      (generalMeanRows 242).J/2-(generalMeanRows 242).error 4 := by
  have he : (generalMeanRows 242).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 242) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 242)
    (generalMeanRows_prefactorDomain 242) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0242

/-! Kernel-checked entropy margins for general spectral rectangle 243. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0243
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5029750512) (.branch 2 (.leaf 4856748134) (.leaf 4691613046))) (.branch 5 (.branch 4 (.leaf 4533890378) (.leaf 4383157588)) (.branch 6 (.leaf 4239021639) (.leaf 4101116485)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3969100813) (.leaf 3842656025)) (.branch 10 (.leaf 3721484413) (.leaf 3605307514))) (.branch 13 (.branch 12 (.leaf 3493864624) (.leaf 3386911450)) (.branch 14 (.leaf 3284218878) (.leaf 3185571864))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3090768408) (.branch 17 (.leaf 2999618629) (.leaf 2911943908))) (.branch 20 (.branch 19 (.leaf 2827576109) (.leaf 2746356859)) (.branch 21 (.leaf 2668136890) (.leaf 2592775427)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2520139630) (.leaf 2450104075)) (.branch 25 (.leaf 2382550274) (.leaf 2317366234))) (.branch 28 (.branch 27 (.leaf 2254446044) (.leaf 2193689496)) (.branch 29 (.leaf 2135001728) (.leaf 2078292902)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2023477888) (.branch 32 (.leaf 1970475992) (.leaf 1919210681))) (.branch 35 (.branch 34 (.leaf 1869609339) (.leaf 1821603039)) (.branch 36 (.leaf 1775126324) (.leaf 1730117010)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1686515992) (.leaf 1644267075)) (.branch 40 (.leaf 1603316805) (.leaf 1563614316))) (.branch 43 (.branch 42 (.leaf 1525111185) (.leaf 1487761297)) (.branch 44 (.leaf 1451520720) (.leaf 1416347581))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1382201959) (.branch 47 (.leaf 1349045775) (.leaf 1316842698))) (.branch 50 (.branch 49 (.leaf 1285558048) (.leaf 1255158712)) (.branch 51 (.leaf 1225613058) (.leaf 1196890861)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1168963227) (.leaf 1141802526)) (.branch 55 (.leaf 1115382329) (.leaf 1089677343))) (.branch 58 (.branch 57 (.leaf 1064663354) (.leaf 1040317176)) (.branch 59 (.leaf 1016616596) (.leaf 993540330))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 971067971) (.branch 62 (.leaf 949179950) (.leaf 927857495))) (.branch 65 (.branch 64 (.leaf 907082591) (.leaf 886837946)) (.branch 66 (.leaf 867106952) (.leaf 847873657)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 829122730) (.leaf 810839437)) (.branch 70 (.leaf 793009607) (.leaf 775619610))) (.branch 73 (.branch 72 (.leaf 758656331) (.leaf 742107147)) (.branch 74 (.leaf 725959903) (.leaf 710202892))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 694824835) (.branch 77 (.leaf 679814863) (.leaf 665162494))) (.branch 80 (.branch 79 (.leaf 650857624) (.leaf 636890502)) (.branch 81 (.leaf 623251721) (.leaf 609932200)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 596923172) (.leaf 584216168)) (.branch 85 (.leaf 571803006) (.leaf 559675781))) (.branch 88 (.branch 87 (.leaf 547826850) (.leaf 536248822)) (.branch 89 (.leaf 524934550) (.leaf 513877117)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 503069833) (.branch 92 (.leaf 492506217) (.leaf 482179998))) (.branch 95 (.branch 94 (.leaf 472085101) (.leaf 462215639)) (.branch 96 (.leaf 452565909) (.leaf 443130384)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 433903704) (.leaf 424880672)) (.branch 100 (.leaf 416056247) (.leaf 407425538))) (.branch 103 (.branch 102 (.leaf 398983799) (.leaf 390726423)) (.branch 104 (.leaf 382648938) (.leaf 374746999))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 367016389) (.leaf 359453009)) (.branch 108 (.leaf 352052877) (.leaf 344812123))) (.branch 111 (.branch 110 (.leaf 337726983) (.leaf 330793800)) (.branch 112 (.leaf 324009016) (.leaf 317369172)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 310870900) (.leaf 304510927)) (.branch 116 (.leaf 298286063) (.leaf 292193208))) (.branch 119 (.branch 118 (.leaf 286229339) (.leaf 280391517)) (.branch 120 (.leaf 274676876) (.leaf 269082629)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 243).prefactor = (9597011165573/2000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 243).cutoff/(generalMeanRows 243).c)).2 =
    (3902568737087/10000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 243).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 243).q*(generalMeanRows 243).c/2-2 = (397/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable105.value]
  have hcontinuation : (generalMeanRows 243).q*(generalMeanRows 243).cutoff/2-2 = (1066/501:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable119.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 243).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 243).criticalRate j.val*(generalMeanRows 243).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 243).c*(generalMeanRows 243).criticalPoint j.val)).2-
      (generalMeanRows 243).J/2-(generalMeanRows 243).error (generalMeanGrid j.val)+
      (generalMeanRows 243).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 243).c)).2-
      (generalMeanRows 243).J/2-(generalMeanRows 243).error 4 := by
  have he : (generalMeanRows 243).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 243) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 243)
    (generalMeanRows_prefactorDomain 243) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0243

/-! Kernel-checked entropy margins for general spectral rectangle 244. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0244
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4961496407) (.branch 2 (.leaf 4788386913) (.leaf 4623179446))) (.branch 5 (.branch 4 (.leaf 4465417441) (.leaf 4314676749)) (.branch 6 (.leaf 4170562816) (.leaf 4032708153)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3900770079) (.leaf 3774428693)) (.branch 10 (.leaf 3653385047) (.leaf 3537359498))) (.branch 13 (.branch 12 (.leaf 3426090212) (.leaf 3319331818)) (.branch 14 (.leaf 3216854175) (.leaf 3118441251))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3023890104) (.branch 17 (.leaf 2933009951) (.leaf 2845621304))) (.branch 20 (.branch 19 (.leaf 2761555199) (.leaf 2680652464)) (.branch 21 (.leaf 2602763064) (.leaf 2527745491)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2455466198) (.leaf 2385799081)) (.branch 25 (.leaf 2318625000) (.leaf 2253831333))) (.branch 28 (.branch 27 (.leaf 2191311565) (.leaf 2130964907)) (.branch 29 (.leaf 2072695937) (.leaf 2016414277)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1962034281) (.branch 32 (.leaf 1909474754) (.leaf 1858658682))) (.branch 35 (.branch 34 (.leaf 1809512988) (.leaf 1761968297)) (.branch 36 (.leaf 1715958725) (.leaf 1671421672)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1628297638) (.leaf 1586530042)) (.branch 40 (.leaf 1546065063) (.leaf 1506851478))) (.branch 43 (.branch 42 (.leaf 1468840523) (.leaf 1431985754)) (.branch 44 (.leaf 1396242921) (.leaf 1361569848))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1327926318) (.branch 47 (.leaf 1295273973) (.leaf 1263576208))) (.branch 50 (.branch 49 (.leaf 1232798084) (.leaf 1202906236)) (.branch 51 (.leaf 1173868791) (.leaf 1145655293)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1118236625) (.leaf 1091584944)) (.branch 55 (.leaf 1065673615) (.leaf 1040477149))) (.branch 58 (.branch 57 (.leaf 1015971143) (.leaf 992132230)) (.branch 59 (.leaf 968938025) (.leaf 946367076))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 924398817) (.branch 62 (.leaf 903013527) (.leaf 882192290))) (.branch 65 (.branch 64 (.leaf 861916950) (.leaf 842170082)) (.branch 66 (.leaf 822934951) (.leaf 804195484)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 785936235) (.leaf 768142359)) (.branch 70 (.leaf 750799580) (.leaf 733894168))) (.branch 73 (.branch 72 (.leaf 717412915) (.leaf 701343105)) (.branch 74 (.leaf 685672499) (.leaf 670389309))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 655482180) (.branch 77 (.leaf 640940168) (.leaf 626752725))) (.branch 80 (.branch 79 (.leaf 612909680) (.leaf 599401224)) (.branch 81 (.leaf 586217891) (.leaf 573350547)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 560790373) (.leaf 548528856)) (.branch 85 (.leaf 536557769) (.leaf 524869165))) (.branch 88 (.branch 87 (.leaf 513455365) (.leaf 502308942)) (.branch 89 (.leaf 491422718) (.leaf 480789746)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 470403308) (.branch 92 (.leaf 460256902) (.leaf 450344232))) (.branch 95 (.branch 94 (.leaf 440659203) (.leaf 431195913)) (.branch 96 (.leaf 421948643) (.leaf 412911852)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 404080170) (.leaf 395448389)) (.branch 100 (.leaf 387011462) (.leaf 378764492))) (.branch 103 (.branch 102 (.leaf 370702729) (.leaf 362821564)) (.branch 104 (.leaf 355116523) (.leaf 347583263))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 340217570) (.leaf 333015347)) (.branch 108 (.leaf 325972618) (.leaf 319085518))) (.branch 111 (.branch 110 (.leaf 312350292) (.leaf 305763292)) (.branch 112 (.leaf 299320969) (.leaf 293019874)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 286856654) (.leaf 280828045)) (.branch 116 (.leaf 274930874) (.leaf 269162054))) (.branch 119 (.branch 118 (.leaf 263518579) (.leaf 257997526)) (.branch 120 (.leaf 252596047) (.leaf 247311370)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 244).prefactor = (2407576969435381/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 244).cutoff/(generalMeanRows 244).c)).2 =
    (15296547849907/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 244).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 244).q*(generalMeanRows 244).c/2-2 = (102/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable107.value]
  have hcontinuation : (generalMeanRows 244).q*(generalMeanRows 244).cutoff/2-2 = (1066/501:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable119.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 244).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 244).criticalRate j.val*(generalMeanRows 244).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 244).c*(generalMeanRows 244).criticalPoint j.val)).2-
      (generalMeanRows 244).J/2-(generalMeanRows 244).error (generalMeanGrid j.val)+
      (generalMeanRows 244).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 244).c)).2-
      (generalMeanRows 244).J/2-(generalMeanRows 244).error 4 := by
  have he : (generalMeanRows 244).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 244) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 244)
    (generalMeanRows_prefactorDomain 244) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0244

/-! Kernel-checked entropy margins for general spectral rectangle 245. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0245
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5032138290) (.branch 2 (.leaf 4859098616) (.leaf 4693912314))) (.branch 5 (.branch 4 (.leaf 4536126421) (.leaf 4385320117)) (.branch 6 (.leaf 4241101925) (.leaf 4103107201)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3970995901) (.leaf 3844450568)) (.branch 10 (.leaf 3723174518) (.leaf 3606890208))) (.branch 13 (.branch 12 (.leaf 3495337758) (.leaf 3388273609)) (.branch 14 (.leaf 3285469304) (.leaf 3186710382))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3091795358) (.branch 17 (.leaf 3000534808) (.leaf 2912750514))) (.branch 20 (.branch 19 (.leaf 2828274689) (.leaf 2746949265)) (.branch 21 (.leaf 2668625238) (.leaf 2593162057)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2520427074) (.leaf 2450295027)) (.branch 25 (.leaf 2382647560) (.leaf 2317372786))) (.branch 28 (.branch 27 (.leaf 2254364881) (.leaf 2193523698)) (.branch 29 (.leaf 2134754425) (.leaf 2077967248)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2023077057) (.branch 32 (.leaf 1970003156) (.leaf 1918669001))) (.branch 35 (.branch 34 (.leaf 1869001957) (.leaf 1820933066)) (.branch 36 (.leaf 1774396835) (.leaf 1729331031)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1685676502) (.leaf 1643376995)) (.branch 40 (.leaf 1602378995) (.leaf 1562631571))) (.branch 43 (.branch 42 (.leaf 1524086232) (.leaf 1486696794)) (.branch 44 (.leaf 1450419251) (.leaf 1415211657))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1381034013) (.branch 47 (.leaf 1347848168) (.leaf 1315617711))) (.branch 50 (.branch 49 (.leaf 1284307887) (.leaf 1253885505)) (.branch 51 (.leaf 1224318857) (.leaf 1195577642)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1167632892) (.leaf 1140456903)) (.branch 55 (.leaf 1114023171) (.leaf 1088306331))) (.branch 58 (.branch 57 (.leaf 1063282100) (.leaf 1038927223)) (.branch 59 (.leaf 1015219419) (.leaf 992137335))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 969660502) (.branch 62 (.leaf 947769288) (.leaf 926444860))) (.branch 65 (.branch 64 (.leaf 905669142) (.leaf 885424784)) (.branch 66 (.leaf 865695122) (.leaf 846464150)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 827716485) (.leaf 809437340)) (.branch 70 (.leaf 791612496) (.leaf 774228275))) (.branch 73 (.branch 72 (.leaf 757271516) (.leaf 740729551)) (.branch 74 (.leaf 724590183) (.leaf 708841664))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 693472676) (.branch 77 (.leaf 678472309) (.leaf 663830048))) (.branch 80 (.branch 79 (.leaf 649535751) (.leaf 635579635)) (.branch 81 (.leaf 621952260) (.leaf 608644516)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 595647603) (.leaf 582953026)) (.branch 85 (.leaf 570552576) (.leaf 558438321))) (.branch 88 (.branch 87 (.leaf 546602594) (.leaf 535037980)) (.branch 89 (.leaf 523737310) (.leaf 512693646)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 501900276) (.branch 92 (.leaf 491350702) (.leaf 481038633))) (.branch 95 (.branch 94 (.leaf 470957975) (.leaf 461102828)) (.branch 96 (.leaf 451467471) (.leaf 442046362)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 432834128) (.leaf 423825558)) (.branch 100 (.leaf 415015598) (.leaf 406399346))) (.branch 103 (.branch 102 (.leaf 397972044) (.leaf 389729074)) (.branch 104 (.leaf 381665955) (.leaf 373778333))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 366061981) (.leaf 358512793)) (.branch 108 (.leaf 351126778) (.leaf 343900059))) (.branch 111 (.branch 110 (.leaf 336828867) (.leaf 329909537)) (.branch 112 (.leaf 323138506) (.leaf 316512308)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 310027573) (.leaf 303681020)) (.branch 116 (.leaf 297469457) (.leaf 291389779))) (.branch 119 (.branch 118 (.leaf 285438961) (.leaf 279614059)) (.branch 120 (.leaf 273912205) (.leaf 268330609)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 245).prefactor = (37368471035563/7812500000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 245).cutoff/(generalMeanRows 245).c)).2 =
    (24204208428771/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 245).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 245).q*(generalMeanRows 245).c/2-2 = (397/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable105.value]
  have hcontinuation : (generalMeanRows 245).q*(generalMeanRows 245).cutoff/2-2 = (2126/1005:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable121.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 245).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 245).criticalRate j.val*(generalMeanRows 245).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 245).c*(generalMeanRows 245).criticalPoint j.val)).2-
      (generalMeanRows 245).J/2-(generalMeanRows 245).error (generalMeanGrid j.val)+
      (generalMeanRows 245).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 245).c)).2-
      (generalMeanRows 245).J/2-(generalMeanRows 245).error 4 := by
  have he : (generalMeanRows 245).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 245) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 245)
    (generalMeanRows_prefactorDomain 245) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0245

/-! Kernel-checked entropy margins for general spectral rectangle 246. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0246
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4964223592) (.branch 2 (.leaf 4791072536) (.leaf 4625809719))) (.branch 5 (.branch 4 (.leaf 4467980473) (.leaf 4317162366)) (.branch 6 (.leaf 4172962389) (.leaf 4035014453)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3902977136) (.leaf 3776531672)) (.branch 10 (.leaf 3655380131) (.leaf 3539243784))) (.branch 13 (.branch 12 (.leaf 3427861616) (.leaf 3320988987)) (.branch 14 (.leaf 3218396408) (.leaf 3119868425))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3025202609) (.branch 17 (.leaf 2934208629) (.leaf 2846707396))) (.branch 20 (.branch 19 (.leaf 2762530291) (.leaf 2681518447)) (.branch 21 (.leaf 2603522089) (.leaf 2528399931)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2456018618) (.leaf 2386252203)) (.branch 25 (.leaf 2318981678) (.leaf 2254094527))) (.branch 28 (.branch 27 (.leaf 2191484318) (.leaf 2131050324)) (.branch 29 (.leaf 2072697171) (.leaf 2016334506)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1961876699) (.branch 32 (.leaf 1909242553) (.leaf 1858355045))) (.branch 35 (.branch 34 (.leaf 1809141075) (.leaf 1761531240)) (.branch 36 (.leaf 1715459615) (.leaf 1670863556)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1627683510) (.leaf 1585862842)) (.branch 40 (.leaf 1545347668) (.leaf 1506086700))) (.branch 43 (.branch 42 (.leaf 1468031106) (.leaf 1431134373)) (.branch 44 (.leaf 1395352176) (.leaf 1360642266))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1326964351) (.branch 47 (.leaf 1294279995) (.leaf 1262552518))) (.branch 50 (.branch 49 (.leaf 1231746904) (.leaf 1201829710)) (.branch 51 (.leaf 1172768988) (.leaf 1144534205)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1117096170) (.leaf 1090426966)) (.branch 55 (.leaf 1064499884) (.leaf 1039289362))) (.branch 58 (.branch 57 (.leaf 1014770930) (.leaf 990921149)) (.branch 59 (.leaf 967717567) (.leaf 945138665))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 923163814) (.branch 62 (.leaf 901773229) (.leaf 880947933))) (.branch 65 (.branch 64 (.leaf 860669711) (.leaf 840921078)) (.branch 66 (.leaf 821685246) (.leaf 802946085)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 784688097) (.leaf 766896386)) (.branch 70 (.leaf 749556627) (.leaf 732655043))) (.branch 73 (.branch 72 (.leaf 716178377) (.leaf 700113873)) (.branch 74 (.leaf 684449246) (.leaf 669172669))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 654272745) (.branch 77 (.leaf 639738493) (.leaf 625559330))) (.branch 80 (.branch 79 (.leaf 611725049) (.leaf 598225806)) (.branch 81 (.leaf 585052103) (.leaf 572194777)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 559644978) (.leaf 547394164)) (.branch 85 (.leaf 535434082) (.leaf 523756760))) (.branch 88 (.branch 87 (.leaf 512354491) (.leaf 501219828)) (.branch 89 (.leaf 490345568) (.leaf 479724745)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 469350618) (.branch 92 (.leaf 459216667) (.leaf 449316577))) (.branch 95 (.branch 94 (.leaf 439644236) (.leaf 430193724)) (.branch 96 (.leaf 420959308) (.leaf 411935431)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 403116709) (.leaf 394497921)) (.branch 100 (.leaf 386074006) (.leaf 377840057))) (.branch 103 (.branch 102 (.leaf 369791310) (.leaf 361923148)) (.branch 104 (.leaf 354231085) (.leaf 346710771))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 339357980) (.leaf 332168609)) (.branch 108 (.leaf 325138673) (.leaf 318264301))) (.branch 111 (.branch 110 (.leaf 311541730) (.leaf 304967305)) (.branch 112 (.leaf 298537473) (.leaf 292248779)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 286097863) (.leaf 280081458)) (.branch 116 (.leaf 274196387) (.leaf 268439557))) (.branch 119 (.branch 118 (.leaf 262807961) (.leaf 257298670)) (.branch 120 (.leaf 251908835) (.leaf 246635681)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 246).prefactor = (4799894002295253/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 246).cutoff/(generalMeanRows 246).c)).2 =
    (94856039349827/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 246).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 246).q*(generalMeanRows 246).c/2-2 = (102/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable107.value]
  have hcontinuation : (generalMeanRows 246).q*(generalMeanRows 246).cutoff/2-2 = (2126/1005:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable121.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 246).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 246).criticalRate j.val*(generalMeanRows 246).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 246).c*(generalMeanRows 246).criticalPoint j.val)).2-
      (generalMeanRows 246).J/2-(generalMeanRows 246).error (generalMeanGrid j.val)+
      (generalMeanRows 246).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 246).c)).2-
      (generalMeanRows 246).J/2-(generalMeanRows 246).error 4 := by
  have he : (generalMeanRows 246).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 246) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 246)
    (generalMeanRows_prefactorDomain 246) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0246

/-! Kernel-checked entropy margins for general spectral rectangle 247. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0247
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4984183397) (.branch 2 (.leaf 4810395095) (.leaf 4644508256))) (.branch 5 (.branch 4 (.leaf 4486068544) (.leaf 4334653788)) (.branch 6 (.leaf 4189871179) (.leaf 4051354768)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3918763221) (.leaf 3791777813)) (.branch 10 (.leaf 3670100613) (.leaf 3553452851))) (.branch 13 (.branch 12 (.leaf 3441573438) (.leaf 3334217629)) (.branch 14 (.leaf 3231155800) (.leaf 3132172343))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3037064650) (.branch 17 (.leaf 2945642191) (.leaf 2857725666))) (.branch 20 (.branch 19 (.leaf 2773146228) (.leaf 2691744771)) (.branch 21 (.leaf 2613371272) (.leaf 2537884188)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2465149897) (.leaf 2395042185)) (.branch 25 (.leaf 2327441769) (.leaf 2262235857))) (.branch 28 (.branch 27 (.leaf 2199317738) (.leaf 2138586407)) (.branch 29 (.leaf 2079946209) (.leaf 2023306513)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1968581411) (.branch 32 (.leaf 1915689433) (.leaf 1864553280))) (.branch 35 (.branch 34 (.leaf 1815099584) (.leaf 1767258675)) (.branch 36 (.leaf 1720964365) (.leaf 1676153753)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1632767032) (.leaf 1590747316)) (.branch 40 (.leaf 1550040477) (.leaf 1510594989))) (.branch 43 (.branch 42 (.leaf 1472361786) (.leaf 1435294123)) (.branch 44 (.leaf 1399347454) (.leaf 1364479311))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1330649189) (.branch 47 (.leaf 1297818444) (.leaf 1265950196))) (.branch 50 (.branch 49 (.leaf 1235009231) (.leaf 1204961916)) (.branch 51 (.leaf 1175776116) (.leaf 1147421120)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1119867560) (.leaf 1093087349)) (.branch 55 (.leaf 1067053615) (.leaf 1041740637))) (.branch 58 (.branch 57 (.leaf 1017123788) (.leaf 993179481)) (.branch 59 (.leaf 969885119) (.leaf 947219042))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 925160486) (.branch 62 (.leaf 903689536) (.leaf 882787086))) (.branch 65 (.branch 64 (.leaf 862434801) (.leaf 842615077)) (.branch 66 (.leaf 823311010) (.leaf 804506362)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 786185529) (.leaf 768333510)) (.branch 70 (.leaf 750935883) (.leaf 733978775))) (.branch 73 (.branch 72 (.leaf 717448838) (.leaf 701333225)) (.branch 74 (.leaf 685619569) (.leaf 670295957))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 655350916) (.branch 77 (.leaf 640773387) (.leaf 626552714))) (.branch 80 (.branch 79 (.leaf 612678619) (.leaf 599141190)) (.branch 81 (.leaf 585930865) (.leaf 573038416)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 560454934) (.leaf 548171817)) (.branch 85 (.leaf 536180758) (.leaf 524473729))) (.branch 88 (.branch 87 (.leaf 513042974) (.leaf 501880995)) (.branch 89 (.leaf 490980540) (.leaf 480334598)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 469936386) (.branch 92 (.leaf 459779338) (.leaf 449857101))) (.branch 95 (.branch 94 (.leaf 440163523) (.leaf 430692647)) (.branch 96 (.leaf 421438703) (.leaf 412396100)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 403559421) (.leaf 394923413)) (.branch 100 (.leaf 386482986) (.leaf 378233200))) (.branch 103 (.branch 102 (.leaf 370169267) (.leaf 362286540)) (.branch 104 (.leaf 354580509) (.leaf 347046798))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 339681158) (.leaf 332479463)) (.branch 108 (.leaf 325437706) (.leaf 318551994))) (.branch 111 (.branch 110 (.leaf 311818546) (.leaf 305233687)) (.branch 112 (.leaf 298793844) (.leaf 292495546)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 286335415) (.leaf 280310169)) (.branch 116 (.leaf 274416614) (.leaf 268651643))) (.branch 119 (.branch 118 (.leaf 263012233) (.leaf 257495444)) (.branch 120 (.leaf 252098411) (.leaf 246818349)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 247).prefactor = (4801256145345961/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 247).cutoff/(generalMeanRows 247).c)).2 =
    (37644352926117/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 247).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 247).q*(generalMeanRows 247).c/2-2 = (102/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable107.value]
  have hcontinuation : (generalMeanRows 247).q*(generalMeanRows 247).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable030.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 247).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 247).criticalRate j.val*(generalMeanRows 247).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 247).c*(generalMeanRows 247).criticalPoint j.val)).2-
      (generalMeanRows 247).J/2-(generalMeanRows 247).error (generalMeanGrid j.val)+
      (generalMeanRows 247).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 247).c)).2-
      (generalMeanRows 247).J/2-(generalMeanRows 247).error 4 := by
  have he : (generalMeanRows 247).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 247) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 247)
    (generalMeanRows_prefactorDomain 247) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0247

/-! Kernel-checked entropy margins for general spectral rectangle 248. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0248
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4917767735) (.branch 2 (.leaf 4743897853) (.leaf 4577964160))) (.branch 5 (.branch 4 (.leaf 4419510565) (.leaf 4268113239)) (.branch 6 (.leaf 4123377803) (.leaf 3984936821)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3852447548) (.leaf 3725589918)) (.branch 10 (.leaf 3604064722) (.leaf 3487591976))) (.branch 13 (.branch 12 (.leaf 3375909434) (.leaf 3268771243)) (.branch 14 (.leaf 3165946727) (.leaf 3067219268))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2972385295) (.branch 17 (.leaf 2881253354) (.leaf 2793643263))) (.branch 20 (.branch 19 (.leaf 2709385329) (.leaf 2628319634)) (.branch 21 (.leaf 2550295378) (.leaf 2475170272)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2402809978) (.leaf 2333087596)) (.branch 25 (.leaf 2265883182) (.leaf 2201083312))) (.branch 28 (.branch 27 (.leaf 2138580666) (.leaf 2078273654)) (.branch 29 (.leaf 2020066058) (.leaf 1963866708)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1909589178) (.branch 32 (.leaf 1857151496) (.leaf 1806475886))) (.branch 35 (.branch 34 (.leaf 1757488517) (.leaf 1710119277)) (.branch 36 (.leaf 1664301551) (.leaf 1619972028)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1577070507) (.leaf 1535539724)) (.branch 40 (.leaf 1495325186) (.leaf 1456375018))) (.branch 43 (.branch 42 (.leaf 1418639817) (.leaf 1382072515)) (.branch 44 (.leaf 1346628258) (.leaf 1312264276))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1278939780) (.branch 47 (.leaf 1246615853) (.leaf 1215255349))) (.branch 50 (.branch 49 (.leaf 1184822801) (.leaf 1155284333)) (.branch 51 (.leaf 1126607579) (.leaf 1098761603)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1071716825) (.leaf 1045444952)) (.branch 55 (.leaf 1019918915) (.leaf 995112806))) (.branch 58 (.branch 57 (.leaf 971001818) (.leaf 947562193)) (.branch 59 (.leaf 924771169) (.leaf 902606930))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 881048560) (.branch 62 (.leaf 860076003) (.leaf 839670016))) (.branch 65 (.branch 64 (.leaf 819812133) (.leaf 800484627)) (.branch 66 (.leaf 781670477) (.leaf 763353332)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 745517482) (.leaf 728147824)) (.branch 70 (.leaf 711229842) (.leaf 694749570))) (.branch 73 (.branch 72 (.leaf 678693576) (.leaf 663048931)) (.branch 74 (.leaf 647803190) (.leaf 632944371))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 618460930) (.branch 77 (.leaf 604341746) (.leaf 590576102))) (.branch 80 (.branch 79 (.leaf 577153665) (.leaf 564064469)) (.branch 81 (.leaf 551298904) (.leaf 538847697)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 526701896) (.leaf 514852861)) (.branch 85 (.leaf 503292249) (.leaf 492011999))) (.branch 88 (.branch 87 (.leaf 481004324) (.leaf 470261700)) (.branch 89 (.leaf 459776851) (.leaf 449542742)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 439552572) (.branch 92 (.leaf 429799757) (.leaf 420277930))) (.branch 95 (.branch 94 (.leaf 410980926) (.leaf 401902777)) (.branch 96 (.leaf 393037705) (.leaf 384380112)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 375924577) (.leaf 367665843)) (.branch 100 (.leaf 359598819) (.leaf 351718568))) (.branch 103 (.branch 102 (.leaf 344020301) (.leaf 336499375)) (.branch 104 (.leaf 329151287) (.leaf 321971666))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 314956271) (.leaf 308100986)) (.branch 108 (.leaf 301401813) (.leaf 294854872))) (.branch 111 (.branch 110 (.leaf 288456393) (.leaf 282202716)) (.branch 112 (.leaf 276090284) (.leaf 270115638)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 264275421) (.leaf 258566366)) (.branch 116 (.leaf 252985298) (.leaf 247529129))) (.branch 119 (.branch 118 (.leaf 242194857) (.leaf 236979561)) (.branch 120 (.leaf 231880399) (.leaf 226894607)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 248).prefactor = (4818186055278917/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 248).cutoff/(generalMeanRows 248).c)).2 =
    (73732277763823/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 248).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 248).q*(generalMeanRows 248).c/2-2 = (419/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable106.value]
  have hcontinuation : (generalMeanRows 248).q*(generalMeanRows 248).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable030.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 248).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 248).criticalRate j.val*(generalMeanRows 248).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 248).c*(generalMeanRows 248).criticalPoint j.val)).2-
      (generalMeanRows 248).J/2-(generalMeanRows 248).error (generalMeanGrid j.val)+
      (generalMeanRows 248).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 248).c)).2-
      (generalMeanRows 248).J/2-(generalMeanRows 248).error 4 := by
  have he : (generalMeanRows 248).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 248) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 248)
    (generalMeanRows_prefactorDomain 248) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0248

/-! Kernel-checked entropy margins for general spectral rectangle 249. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0249
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4897704431) (.branch 2 (.leaf 4724476540) (.leaf 4559171358))) (.branch 5 (.branch 4 (.leaf 4401332476) (.leaf 4250535819)) (.branch 6 (.leaf 4106386825) (.leaf 3968517928)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3836586309) (.leaf 3710271869)) (.branch 10 (.leaf 3589275414) (.leaf 3473317009))) (.branch 13 (.branch 12 (.leaf 3362134492) (.leaf 3255482124)) (.branch 14 (.leaf 3153129370) (.leaf 3054859775))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2960469953) (.branch 17 (.leaf 2869768656) (.leaf 2782575920))) (.branch 20 (.branch 19 (.leaf 2698722284) (.leaf 2618048076)) (.branch 21 (.leaf 2540402748) (.leaf 2465644274)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2393638586) (.leaf 2324259055)) (.branch 25 (.leaf 2257386018) (.leaf 2192906329))) (.branch 28 (.branch 27 (.leaf 2130712950) (.leaf 2070704573)) (.branch 29 (.leaf 2012785264) (.leaf 1956864135)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1902855038) (.branch 32 (.leaf 1850676281) (.leaf 1800250362))) (.branch 35 (.branch 34 (.leaf 1751503723) (.leaf 1704366518)) (.branch 36 (.leaf 1658772400) (.leaf 1614658316)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1571964322) (.leaf 1530633403)) (.branch 40 (.leaf 1490611315) (.leaf 1451846421))) (.branch 43 (.branch 42 (.leaf 1414289556) (.leaf 1377893882)) (.branch 44 (.leaf 1342614767) (.leaf 1308409665))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1275237999) (.branch 47 (.leaf 1243061059) (.leaf 1211841903))) (.branch 50 (.branch 49 (.leaf 1181545262) (.leaf 1152137451)) (.branch 51 (.leaf 1123586292) (.leaf 1095861028)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1068932255) (.leaf 1042771851)) (.branch 55 (.leaf 1017352914) (.leaf 992649693))) (.branch 58 (.branch 57 (.leaf 968637539) (.leaf 945292842)) (.branch 59 (.leaf 922592987) (.leaf 900516297))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 879041995) (.branch 62 (.leaf 858150154) (.leaf 837821659))) (.branch 65 (.branch 64 (.leaf 818038166) (.leaf 798782069)) (.branch 66 (.leaf 780036459) (.leaf 761785097)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 744012378) (.leaf 726703305)) (.branch 70 (.leaf 709843457) (.leaf 693418969))) (.branch 73 (.branch 72 (.leaf 677416496) (.leaf 661823202)) (.branch 74 (.leaf 646626726) (.leaf 631815168))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 617377064) (.branch 77 (.leaf 603301370) (.leaf 589577442))) (.branch 80 (.branch 79 (.leaf 576195017) (.leaf 563144200)) (.branch 81 (.leaf 550415445) (.leaf 537999541)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 525887599) (.leaf 514071037)) (.branch 85 (.leaf 502541565) (.leaf 491291180))) (.branch 88 (.branch 87 (.leaf 480312146) (.leaf 469596987)) (.branch 89 (.leaf 459138476) (.leaf 448929626)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 438963676) (.branch 92 (.leaf 429234089) (.leaf 419734535))) (.branch 95 (.branch 94 (.leaf 410458891) (.leaf 401401225)) (.branch 96 (.leaf 392555796) (.leaf 383917040)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 375479568) (.leaf 367238159)) (.branch 100 (.leaf 359187749) (.leaf 351323430))) (.branch 103 (.branch 102 (.leaf 343640444) (.leaf 336134175)) (.branch 104 (.leaf 328800143) (.leaf 321634004))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 314631541) (.leaf 307788659)) (.branch 108 (.leaf 301101385) (.leaf 294565857))) (.branch 111 (.branch 110 (.leaf 288178329) (.leaf 281935156)) (.branch 112 (.leaf 275832801) (.leaf 269867825)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 264036885) (.leaf 258336732)) (.branch 116 (.leaf 252764207) (.leaf 247316236))) (.branch 119 (.branch 118 (.leaf 241989832) (.leaf 236782087)) (.branch 120 (.leaf 231690173) (.leaf 226711339)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 249).prefactor = (2408341113135531/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 249).cutoff/(generalMeanRows 249).c)).2 =
    (185821008478627/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 249).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 249).q*(generalMeanRows 249).c/2-2 = (419/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable106.value]
  have hcontinuation : (generalMeanRows 249).q*(generalMeanRows 249).cutoff/2-2 = (2126/1005:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable121.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 249).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 249).criticalRate j.val*(generalMeanRows 249).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 249).c*(generalMeanRows 249).criticalPoint j.val)).2-
      (generalMeanRows 249).J/2-(generalMeanRows 249).error (generalMeanGrid j.val)+
      (generalMeanRows 249).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 249).c)).2-
      (generalMeanRows 249).J/2-(generalMeanRows 249).error 4 := by
  have he : (generalMeanRows 249).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 249) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 249)
    (generalMeanRows_prefactorDomain 249) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0249

/-! Kernel-checked entropy margins for general spectral rectangle 250. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0250
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4914834760) (.branch 2 (.leaf 4741000982) (.leaf 4575117624))) (.branch 5 (.branch 4 (.leaf 4416726682) (.leaf 4265402595)) (.branch 6 (.leaf 4120749422) (.leaf 3982398311)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3850005245) (.leaf 3723249004)) (.branch 10 (.leaf 3601829350) (.leaf 3485465366))) (.branch 13 (.branch 12 (.leaf 3373893974) (.leaf 3266868577)) (.branch 14 (.leaf 3164157830) (.leaf 3065544525))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2970824564) (.branch 17 (.leaf 2879806028) (.leaf 2792308324))) (.branch 20 (.branch 19 (.leaf 2708161400) (.leaf 2627205023)) (.branch 21 (.leaf 2549288121) (.leaf 2474268170)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2402010633) (.leaf 2332388439)) (.branch 25 (.leaf 2265281506) (.leaf 2200576290))) (.branch 28 (.branch 27 (.leaf 2138165382) (.leaf 2077947119)) (.branch 29 (.leaf 2019825230) (.leaf 1963708510)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1909510509) (.branch 32 (.leaf 1857149250) (.leaf 1806546960))) (.branch 35 (.branch 34 (.leaf 1757629824) (.leaf 1710327751)) (.branch 36 (.leaf 1664574162) (.leaf 1620305784)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1577462462) (.leaf 1535986983)) (.branch 40 (.leaf 1495824912) (.leaf 1456924434))) (.branch 43 (.branch 42 (.leaf 1419236208) (.leaf 1382713236)) (.branch 44 (.leaf 1347310729) (.leaf 1312985990))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1279698302) (.branch 47 (.leaf 1247408819) (.leaf 1216080470))) (.branch 50 (.branch 49 (.leaf 1185677863) (.leaf 1156167195)) (.branch 51 (.leaf 1127516174) (.leaf 1099693937)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1072670978) (.leaf 1046419075)) (.branch 55 (.leaf 1020911232) (.leaf 996121609))) (.branch 58 (.branch 57 (.leaf 972025469) (.leaf 948599121)) (.branch 59 (.leaf 925819870) (.leaf 903665965))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 882116553) (.branch 62 (.leaf 861151640) (.leaf 840752044))) (.branch 65 (.branch 64 (.leaf 820899356) (.leaf 801575908)) (.branch 66 (.leaf 782764733) (.leaf 764449534)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 746614653) (.leaf 729245039)) (.branch 70 (.leaf 712326223) (.leaf 695844287))) (.branch 73 (.branch 72 (.leaf 679785845) (.leaf 664138011)) (.branch 74 (.leaf 648888383) (.leaf 634025020))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 619536417) (.branch 77 (.leaf 605411492) (.leaf 591639562))) (.branch 80 (.branch 79 (.leaf 578210331) (.leaf 565113867)) (.branch 81 (.leaf 552340592) (.leaf 539881262)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 527726956) (.leaf 515869064)) (.branch 85 (.leaf 504299267) (.leaf 493009532))) (.branch 88 (.branch 87 (.leaf 481992097) (.leaf 471239461)) (.branch 89 (.leaf 460744370) (.leaf 450499813)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 440499006) (.branch 92 (.leaf 430735388) (.leaf 421202609))) (.branch 95 (.branch 94 (.leaf 411894521) (.leaf 402805176)) (.branch 96 (.leaf 393928808) (.leaf 385259837)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 376792855) (.leaf 368522620)) (.branch 100 (.leaf 360444052) (.leaf 352552228))) (.branch 103 (.branch 102 (.leaf 344842369) (.leaf 337309846)) (.branch 104 (.leaf 329950162) (.leaf 322758959))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 315732004) (.leaf 308865188)) (.branch 108 (.leaf 302154524) (.leaf 295596138))) (.branch 111 (.branch 110 (.leaf 289186268) (.leaf 282921259)) (.branch 112 (.leaf 276797560) (.leaf 270811721)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 264960387) (.leaf 259240297)) (.branch 116 (.leaf 253648281) (.leaf 248181255))) (.branch 119 (.branch 118 (.leaf 242836221) (.leaf 237610262)) (.branch 120 (.leaf 232500539) (.leaf 227504290)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 250).prefactor = (4833529169140279/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 250).cutoff/(generalMeanRows 250).c)).2 =
    (185821008478627/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 250).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 250).q*(generalMeanRows 250).c/2-2 = (419/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable106.value]
  have hcontinuation : (generalMeanRows 250).q*(generalMeanRows 250).cutoff/2-2 = (2126/1005:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable121.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 250).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 250).criticalRate j.val*(generalMeanRows 250).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 250).c*(generalMeanRows 250).criticalPoint j.val)).2-
      (generalMeanRows 250).J/2-(generalMeanRows 250).error (generalMeanGrid j.val)+
      (generalMeanRows 250).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 250).c)).2-
      (generalMeanRows 250).J/2-(generalMeanRows 250).error 4 := by
  have he : (generalMeanRows 250).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 250) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 250)
    (generalMeanRows_prefactorDomain 250) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0250

/-! Kernel-checked entropy margins for general spectral rectangle 251. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0251
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4852714181) (.branch 2 (.leaf 4678795889) (.leaf 4512848085))) (.branch 5 (.branch 4 (.leaf 4354412893) (.leaf 4203064796)) (.branch 6 (.leaf 4058407821) (.leaf 3920073019)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3787716213) (.leaf 3661015974)) (.branch 10 (.leaf 3539671801) (.leaf 3423402476))) (.branch 13 (.branch 12 (.leaf 3311944580) (.leaf 3205051144)) (.branch 14 (.leaf 3102490423) (.leaf 3004044781))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2909509674) (.branch 17 (.leaf 2818692718) (.leaf 2731412840))) (.branch 20 (.branch 19 (.leaf 2647499495) (.leaf 2566791952)) (.branch 21 (.leaf 2489138627) (.leaf 2414396485)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2342430470) (.leaf 2273112993)) (.branch 25 (.leaf 2206323452) (.leaf 2141947790))) (.branch 28 (.branch 27 (.leaf 2079878079) (.leaf 2020012146)) (.branch 29 (.leaf 1962253216) (.leaf 1906509582)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1852694300) (.branch 32 (.leaf 1800724906) (.leaf 1750523149))) (.branch 35 (.branch 34 (.leaf 1702014742) (.leaf 1655129135)) (.branch 36 (.leaf 1609799294) (.leaf 1565961503)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1523555176) (.leaf 1482522675)) (.branch 40 (.leaf 1442809154) (.leaf 1404362393))) (.branch 43 (.branch 42 (.leaf 1367132662) (.leaf 1331072581)) (.branch 44 (.leaf 1296136989) (.leaf 1262282831))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1229469040) (.branch 47 (.leaf 1197656433) (.leaf 1166807608))) (.branch 50 (.branch 49 (.leaf 1136886856) (.leaf 1107860068)) (.branch 51 (.leaf 1079694655) (.leaf 1052359466)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1025824717) (.leaf 1000061921)) (.branch 55 (.leaf 975043823) (.leaf 950744336))) (.branch 58 (.branch 57 (.leaf 927138483) (.leaf 904202345)) (.branch 59 (.leaf 881913004) (.leaf 860248499))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 839187774) (.branch 62 (.leaf 818710638) (.leaf 798797723))) (.branch 65 (.branch 64 (.leaf 779430441) (.leaf 760590954)) (.branch 66 (.leaf 742262131) (.leaf 724427519)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 707071310) (.leaf 690178312)) (.branch 70 (.leaf 673733920) (.leaf 657724089))) (.branch 73 (.branch 72 (.leaf 642135308) (.leaf 626954578)) (.branch 74 (.leaf 612169387) (.leaf 597767687))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 583737878) (.branch 77 (.leaf 570068783) (.leaf 556749632))) (.branch 80 (.branch 79 (.leaf 543770046) (.leaf 531120017)) (.branch 81 (.leaf 518789893) (.leaf 506770362)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 495052442) (.leaf 483627459)) (.branch 85 (.leaf 472487043) (.leaf 461623109))) (.branch 88 (.branch 87 (.leaf 451027848) (.leaf 440693714)) (.branch 89 (.leaf 430613416) (.leaf 420779905)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 411186366) (.branch 92 (.leaf 401826206) (.leaf 392693050))) (.branch 95 (.branch 94 (.leaf 383780727) (.leaf 375083266)) (.branch 96 (.leaf 366594886) (.leaf 358309990)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 350223158) (.leaf 342329138)) (.branch 100 (.leaf 334622843) (.leaf 327099341))) (.branch 103 (.branch 102 (.leaf 319753854) (.leaf 312581747)) (.branch 104 (.leaf 305578528) (.leaf 298739838))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 292061450) (.leaf 285539261)) (.branch 108 (.leaf 279169290) (.leaf 272947673))) (.branch 111 (.branch 110 (.leaf 266870660) (.leaf 260934607)) (.branch 112 (.leaf 255135976) (.leaf 249471332)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 243937335) (.leaf 238530744)) (.branch 116 (.leaf 233248404) (.leaf 228087252))) (.branch 119 (.branch 118 (.leaf 223044310) (.leaf 218116682)) (.branch 120 (.leaf 213301551) (.leaf 208596177)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 251).prefactor = (4835175662474757/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 251).cutoff/(generalMeanRows 251).c)).2 =
    (90234835681301/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 251).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 251).q*(generalMeanRows 251).c/2-2 = (43/50:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable020.value]
  have hcontinuation : (generalMeanRows 251).q*(generalMeanRows 251).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable030.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 251).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 251).criticalRate j.val*(generalMeanRows 251).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 251).c*(generalMeanRows 251).criticalPoint j.val)).2-
      (generalMeanRows 251).J/2-(generalMeanRows 251).error (generalMeanGrid j.val)+
      (generalMeanRows 251).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 251).c)).2-
      (generalMeanRows 251).J/2-(generalMeanRows 251).error 4 := by
  have he : (generalMeanRows 251).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 251) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 251)
    (generalMeanRows_prefactorDomain 251) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0251

/-! Kernel-checked entropy margins for general spectral rectangle 252. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0252
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4788993170) (.branch 2 (.leaf 4615058309) (.leaf 4449127781))) (.branch 5 (.branch 4 (.leaf 4290741894) (.leaf 4139473419)) (.branch 6 (.leaf 3994924762) (.leaf 3856725441)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3724529822) (.leaf 3598015098)) (.branch 10 (.leaf 3476879456) (.leaf 3360840432))) (.branch 13 (.branch 12 (.leaf 3249633422) (.leaf 3143010324)) (.branch 14 (.leaf 3040738317) (.leaf 2942598737))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2848386058) (.branch 17 (.leaf 2757906961) (.leaf 2670979477))) (.branch 20 (.branch 19 (.leaf 2587432206) (.leaf 2507103596)) (.branch 21 (.leaf 2429841282) (.leaf 2355501478)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2283948410) (.leaf 2215053803)) (.branch 25 (.leaf 2148696397) (.leaf 2084761501))) (.branch 28 (.branch 27 (.leaf 2023140585) (.leaf 1963730897)) (.branch 29 (.leaf 1906435104) (.leaf 1851160970)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1797821039) (.branch 32 (.leaf 1746332358) (.leaf 1696616207))) (.branch 35 (.branch 34 (.leaf 1648597851) (.leaf 1602206307)) (.branch 36 (.leaf 1557374129) (.leaf 1514037205)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1472134570) (.leaf 1431608225)) (.branch 40 (.leaf 1392402971) (.leaf 1354466258))) (.branch 43 (.branch 42 (.leaf 1317748036) (.leaf 1282200619)) (.branch 44 (.leaf 1247778555) (.leaf 1214438507))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1182139142) (.branch 47 (.leaf 1150841019) (.leaf 1120506493))) (.branch 50 (.branch 49 (.leaf 1091099622) (.leaf 1062586072)) (.branch 51 (.leaf 1034933041) (.leaf 1008109175)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 982084496) (.leaf 956830332)) (.branch 55 (.leaf 932319252) (.leaf 908525000))) (.branch 58 (.branch 57 (.leaf 885422442) (.leaf 862987505)) (.branch 59 (.leaf 841197127) (.leaf 820029211))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 799462571) (.branch 62 (.leaf 779476892) (.leaf 760052690))) (.branch 65 (.branch 64 (.leaf 741171269) (.leaf 722814683)) (.branch 66 (.leaf 704965705) (.leaf 687607789)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 670725040) (.leaf 654302184)) (.branch 70 (.leaf 638324540) (.leaf 622777989))) (.branch 73 (.branch 72 (.leaf 607648955) (.leaf 592924376)) (.branch 74 (.leaf 578591679) (.leaf 564638766))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 551053983) (.branch 77 (.leaf 537826109) (.leaf 524944333))) (.branch 80 (.branch 79 (.leaf 512398234) (.leaf 500177769)) (.branch 81 (.leaf 488273255) (.leaf 476675352)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 465375050) (.leaf 454363655)) (.branch 85 (.leaf 443632775) (.leaf 433174307))) (.branch 88 (.branch 87 (.leaf 422980429) (.leaf 413043584)) (.branch 89 (.leaf 403356468) (.leaf 393912028)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 384703441) (.branch 92 (.leaf 375724113) (.leaf 366967667))) (.branch 95 (.branch 94 (.leaf 358427933) (.leaf 350098944)) (.branch 96 (.leaf 341974923) (.leaf 334050279)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 326319599) (.leaf 318777642)) (.branch 100 (.leaf 311419332) (.leaf 304239749))) (.branch 103 (.branch 102 (.leaf 297234128) (.leaf 290397851)) (.branch 104 (.leaf 283726441) (.leaf 277215557))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 270860989) (.leaf 264658656)) (.branch 108 (.leaf 258604597) (.leaf 252694969))) (.branch 111 (.branch 110 (.leaf 246926044) (.leaf 241294202)) (.branch 112 (.leaf 235795929) (.leaf 230427815)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 225186547) (.leaf 220068907)) (.branch 116 (.leaf 215071770) (.leaf 210192099))) (.branch 119 (.branch 118 (.leaf 205426944) (.leaf 200773437)) (.branch 120 (.leaf 196228792) (.leaf 191790298)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 252).prefactor = (4852225177434519/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 252).cutoff/(generalMeanRows 252).c)).2 =
    (70655293995927/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 252).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 252).q*(generalMeanRows 252).c/2-2 = (441/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable108.value]
  have hcontinuation : (generalMeanRows 252).q*(generalMeanRows 252).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable030.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 252).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 252).criticalRate j.val*(generalMeanRows 252).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 252).c*(generalMeanRows 252).criticalPoint j.val)).2-
      (generalMeanRows 252).J/2-(generalMeanRows 252).error (generalMeanGrid j.val)+
      (generalMeanRows 252).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 252).c)).2-
      (generalMeanRows 252).J/2-(generalMeanRows 252).error 4 := by
  have he : (generalMeanRows 252).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 252) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 252)
    (generalMeanRows_prefactorDomain 252) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0252

/-! Kernel-checked entropy margins for general spectral rectangle 253. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0253
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5200071075) (.branch 2 (.leaf 5029013699) (.leaf 4865714735))) (.branch 5 (.branch 4 (.leaf 4709719828) (.leaf 4560607197)) (.branch 6 (.leaf 4417984795) (.leaf 4281487765)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4150776165) (.leaf 4025532929)) (.branch 10 (.leaf 3905462021) (.leaf 3790286776))) (.branch 13 (.branch 12 (.leaf 3679748397) (.leaf 3573604590)) (.branch 14 (.leaf 3471628320) (.leaf 3373606690))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3279339904) (.branch 17 (.leaf 3188640326) (.leaf 3101331622))) (.branch 20 (.branch 19 (.leaf 3017247962) (.leaf 2936233301)) (.branch 21 (.leaf 2858140707) (.leaf 2782831747)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2710175919) (.leaf 2640050130)) (.branch 25 (.leaf 2572338211) (.leaf 2506930469))) (.branch 28 (.branch 27 (.leaf 2443723273) (.leaf 2382618668)) (.branch 29 (.leaf 2323524022) (.leaf 2266351689)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2211018706) (.branch 32 (.leaf 2157446503) (.leaf 2105560638))) (.branch 35 (.branch 34 (.leaf 2055290546) (.leaf 2006569311)) (.branch 36 (.leaf 1959333446) (.leaf 1913522693)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1869079834) (.leaf 1825950513)) (.branch 40 (.leaf 1784083072) (.leaf 1743428399))) (.branch 43 (.branch 42 (.leaf 1703939780) (.leaf 1665572763)) (.branch 44 (.leaf 1628285036) (.leaf 1592036301))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1556788169) (.branch 47 (.leaf 1522504051) (.leaf 1489149059))) (.branch 50 (.branch 49 (.leaf 1456689918) (.leaf 1425094873)) (.branch 51 (.leaf 1394333613) (.leaf 1364377190)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1335197949) (.leaf 1306769458)) (.branch 55 (.leaf 1279066447) (.leaf 1252064744))) (.branch 58 (.branch 57 (.leaf 1225741221) (.leaf 1200073739)) (.branch 59 (.leaf 1175041096) (.leaf 1150622984))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1126799938) (.branch 62 (.leaf 1103553300) (.leaf 1080865173))) (.branch 65 (.branch 64 (.leaf 1058718387) (.leaf 1037096461)) (.branch 66 (.leaf 1015983572) (.leaf 995364521)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 975224702) (.leaf 955550077)) (.branch 70 (.leaf 936327145) (.leaf 917542920))) (.branch 73 (.branch 72 (.leaf 899184903) (.leaf 881241064)) (.branch 74 (.leaf 863699816) (.leaf 846549997))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 829780850) (.branch 77 (.leaf 813382005) (.leaf 797343459))) (.branch 80 (.branch 79 (.leaf 781655564) (.leaf 766309007)) (.branch 81 (.leaf 751294799) (.leaf 736604256)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 722228993) (.leaf 708160902)) (.branch 85 (.leaf 694392148) (.leaf 680915152))) (.branch 88 (.branch 87 (.leaf 667722585) (.leaf 654807354)) (.branch 89 (.leaf 642162591) (.leaf 629781649)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 617658089) (.branch 92 (.leaf 605785672) (.leaf 594158351))) (.branch 95 (.branch 94 (.leaf 582770266) (.leaf 571615732)) (.branch 96 (.leaf 560689236) (.leaf 549985429)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 539499117) (.leaf 529225262)) (.branch 100 (.leaf 519158969) (.leaf 509295483))) (.branch 103 (.branch 102 (.leaf 499630186) (.leaf 490158589)) (.branch 104 (.leaf 480876328) (.leaf 471779161))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 462862962) (.leaf 454123718)) (.branch 108 (.leaf 445557524) (.leaf 437160578))) (.branch 111 (.branch 110 (.leaf 428929182) (.leaf 420859734)) (.branch 112 (.leaf 412948725) (.leaf 405192740)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 397588450) (.leaf 390132611)) (.branch 116 (.leaf 382822062) (.leaf 375653722))) (.branch 119 (.branch 118 (.leaf 368624586) (.leaf 361731724)) (.branch 120 (.leaf 354972279) (.leaf 348343464)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 253).prefactor = (4776632263421303/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 253).cutoff/(generalMeanRows 253).c)).2 =
    (106552683269607/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 253).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 253).q*(generalMeanRows 253).c/2-2 = (91/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable102.value]
  have hcontinuation : (generalMeanRows 253).q*(generalMeanRows 253).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable092.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 253).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 253).criticalRate j.val*(generalMeanRows 253).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 253).c*(generalMeanRows 253).criticalPoint j.val)).2-
      (generalMeanRows 253).J/2-(generalMeanRows 253).error (generalMeanGrid j.val)+
      (generalMeanRows 253).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 253).c)).2-
      (generalMeanRows 253).J/2-(generalMeanRows 253).error 4 := by
  have he : (generalMeanRows 253).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 253) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 253)
    (generalMeanRows_prefactorDomain 253) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0253

/-! Kernel-checked entropy margins for general spectral rectangle 254. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0254
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5235080385) (.branch 2 (.leaf 5062871371) (.leaf 4898473002))) (.branch 5 (.branch 4 (.leaf 4741427864) (.leaf 4591311338)) (.branch 6 (.leaf 4447728735) (.leaf 4310312743)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4178721132) (.leaf 4052634699)) (.branch 10 (.leaf 3931755418) (.leaf 3815804759))) (.branch 13 (.branch 12 (.leaf 3704522185) (.leaf 3597663767)) (.branch 14 (.leaf 3495000946) (.leaf 3396319388))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3301417954) (.branch 17 (.leaf 3210107744) (.leaf 3122211236))) (.branch 20 (.branch 19 (.leaf 3037561486) (.leaf 2956001397)) (.branch 21 (.leaf 2877383047) (.leaf 2801567072)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2728422091) (.leaf 2657824182)) (.branch 25 (.leaf 2589656395) (.leaf 2523808297))) (.branch 28 (.branch 27 (.leaf 2460175560) (.leaf 2398659571)) (.branch 29 (.leaf 2339167072) (.leaf 2281609829)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2225904318) (.branch 32 (.leaf 2171971442) (.leaf 2119736257))) (.branch 35 (.branch 34 (.leaf 2069127723) (.leaf 2020078474)) (.branch 36 (.leaf 1972524595) (.leaf 1926405423)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1881663354) (.leaf 1838243665)) (.branch 40 (.leaf 1796094354) (.leaf 1755165974))) (.branch 43 (.branch 42 (.leaf 1715411499) (.leaf 1676786178)) (.branch 44 (.leaf 1639247412) (.leaf 1602754634))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1567269195) (.branch 47 (.leaf 1532754260) (.leaf 1499174707))) (.branch 50 (.branch 49 (.leaf 1466497036) (.leaf 1434689278)) (.branch 51 (.leaf 1403720919) (.leaf 1373562815)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1344187126) (.leaf 1315567241)) (.branch 55 (.leaf 1287677721) (.leaf 1260494230))) (.branch 58 (.branch 57 (.leaf 1233993485) (.leaf 1208153196)) (.branch 59 (.leaf 1182952022) (.leaf 1158369516))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1134386082) (.branch 62 (.leaf 1110982937) (.leaf 1088142063))) (.branch 65 (.branch 64 (.leaf 1065846174) (.leaf 1044078679)) (.branch 66 (.leaf 1022823649) (.leaf 1002065780)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 981790371) (.leaf 961983287)) (.branch 70 (.leaf 942630937) (.leaf 923720248))) (.branch 73 (.branch 72 (.leaf 905238636) (.leaf 887173991)) (.branch 74 (.leaf 869514647) (.leaf 852249367))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 835367323) (.branch 77 (.leaf 818858073) (.leaf 802711548))) (.branch 80 (.branch 79 (.leaf 786918034) (.leaf 771468157)) (.branch 81 (.leaf 756352867) (.leaf 741563421)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 727091376) (.leaf 712928572)) (.branch 85 (.leaf 699067120) (.leaf 685499392))) (.branch 88 (.branch 87 (.leaf 672218006) (.leaf 659215823)) (.branch 89 (.leaf 646485930) (.leaf 634021634)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 621816452) (.branch 92 (.leaf 609864104) (.leaf 598158503))) (.branch 95 (.branch 94 (.leaf 586693748) (.leaf 575464117)) (.branch 96 (.leaf 564464058) (.leaf 553688188)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 543131278) (.leaf 532788254)) (.branch 100 (.leaf 522654190) (.leaf 512724298))) (.branch 103 (.branch 102 (.leaf 502993930) (.leaf 493458565)) (.branch 104 (.leaf 484113812) (.leaf 474955399))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 465979172) (.leaf 457181092)) (.branch 108 (.leaf 448557226) (.leaf 440103748))) (.branch 111 (.branch 110 (.leaf 431816934) (.leaf 423693158)) (.branch 112 (.leaf 415728889) (.leaf 407920687)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 400265201) (.leaf 392759166)) (.branch 116 (.leaf 385399399) (.leaf 378182798))) (.branch 119 (.branch 118 (.leaf 371106339) (.leaf 364167071)) (.branch 120 (.leaf 357362119) (.leaf 350688675)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 254).prefactor = (961758157135819/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 254).cutoff/(generalMeanRows 254).c)).2 =
    (106552683269607/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 254).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 254).q*(generalMeanRows 254).c/2-2 = (91/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable102.value]
  have hcontinuation : (generalMeanRows 254).q*(generalMeanRows 254).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable092.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 254).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 254).criticalRate j.val*(generalMeanRows 254).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 254).c*(generalMeanRows 254).criticalPoint j.val)).2-
      (generalMeanRows 254).J/2-(generalMeanRows 254).error (generalMeanGrid j.val)+
      (generalMeanRows 254).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 254).c)).2-
      (generalMeanRows 254).J/2-(generalMeanRows 254).error 4 := by
  have he : (generalMeanRows 254).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 254) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 254)
    (generalMeanRows_prefactorDomain 254) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0254

/-! Kernel-checked entropy margins for general spectral rectangle 255. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0255
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5007048391) (.branch 2 (.leaf 4834753181) (.leaf 4670323988))) (.branch 5 (.branch 4 (.leaf 4513303786) (.leaf 4363268127)) (.branch 6 (.leaf 4219822298) (.leaf 4082598782)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3951254987) (.leaf 3825471209)) (.branch 10 (.leaf 3704948785) (.leaf 3589408446))) (.branch 13 (.branch 12 (.leaf 3478588806) (.leaf 3372245006)) (.branch 14 (.leaf 3270147474) (.leaf 3172080800))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3077842707) (.branch 17 (.leaf 2987243112) (.leaf 2900103263))) (.branch 20 (.branch 19 (.leaf 2816254955) (.leaf 2735539799)) (.branch 21 (.leaf 2657808561) (.leaf 2582920545)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2510743029) (.leaf 2441150739)) (.branch 25 (.leaf 2374025370) (.leaf 2309255137))) (.branch 28 (.branch 27 (.leaf 2246734360) (.leaf 2186363081)) (.branch 29 (.leaf 2128046706) (.leaf 2071695676)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2017225158) (.branch 32 (.leaf 1964554757) (.leaf 1913608253))) (.branch 35 (.branch 34 (.leaf 1864313346) (.leaf 1816601429)) (.branch 36 (.leaf 1770407369) (.leaf 1725669306)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1682328462) (.leaf 1640328967)) (.branch 40 (.leaf 1599617690) (.leaf 1560144086))) (.branch 43 (.branch 42 (.leaf 1521860050) (.leaf 1484719784)) (.branch 44 (.leaf 1448679663) (.leaf 1413698122))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1379735539) (.branch 47 (.leaf 1346754132) (.leaf 1314717858))) (.branch 50 (.branch 49 (.leaf 1283592320) (.leaf 1253344683)) (.branch 51 (.leaf 1223943586) (.leaf 1195359067)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1167562490) (.leaf 1140526476)) (.branch 55 (.leaf 1114224840) (.leaf 1088632526))) (.branch 58 (.branch 57 (.leaf 1063725552) (.leaf 1039480954)) (.branch 59 (.leaf 1015876739) (.leaf 992891829))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 970506025) (.branch 62 (.leaf 948699954) (.leaf 927455036))) (.branch 65 (.branch 64 (.leaf 906753440) (.leaf 886578052)) (.branch 66 (.leaf 866912439) (.leaf 847740813)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 829048005) (.leaf 810819437)) (.branch 70 (.leaf 793041086) (.leaf 775699468))) (.branch 73 (.branch 72 (.leaf 758781606) (.leaf 742275010)) (.branch 74 (.leaf 726167655) (.leaf 710447958))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 695104759) (.branch 77 (.leaf 680127302) (.leaf 665505218))) (.branch 80 (.branch 79 (.leaf 651228506) (.leaf 637287519)) (.branch 81 (.leaf 623672947) (.leaf 610375801)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 597387406) (.leaf 584699378)) (.branch 85 (.leaf 572303618) (.leaf 560192301))) (.branch 88 (.branch 87 (.leaf 548357858) (.leaf 536792972)) (.branch 89 (.leaf 525490565) (.leaf 514443789)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 503646015) (.branch 92 (.leaf 493090824) (.leaf 482772004))) (.branch 95 (.branch 94 (.leaf 472683534) (.leaf 462819583)) (.branch 96 (.leaf 453174498) (.leaf 443742799)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 434519175) (.leaf 425498472)) (.branch 100 (.leaf 416675692) (.leaf 408045985))) (.branch 103 (.branch 102 (.leaf 399604642) (.leaf 391347094)) (.branch 104 (.leaf 383268903) (.leaf 375365759))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 367633476) (.leaf 360067985)) (.branch 108 (.leaf 352665334) (.leaf 345421678))) (.branch 111 (.branch 110 (.leaf 338333283) (.leaf 331396514)) (.branch 112 (.leaf 324607838) (.leaf 317963817)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 311461106) (.leaf 305096450)) (.branch 116 (.leaf 298866682) (.leaf 292768716))) (.branch 119 (.branch 118 (.leaf 286799549) (.leaf 280956258)) (.branch 120 (.leaf 275235992) (.leaf 269635979)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 255).prefactor = (601502858427977/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 255).cutoff/(generalMeanRows 255).c)).2 =
    (24766431110557/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 255).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 255).q*(generalMeanRows 255).c/2-2 = (397/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable105.value]
  have hcontinuation : (generalMeanRows 255).q*(generalMeanRows 255).cutoff/2-2 = (536/249:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable118.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 255).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 255).criticalRate j.val*(generalMeanRows 255).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 255).c*(generalMeanRows 255).criticalPoint j.val)).2-
      (generalMeanRows 255).J/2-(generalMeanRows 255).error (generalMeanGrid j.val)+
      (generalMeanRows 255).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 255).c)).2-
      (generalMeanRows 255).J/2-(generalMeanRows 255).error 4 := by
  have he : (generalMeanRows 255).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 255) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 255)
    (generalMeanRows_prefactorDomain 255) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0255

/-! Kernel-checked entropy margins for general spectral rectangle 256. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0256
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5041298145) (.branch 2 (.leaf 4867824382) (.leaf 4702270443))) (.branch 5 (.branch 4 (.leaf 4544176175) (.leaf 4393114226)) (.branch 6 (.leaf 4248687183) (.leaf 4110525015)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3978282789) (.leaf 3851638610)) (.branch 10 (.leaf 3730291777) (.leaf 3613961106))) (.branch 13 (.branch 12 (.leaf 3502383425) (.leaf 3395312201)) (.branch 14 (.leaf 3292516290) (.leaf 3193778810))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3098896100) (.branch 17 (.leaf 3007676775) (.leaf 2919940863))) (.branch 20 (.branch 19 (.leaf 2835519007) (.leaf 2754251734)) (.branch 21 (.leaf 2675988791) (.leaf 2600588518)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2527917285) (.leaf 2457848962)) (.branch 25 (.leaf 2390264435) (.leaf 2325051154))) (.branch 28 (.branch 27 (.leaf 2262102716) (.leaf 2201318478)) (.branch 29 (.leaf 2142603201) (.leaf 2085866712)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2031023599) (.branch 32 (.leaf 1977992917) (.leaf 1926697923))) (.branch 35 (.branch 34 (.leaf 1877065824) (.leaf 1829027542)) (.branch 36 (.leaf 1782517501) (.leaf 1737473415)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1693836107) (.leaf 1651549323)) (.branch 40 (.leaf 1610559568) (.leaf 1570815952))) (.branch 43 (.branch 42 (.leaf 1532270042) (.leaf 1494875725)) (.branch 44 (.leaf 1458589079) (.leaf 1423368253))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1389173356) (.branch 47 (.leaf 1355966345) (.leaf 1323710933))) (.branch 50 (.branch 49 (.leaf 1292372487) (.leaf 1261917947)) (.branch 51 (.leaf 1232315737) (.leaf 1203535691)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1175548977) (.leaf 1148328029)) (.branch 55 (.leaf 1121846482) (.leaf 1096079108))) (.branch 58 (.branch 57 (.leaf 1071001762) (.leaf 1046591324)) (.branch 59 (.leaf 1022825649) (.leaf 999683516))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 977144585) (.branch 62 (.leaf 955189354) (.leaf 933799114))) (.branch 65 (.branch 64 (.leaf 912955913) (.leaf 892642519)) (.branch 66 (.leaf 872842387) (.leaf 853539621)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 834718949) (.leaf 816365692)) (.branch 70 (.leaf 798465731) (.leaf 781005491))) (.branch 73 (.branch 72 (.leaf 763971906) (.leaf 747352400)) (.branch 74 (.leaf 731134866) (.leaf 715307641))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 699859490) (.branch 77 (.leaf 684779583) (.leaf 670057479))) (.branch 80 (.branch 79 (.leaf 655683110) (.leaf 641646762)) (.branch 81 (.leaf 627939062) (.leaf 614550960)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 601473720) (.leaf 588698902)) (.branch 85 (.leaf 576218351) (.leaf 564024188))) (.branch 88 (.branch 87 (.leaf 552108794) (.leaf 540464801)) (.branch 89 (.leaf 529085083) (.leaf 517962743)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 507091109) (.branch 92 (.leaf 496463717) (.leaf 486074313))) (.branch 95 (.branch 94 (.leaf 475916835) (.leaf 465985411)) (.branch 96 (.leaf 456274351) (.leaf 446778137)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 437491420) (.leaf 428409013)) (.branch 100 (.leaf 419525882) (.leaf 410837145))) (.branch 103 (.branch 102 (.leaf 402338061) (.leaf 394024028)) (.branch 104 (.leaf 385890580) (.leaf 377933376))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 370148202) (.leaf 362530961)) (.branch 108 (.leaf 355077673) (.leaf 347784469))) (.branch 111 (.branch 110 (.leaf 340647587) (.leaf 333663368)) (.branch 112 (.leaf 326828255) (.leaf 320138787)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 313591596) (.leaf 307183404)) (.branch 116 (.leaf 300911022) (.leaf 294771344))) (.branch 119 (.branch 118 (.leaf 288761346) (.leaf 282878085)) (.branch 120 (.leaf 277118691) (.leaf 271480372)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 256).prefactor = (4844938586590937/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 256).cutoff/(generalMeanRows 256).c)).2 =
    (24766431110557/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 256).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 256).q*(generalMeanRows 256).c/2-2 = (397/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable105.value]
  have hcontinuation : (generalMeanRows 256).q*(generalMeanRows 256).cutoff/2-2 = (536/249:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable118.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 256).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 256).criticalRate j.val*(generalMeanRows 256).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 256).c*(generalMeanRows 256).criticalPoint j.val)).2-
      (generalMeanRows 256).J/2-(generalMeanRows 256).error (generalMeanGrid j.val)+
      (generalMeanRows 256).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 256).c)).2-
      (generalMeanRows 256).J/2-(generalMeanRows 256).error 4 := by
  have he : (generalMeanRows 256).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 256) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 256)
    (generalMeanRows_prefactorDomain 256) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0256

/-! Kernel-checked entropy margins for general spectral rectangle 257. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0257
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5023249772) (.branch 2 (.leaf 4847892915) (.leaf 4680572231))) (.branch 5 (.branch 4 (.leaf 4520821140) (.leaf 4368206289)) (.branch 6 (.leaf 4222324658) (.leaf 4082800967)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3949285364) (.leaf 3821451339)) (.branch 10 (.leaf 3698993855) (.leaf 3581627653))) (.branch 13 (.branch 12 (.leaf 3469085722) (.leaf 3361117910)) (.branch 14 (.leaf 3257489666) (.leaf 3157980886))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3062384867) (.branch 17 (.leaf 2970507348) (.leaf 2882165635))) (.branch 20 (.branch 19 (.leaf 2797187792) (.leaf 2715411907)) (.branch 21 (.leaf 2636685408) (.leaf 2560864440)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2487813286) (.leaf 2417403835)) (.branch 25 (.leaf 2349515090) (.leaf 2284032709))) (.branch 28 (.branch 27 (.leaf 2220848585) (.leaf 2159860457)) (.branch 29 (.leaf 2100971538) (.leaf 2044090187)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1989129588) (.branch 32 (.leaf 1936007460) (.leaf 1884645785))) (.branch 35 (.branch 34 (.leaf 1834970553) (.leaf 1786911528)) (.branch 36 (.leaf 1740402023) (.leaf 1695378695)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1651781355) (.leaf 1609552783)) (.branch 40 (.leaf 1568638561) (.leaf 1528986917))) (.branch 43 (.branch 42 (.leaf 1490548573) (.leaf 1453276608)) (.branch 44 (.leaf 1417126328) (.leaf 1382055144))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1348022456) (.branch 47 (.leaf 1314989546) (.leaf 1282919477))) (.branch 50 (.branch 49 (.leaf 1251776997) (.leaf 1221528451)) (.branch 51 (.leaf 1192141695) (.leaf 1163586017)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1135832065) (.leaf 1108851771)) (.branch 55 (.leaf 1082618292) (.leaf 1057105942))) (.branch 58 (.branch 57 (.leaf 1032290135) (.leaf 1008147330)) (.branch 59 (.leaf 984654978) (.leaf 961791473))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 939536104) (.branch 62 (.leaf 917869014) (.leaf 896771153))) (.branch 65 (.branch 64 (.leaf 876224244) (.leaf 856210743)) (.branch 66 (.leaf 836713805) (.leaf 817717250)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 799205530) (.leaf 781163702)) (.branch 70 (.leaf 763577399) (.leaf 746432801))) (.branch 73 (.branch 72 (.leaf 729716614) (.leaf 713416042)) (.branch 74 (.leaf 697518764) (.leaf 682012918))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 666887073) (.branch 77 (.leaf 652130216) (.leaf 637731729))) (.branch 80 (.branch 79 (.leaf 623681374) (.leaf 609969276)) (.branch 81 (.leaf 596585907) (.leaf 583522071)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 570768891) (.leaf 558317792)) (.branch 85 (.leaf 546160492) (.leaf 534288988))) (.branch 88 (.branch 87 (.leaf 522695546) (.leaf 511372686)) (.branch 89 (.leaf 500313177) (.leaf 489510022)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 478956451) (.branch 92 (.leaf 468645913) (.leaf 458572063))) (.branch 95 (.branch 94 (.leaf 448728760) (.leaf 439110053)) (.branch 96 (.leaf 429710178) (.leaf 420523547)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 411544746) (.leaf 402768525)) (.branch 100 (.leaf 394189790) (.leaf 385803604))) (.branch 103 (.branch 102 (.leaf 377605173) (.leaf 369589846)) (.branch 104 (.leaf 361753110) (.leaf 354090581))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 346598004) (.leaf 339271244)) (.branch 108 (.leaf 332106284) (.leaf 325099223))) (.branch 111 (.branch 110 (.leaf 318246268) (.leaf 311543733)) (.branch 112 (.leaf 304988032) (.leaf 298575680)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 292303288) (.leaf 286167558)) (.branch 116 (.leaf 280165281) (.leaf 274293336))) (.branch 119 (.branch 118 (.leaf 268548683) (.leaf 262928365)) (.branch 120 (.leaf 257429502) (.leaf 252049290)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 257).prefactor = (4911447026030401/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 257).cutoff/(generalMeanRows 257).c)).2 =
    (77683944061577/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 257).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 257).q*(generalMeanRows 257).c/2-2 = (102/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable107.value]
  have hcontinuation : (generalMeanRows 257).q*(generalMeanRows 257).cutoff/2-2 = (536/249:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable118.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 257).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 257).criticalRate j.val*(generalMeanRows 257).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 257).c*(generalMeanRows 257).criticalPoint j.val)).2-
      (generalMeanRows 257).J/2-(generalMeanRows 257).error (generalMeanGrid j.val)+
      (generalMeanRows 257).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 257).c)).2-
      (generalMeanRows 257).J/2-(generalMeanRows 257).error 4 := by
  have he : (generalMeanRows 257).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 257) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 257)
    (generalMeanRows_prefactorDomain 257) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0257

/-! Kernel-checked entropy margins for general spectral rectangle 258. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0258
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5027083534) (.branch 2 (.leaf 4854133285) (.leaf 4689063492))) (.branch 5 (.branch 4 (.leaf 4531417413) (.leaf 4380770811)) (.branch 6 (.leaf 4236729123) (.leaf 4098924924)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3967015664) (.leaf 3840681632)) (.branch 10 (.leaf 3719624120) (.leaf 3603563771))) (.branch 13 (.branch 12 (.leaf 3492239084) (.leaf 3385405050)) (.branch 14 (.leaf 3282831925) (.leaf 3184304103))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3089619089) (.branch 17 (.leaf 2998586567) (.leaf 2911027536))) (.branch 20 (.branch 19 (.leaf 2826773529) (.leaf 2745665886)) (.branch 21 (.leaf 2667555093) (.leaf 2592300165)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2519768087) (.leaf 2449833289)) (.branch 25 (.leaf 2382377166) (.leaf 2317287630))) (.branch 28 (.branch 27 (.leaf 2254458699) (.leaf 2193790112)) (.branch 29 (.leaf 2135186976) (.leaf 2078559432)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2023822350) (.branch 32 (.leaf 1970895042) (.leaf 1919700996))) (.branch 35 (.branch 34 (.leaf 1870167626) (.leaf 1822226045)) (.branch 36 (.leaf 1775810841) (.leaf 1730859883)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1687314127) (.leaf 1645117438)) (.branch 40 (.leaf 1604216433) (.leaf 1564560314))) (.branch 43 (.branch 42 (.leaf 1526100735) (.leaf 1488791656)) (.branch 44 (.leaf 1452589222) (.leaf 1417451640))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1383339070) (.branch 47 (.leaf 1350213513) (.leaf 1318038720))) (.branch 50 (.branch 49 (.leaf 1286780091) (.leaf 1256404594)) (.branch 51 (.leaf 1226880676) (.leaf 1198178192)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1170268327) (.leaf 1143123529)) (.branch 55 (.leaf 1116717442) (.leaf 1091024848))) (.branch 58 (.branch 57 (.leaf 1066021609) (.leaf 1041684608)) (.branch 59 (.leaf 1017991705) (.leaf 994921680))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 972454195) (.branch 62 (.leaf 950569746) (.leaf 929249623))) (.branch 65 (.branch 64 (.leaf 908475874) (.leaf 888231265)) (.branch 66 (.leaf 868499246) (.leaf 849263919)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 830510011) (.leaf 812222836)) (.branch 70 (.leaf 794388275) (.leaf 776992748))) (.branch 73 (.branch 72 (.leaf 760023186) (.leaf 743467010)) (.branch 74 (.leaf 727312109) (.leaf 711546819))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 696159901) (.branch 77 (.leaf 681140522) (.leaf 666478242))) (.branch 80 (.branch 79 (.leaf 652162988) (.leaf 638185045)) (.branch 81 (.leaf 624535040) (.leaf 611203921)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 598182952) (.leaf 585463693)) (.branch 85 (.leaf 573037990) (.leaf 560897962))) (.branch 88 (.branch 87 (.leaf 549035992) (.leaf 537444713)) (.branch 89 (.leaf 526117000) (.leaf 515045959)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 504224919) (.branch 92 (.leaf 493647420) (.leaf 483307208))) (.branch 95 (.branch 94 (.leaf 473198226) (.leaf 463314604)) (.branch 96 (.leaf 453650656) (.leaf 444200867)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 434959894) (.leaf 425922552)) (.branch 100 (.leaf 417083814) (.leaf 408438799))) (.branch 103 (.branch 102 (.leaf 399982773) (.leaf 391711140)) (.branch 104 (.leaf 383619437) (.leaf 375703331))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 367958611) (.leaf 360381187)) (.branch 108 (.leaf 352967084) (.leaf 345712441))) (.branch 111 (.branch 110 (.leaf 338613499) (.leaf 331666609)) (.branch 112 (.leaf 324868218) (.leaf 318214871)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 311703207) (.leaf 305329956)) (.branch 116 (.leaf 299091934) (.leaf 292986042))) (.branch 119 (.branch 118 (.leaf 287009264) (.leaf 281158662)) (.branch 120 (.leaf 275431374) (.leaf 269824614)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 258).prefactor = (4813600907861221/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 258).cutoff/(generalMeanRows 258).c)).2 =
    (196627688352479/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 258).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 258).q*(generalMeanRows 258).c/2-2 = (397/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable105.value]
  have hcontinuation : (generalMeanRows 258).q*(generalMeanRows 258).cutoff/2-2 = (2138/999:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable120.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 258).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 258).criticalRate j.val*(generalMeanRows 258).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 258).c*(generalMeanRows 258).criticalPoint j.val)).2-
      (generalMeanRows 258).J/2-(generalMeanRows 258).error (generalMeanGrid j.val)+
      (generalMeanRows 258).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 258).c)).2-
      (generalMeanRows 258).J/2-(generalMeanRows 258).error 4 := by
  have he : (generalMeanRows 258).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 258) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 258)
    (generalMeanRows_prefactorDomain 258) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0258

/-! Kernel-checked entropy margins for general spectral rectangle 259. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0259
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4958495438) (.branch 2 (.leaf 4785442276) (.leaf 4620304176))) (.branch 5 (.branch 4 (.leaf 4462622710) (.leaf 4311972046)) (.branch 6 (.leaf 4167956110) (.leaf 4030206044)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3898377936) (.leaf 3772150779)) (.branch 10 (.leaf 3651224631) (.leaf 3535318959))) (.branch 13 (.branch 12 (.leaf 3424171137) (.leaf 3317535087)) (.branch 14 (.leaf 3215180038) (.leaf 3116889401))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3022459743) (.branch 17 (.leaf 2931699847) (.leaf 2844429850))) (.branch 20 (.branch 19 (.leaf 2760480456) (.leaf 2679692211)) (.branch 21 (.leaf 2601914835) (.leaf 2527006613)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2454833824) (.leaf 2385270220)) (.branch 25 (.leaf 2318196545) (.leaf 2253500084))) (.branch 28 (.branch 27 (.leaf 2191074252) (.leaf 2130818208)) (.branch 29 (.leaf 2072636501) (.leaf 2016438733)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1962139256) (.branch 32 (.leaf 1909656885) (.leaf 1858914626))) (.branch 35 (.branch 34 (.leaf 1809839434) (.leaf 1762361972)) (.branch 36 (.leaf 1716416404) (.leaf 1671940183)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1628873867) (.leaf 1587160941)) (.branch 40 (.leaf 1546747649) (.leaf 1507582843))) (.branch 43 (.branch 42 (.leaf 1469617830) (.leaf 1432806245)) (.branch 44 (.leaf 1397103914) (.leaf 1362468741))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1328860590) (.branch 47 (.leaf 1296241182) (.leaf 1264573996))) (.branch 50 (.branch 49 (.leaf 1233824172) (.leaf 1203958425)) (.branch 51 (.leaf 1174944964) (.leaf 1146753410)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1119354726) (.leaf 1092721147)) (.branch 55 (.leaf 1066826111) (.leaf 1041644205))) (.branch 58 (.branch 57 (.leaf 1017151100) (.leaf 993323500)) (.branch 59 (.leaf 970139088) (.leaf 947576483))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 925615184) (.branch 62 (.leaf 904235536) (.leaf 883418684))) (.branch 65 (.branch 64 (.leaf 863146535) (.leaf 843401722)) (.branch 66 (.leaf 824167569) (.leaf 805428058)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 787167797) (.leaf 769371992)) (.branch 70 (.leaf 752026418) (.leaf 735117396))) (.branch 73 (.branch 72 (.leaf 718631760) (.leaf 702556844)) (.branch 74 (.leaf 686880450) (.leaf 671590832))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 656676675) (.branch 77 (.leaf 642127075) (.leaf 627931520))) (.branch 80 (.branch 79 (.leaf 614079875) (.leaf 600562364)) (.branch 81 (.leaf 587369556) (.leaf 574492346)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 561921947) (.leaf 549649872)) (.branch 85 (.leaf 537667924) (.leaf 525968181))) (.branch 88 (.branch 87 (.leaf 514542989) (.leaf 503384945)) (.branch 89 (.leaf 492486894) (.leaf 481841910)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 471443296) (.branch 92 (.leaf 461284569) (.leaf 451359452))) (.branch 95 (.branch 94 (.leaf 441661868) (.leaf 432185931)) (.branch 96 (.leaf 422925939) (.leaf 413876365)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 405031852) (.leaf 396387209)) (.branch 100 (.leaf 387937399) (.leaf 379677538))) (.branch 103 (.branch 102 (.leaf 371602887) (.leaf 363708847)) (.branch 104 (.leaf 355990956) (.leaf 348444880))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 341066411) (.leaf 333851464)) (.branch 108 (.leaf 326796069) (.leaf 319896369))) (.branch 111 (.branch 110 (.leaf 313148615) (.leaf 306549165)) (.branch 112 (.leaf 300094478) (.leaf 293781109)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 287605709) (.leaf 281565021)) (.branch 116 (.leaf 275655875) (.leaf 269875188))) (.branch 119 (.branch 118 (.leaf 264219958) (.leaf 258687265)) (.branch 120 (.leaf 253274265) (.leaf 247978188)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 259).prefactor = (4830167995256131/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 259).cutoff/(generalMeanRows 259).c)).2 =
    (385412199243929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 259).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 259).q*(generalMeanRows 259).c/2-2 = (102/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable107.value]
  have hcontinuation : (generalMeanRows 259).q*(generalMeanRows 259).cutoff/2-2 = (2138/999:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable120.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 259).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 259).criticalRate j.val*(generalMeanRows 259).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 259).c*(generalMeanRows 259).criticalPoint j.val)).2-
      (generalMeanRows 259).J/2-(generalMeanRows 259).error (generalMeanGrid j.val)+
      (generalMeanRows 259).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 259).c)).2-
      (generalMeanRows 259).J/2-(generalMeanRows 259).error 4 := by
  have he : (generalMeanRows 259).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 259) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 259)
    (generalMeanRows_prefactorDomain 259) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0259

/-! Kernel-checked entropy margins for general spectral rectangle 260. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0260
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4894645766) (.branch 2 (.leaf 4721463829) (.leaf 4556218252))) (.branch 5 (.branch 4 (.leaf 4398450743) (.leaf 4247735520)) (.branch 6 (.leaf 4103676479) (.leaf 3965904666)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3834076008) (.leaf 3707869280)) (.branch 10 (.leaf 3586984275) (.leaf 3471140148))) (.branch 13 (.branch 12 (.leaf 3360073923) (.leaf 3253539137)) (.branch 14 (.leaf 3151304606) (.leaf 3053153301))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2958881328) (.branch 17 (.leaf 2868296987) (.leaf 2781219921))) (.branch 20 (.branch 19 (.leaf 2697480324) (.leaf 2616918224)) (.branch 21 (.leaf 2539382816) (.leaf 2464731851)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2392831073) (.leaf 2323553698)) (.branch 25 (.leaf 2256779930) (.leaf 2192396521))) (.branch 28 (.branch 27 (.leaf 2130296351) (.leaf 2070378049)) (.branch 29 (.leaf 2012545639) (.leaf 1956708203)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1902779583) (.branch 32 (.leaf 1850678085) (.leaf 1800326221))) (.branch 35 (.branch 34 (.leaf 1751650453) (.leaf 1704580968)) (.branch 36 (.leaf 1659051457) (.leaf 1614998912)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1572363441) (.leaf 1531088088)) (.branch 40 (.leaf 1491118667) (.leaf 1452403611))) (.branch 43 (.branch 42 (.leaf 1414893818) (.leaf 1378542524)) (.branch 44 (.leaf 1343305171) (.leaf 1309139283))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1276004362) (.branch 47 (.leaf 1243861774) (.leaf 1212674653))) (.branch 50 (.branch 49 (.leaf 1182407807) (.leaf 1153027629)) (.branch 51 (.leaf 1124502015) (.leaf 1096800285)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1069893111) (.leaf 1043752446)) (.branch 55 (.leaf 1018351457) (.leaf 993664469))) (.branch 58 (.branch 57 (.leaf 969666901) (.leaf 946335214)) (.branch 59 (.leaf 923646859) (.leaf 901580228))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 880114605) (.branch 62 (.leaf 859230127) (.leaf 838907742))) (.branch 65 (.branch 64 (.leaf 819129164) (.leaf 799876845)) (.branch 66 (.leaf 781133933) (.leaf 762884243)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 745112223) (.leaf 727802926)) (.branch 70 (.leaf 710941982) (.leaf 694515571))) (.branch 73 (.branch 72 (.leaf 678510397) (.leaf 662913666)) (.branch 74 (.leaf 647713061) (.leaf 632896722))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 618453227) (.branch 77 (.leaf 604371568) (.leaf 590641137))) (.branch 80 (.branch 79 (.leaf 577251709) (.leaf 564193420)) (.branch 81 (.leaf 551456757) (.leaf 539032541)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 526911911) (.leaf 515086314)) (.branch 85 (.leaf 503547489) (.leaf 492287456))) (.branch 88 (.branch 87 (.leaf 481298506) (.leaf 470573185)) (.branch 89 (.leaf 460104290) (.leaf 449884855)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 439908139) (.branch 92 (.leaf 430167625) (.leaf 420657002))) (.branch 95 (.branch 94 (.leaf 411370163) (.leaf 402301195)) (.branch 96 (.leaf 393444371) (.leaf 384794143)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 376345137) (.leaf 368092143)) (.branch 100 (.leaf 360030112) (.leaf 352154148))) (.branch 103 (.branch 102 (.leaf 344459504) (.leaf 336941573)) (.branch 104 (.leaf 329595889) (.leaf 322418115))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 315404042) (.leaf 308549586)) (.branch 108 (.leaf 301850780) (.leaf 295303772))) (.branch 111 (.branch 110 (.leaf 288904818) (.leaf 282650285)) (.branch 112 (.leaf 276536639) (.leaf 270560447)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 264718372) (.leaf 259007169)) (.branch 116 (.leaf 253423684) (.leaf 247964847))) (.branch 119 (.branch 118 (.leaf 242627674) (.leaf 237409262)) (.branch 120 (.leaf 232306786) (.leaf 227317496)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 260).prefactor = (2415930028110817/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 260).cutoff/(generalMeanRows 260).c)).2 =
    (374631555805619/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 260).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 260).q*(generalMeanRows 260).c/2-2 = (419/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable106.value]
  have hcontinuation : (generalMeanRows 260).q*(generalMeanRows 260).cutoff/2-2 = (1066/501:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable119.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 260).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 260).criticalRate j.val*(generalMeanRows 260).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 260).c*(generalMeanRows 260).criticalPoint j.val)).2-
      (generalMeanRows 260).J/2-(generalMeanRows 260).error (generalMeanGrid j.val)+
      (generalMeanRows 260).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 260).c)).2-
      (generalMeanRows 260).J/2-(generalMeanRows 260).error 4 := by
  have he : (generalMeanRows 260).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 260) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 260)
    (generalMeanRows_prefactorDomain 260) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0260

/-! Kernel-checked entropy margins for general spectral rectangle 261. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0261
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4911627680) (.branch 2 (.leaf 4737844890) (.leaf 4572025996))) (.branch 5 (.branch 4 (.leaf 4413711114) (.leaf 4262472986)) (.branch 6 (.leaf 4117914134) (.leaf 3979664324)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3847378288) (.leaf 3720733687)) (.branch 10 (.leaf 3599429272) (.leaf 3483183226))) (.branch 13 (.branch 12 (.leaf 3371731658) (.leaf 3264827251)) (.branch 14 (.leaf 3162238019) (.leaf 3063746179))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2969147130) (.branch 17 (.leaf 2878248508) (.leaf 2790869329))) (.branch 20 (.branch 19 (.leaf 2706839199) (.leaf 2625997590)) (.branch 21 (.leaf 2548193174) (.leaf 2473283208)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2401132971) (.leaf 2331615238)) (.branch 25 (.leaf 2264609800) (.leaf 2200003014))) (.branch 28 (.branch 27 (.leaf 2137687388) (.leaf 2077561200)) (.branch 29 (.leaf 2019528141) (.leaf 1963496979)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1909381253) (.branch 32 (.leaf 1857098990) (.leaf 1806572431))) (.branch 35 (.branch 34 (.leaf 1757727783) (.leaf 1710494991)) (.branch 36 (.leaf 1664807515) (.leaf 1620602131)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1577818736) (.leaf 1536400179)) (.branch 40 (.leaf 1496292085) (.leaf 1457442707))) (.branch 43 (.branch 42 (.leaf 1419802775) (.leaf 1383325361)) (.branch 44 (.leaf 1347965751) (.leaf 1313681326))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1280431444) (.branch 47 (.leaf 1248177338) (.leaf 1216882013))) (.branch 50 (.branch 49 (.leaf 1186510156) (.leaf 1157028044)) (.branch 51 (.leaf 1128403461) (.leaf 1100605620)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1073605092) (.leaf 1047373732)) (.branch 55 (.leaf 1021884615) (.leaf 997111976))) (.branch 58 (.branch 57 (.leaf 973031149) (.leaf 949618513)) (.branch 59 (.leaf 926851441) (.leaf 904708249))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 883168151) (.branch 62 (.leaf 862211216) (.leaf 841818322))) (.branch 65 (.branch 64 (.leaf 821971123) (.leaf 802652008)) (.branch 66 (.leaf 783844068) (.leaf 765531060)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 747697380) (.leaf 730328029)) (.branch 70 (.leaf 713408586) (.leaf 696925184))) (.branch 73 (.branch 72 (.leaf 680864480) (.leaf 665213636)) (.branch 74 (.leaf 649960293) (.leaf 635092550))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 620598943) (.branch 77 (.leaf 606468427) (.leaf 592690360))) (.branch 80 (.branch 79 (.leaf 579254477) (.leaf 566150882)) (.branch 81 (.leaf 553370029) (.leaf 540902707)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 528740025) (.leaf 516873399)) (.branch 85 (.leaf 505294541) (.leaf 493995441))) (.branch 88 (.branch 87 (.leaf 482968365) (.leaf 472205833)) (.branch 89 (.leaf 461700617) (.leaf 451445725)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 441434395) (.branch 92 (.leaf 431660086) (.leaf 422116466))) (.branch 95 (.branch 94 (.leaf 412797407) (.leaf 403696974)) (.branch 96 (.leaf 394809421) (.leaf 386129182)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 377650862) (.leaf 369369234)) (.branch 100 (.leaf 361279232) (.leaf 353375943))) (.branch 103 (.branch 102 (.leaf 345654602) (.leaf 338110588)) (.branch 104 (.leaf 330739418) (.leaf 323536740))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 316498333) (.leaf 309620095)) (.branch 108 (.leaf 302898048) (.leaf 296328324))) (.branch 111 (.branch 110 (.leaf 289907170) (.leaf 283630937)) (.branch 112 (.leaf 277496080) (.leaf 271499153)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 265636809) (.leaf 259905792)) (.branch 116 (.leaf 254302934) (.leaf 248825158))) (.branch 119 (.branch 118 (.leaf 243469468) (.leaf 238232951)) (.branch 120 (.leaf 233112771) (.leaf 228106171)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 261).prefactor = (38788993081929/8000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 261).cutoff/(generalMeanRows 261).c)).2 =
    (374631555805619/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 261).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 261).q*(generalMeanRows 261).c/2-2 = (419/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable106.value]
  have hcontinuation : (generalMeanRows 261).q*(generalMeanRows 261).cutoff/2-2 = (1066/501:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable119.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 261).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 261).criticalRate j.val*(generalMeanRows 261).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 261).c*(generalMeanRows 261).criticalPoint j.val)).2-
      (generalMeanRows 261).J/2-(generalMeanRows 261).error (generalMeanGrid j.val)+
      (generalMeanRows 261).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 261).c)).2-
      (generalMeanRows 261).J/2-(generalMeanRows 261).error 4 := by
  have he : (generalMeanRows 261).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 261) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 261)
    (generalMeanRows_prefactorDomain 261) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0261

/-! Kernel-checked entropy margins for general spectral rectangle 262. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0262
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4975561213) (.branch 2 (.leaf 4801912449) (.leaf 4636205989))) (.branch 5 (.branch 4 (.leaf 4477981827) (.leaf 4326812665)) (.branch 6 (.leaf 4182301066) (.leaf 4044076902)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3911795079) (.leaf 3785133482)) (.branch 10 (.leaf 3663791139) (.leaf 3547486552))) (.branch 13 (.branch 12 (.leaf 3435956190) (.leaf 3328953128)) (.branch 14 (.leaf 3226245801) (.leaf 3127616875))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3032862216) (.branch 17 (.leaf 2941789950) (.leaf 2854219594))) (.branch 20 (.branch 19 (.leaf 2769981269) (.leaf 2688914973)) (.branch 21 (.leaf 2610869909) (.leaf 2535703873)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2463282685) (.leaf 2393479662)) (.branch 25 (.leaf 2326175138) (.leaf 2261256010))) (.branch 28 (.branch 27 (.leaf 2198615325) (.leaf 2138151897)) (.branch 29 (.leaf 2079769944) (.leaf 2023378759)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1968892398) (.branch 32 (.leaf 1916229397) (.leaf 1865312498))) (.branch 35 (.branch 34 (.leaf 1816068402) (.leaf 1768427536)) (.branch 36 (.leaf 1722323836) (.leaf 1677694540)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1634480002) (.leaf 1592623511)) (.branch 40 (.leaf 1552071128) (.leaf 1512771527))) (.branch 43 (.branch 42 (.leaf 1474675850) (.leaf 1437737569)) (.branch 44 (.leaf 1401912360) (.leaf 1367157982))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1333434162) (.branch 47 (.leaf 1300702487) (.leaf 1268926311))) (.branch 50 (.branch 49 (.leaf 1238070654) (.leaf 1208102118)) (.branch 51 (.leaf 1178988801) (.leaf 1150700219)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1123207237) (.leaf 1096481992)) (.branch 55 (.leaf 1070497833) (.leaf 1045229257))) (.branch 58 (.branch 57 (.leaf 1020651853) (.leaf 996742245)) (.branch 59 (.leaf 973478040) (.leaf 950837780))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 928800896) (.branch 62 (.leaf 907347665) (.leaf 886459167))) (.branch 65 (.branch 64 (.leaf 866117247) (.leaf 846304478)) (.branch 66 (.leaf 827004127) (.leaf 808200119)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 789877011) (.leaf 772019958)) (.branch 70 (.leaf 754614686) (.leaf 737647467))) (.branch 73 (.branch 72 (.leaf 721105093) (.leaf 704974851)) (.branch 74 (.leaf 689244503) (.leaf 673902263))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 658936775) (.branch 77 (.leaf 644337099) (.leaf 630092687))) (.branch 80 (.branch 79 (.leaf 616193369) (.leaf 602629334)) (.branch 81 (.leaf 589391120) (.leaf 576469590)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 563855927) (.leaf 551541615)) (.branch 85 (.leaf 539518429) (.leaf 527778419))) (.branch 88 (.branch 87 (.leaf 516313904) (.leaf 505117458)) (.branch 89 (.leaf 494181898) (.leaf 483500277)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 473065874) (.branch 92 (.leaf 462872183) (.leaf 452912907))) (.branch 95 (.branch 94 (.leaf 443181947) (.leaf 433673396)) (.branch 96 (.leaf 424381533) (.leaf 415300813)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 406425860) (.leaf 397751465)) (.branch 100 (.leaf 389272573) (.leaf 380984284))) (.branch 103 (.branch 102 (.leaf 372881842) (.leaf 364960633)) (.branch 104 (.leaf 357216179) (.leaf 349644131))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 342240268) (.leaf 335000489)) (.branch 108 (.leaf 327920811) (.leaf 320997364))) (.branch 111 (.branch 110 (.leaf 314226386) (.leaf 307604223)) (.branch 112 (.leaf 301127320) (.leaf 294792223)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 288595569) (.leaf 282534090)) (.branch 116 (.leaf 276604607) (.leaf 270804024))) (.branch 119 (.branch 118 (.leaf 265129331) (.leaf 259577595)) (.branch 120 (.leaf 254145965) (.leaf 248831660)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 262).prefactor = (2423396050999463/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 262).cutoff/(generalMeanRows 262).c)).2 =
    (385412199243929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 262).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 262).q*(generalMeanRows 262).c/2-2 = (102/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable107.value]
  have hcontinuation : (generalMeanRows 262).q*(generalMeanRows 262).cutoff/2-2 = (2138/999:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable120.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 262).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 262).criticalRate j.val*(generalMeanRows 262).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 262).c*(generalMeanRows 262).criticalPoint j.val)).2-
      (generalMeanRows 262).J/2-(generalMeanRows 262).error (generalMeanGrid j.val)+
      (generalMeanRows 262).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 262).c)).2-
      (generalMeanRows 262).J/2-(generalMeanRows 262).error 4 := by
  have he : (generalMeanRows 262).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 262) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 262)
    (generalMeanRows_prefactorDomain 262) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0262

/-! Kernel-checked entropy margins for general spectral rectangle 263. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0263
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4992685723) (.branch 2 (.leaf 4818439308) (.leaf 4652162532))) (.branch 5 (.branch 4 (.leaf 4493393806) (.leaf 4341704362)) (.branch 6 (.leaf 4196695393) (.leaf 4057995500)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3925258399) (.leaf 3798160868)) (.branch 10 (.leaf 3676400898) (.leaf 3559696023))) (.branch 13 (.branch 12 (.leaf 3447781805) (.leaf 3340410467)) (.branch 14 (.leaf 3237349650) (.leaf 3138381270))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3043300492) (.branch 17 (.leaf 2951914780) (.leaf 2864043031))) (.branch 20 (.branch 19 (.leaf 2779514781) (.leaf 2698169477)) (.branch 21 (.leaf 2619855803) (.leaf 2544431067)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2471760625) (.leaf 2401717360)) (.branch 25 (.leaf 2334181192) (.leaf 2269038629))) (.branch 28 (.branch 27 (.leaf 2206182353) (.leaf 2145510827)) (.branch 29 (.leaf 2086927939) (.leaf 2030342671)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1975668783) (.branch 32 (.leaf 1922824531) (.leaf 1871732389))) (.branch 35 (.branch 34 (.leaf 1822318809) (.leaf 1774513976)) (.branch 36 (.leaf 1728251600) (.leaf 1683468702)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1640105431) (.leaf 1598104882)) (.branch 40 (.leaf 1557412929) (.leaf 1517978070))) (.branch 43 (.branch 42 (.leaf 1479751277) (.leaf 1442685865)) (.branch 44 (.leaf 1406737356) (.leaf 1371863363))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1338023474) (.branch 47 (.leaf 1305179146) (.leaf 1273293606))) (.branch 50 (.branch 49 (.leaf 1242331752) (.leaf 1212260073)) (.branch 51 (.leaf 1183046555) (.leaf 1154660612)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1127073007) (.leaf 1100255780)) (.branch 55 (.leaf 1074182191) (.leaf 1048826648))) (.branch 58 (.branch 57 (.leaf 1024164656) (.leaf 1000172757)) (.branch 59 (.leaf 976828483) (.leaf 954110301))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 931997573) (.branch 62 (.leaf 910470506) (.leaf 889510115))) (.branch 65 (.branch 64 (.leaf 869098184) (.leaf 849217225)) (.branch 66 (.leaf 829850447) (.leaf 810981721)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 792595550) (.leaf 774677038)) (.branch 70 (.leaf 757211862) (.leaf 740186246))) (.branch 73 (.branch 72 (.leaf 723586938) (.leaf 707401180)) (.branch 74 (.leaf 691616693) (.leaf 676221649))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 661204654) (.branch 77 (.leaf 646554730) (.leaf 632261293))) (.branch 80 (.branch 79 (.leaf 618314136) (.leaf 604703419)) (.branch 81 (.leaf 591419641) (.leaf 578453639)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 565796564) (.leaf 553439869)) (.branch 85 (.leaf 541375302) (.leaf 529594887))) (.branch 88 (.branch 87 (.leaf 518090914) (.leaf 506855933)) (.branch 89 (.leaf 495882736) (.leaf 485164352)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 474694037) (.branch 92 (.leaf 464465262) (.leaf 454471708))) (.branch 95 (.branch 94 (.leaf 444707257) (.leaf 435165981)) (.branch 96 (.leaf 425842138) (.leaf 416730164)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 407824666) (.leaf 399120416)) (.branch 100 (.leaf 390612342) (.leaf 382295526))) (.branch 103 (.branch 102 (.leaf 374165198) (.leaf 366216727)) (.branch 104 (.leaf 358445618) (.leaf 350847510))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 343418165) (.leaf 336153468)) (.branch 108 (.leaf 329049424) (.leaf 322102148))) (.branch 111 (.branch 110 (.leaf 315307867) (.leaf 308662912)) (.branch 112 (.leaf 302163718) (.leaf 295806816)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 289588835) (.leaf 283506495)) (.branch 116 (.leaf 277556604) (.leaf 271736057))) (.branch 119 (.branch 118 (.leaf 266041833) (.leaf 260470990)) (.branch 120 (.leaf 255020665) (.leaf 249688070)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 263).prefactor = (607934178041811/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 263).cutoff/(generalMeanRows 263).c)).2 =
    (385412199243929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 263).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 263).q*(generalMeanRows 263).c/2-2 = (102/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable107.value]
  have hcontinuation : (generalMeanRows 263).q*(generalMeanRows 263).cutoff/2-2 = (2138/999:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable120.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 263).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 263).criticalRate j.val*(generalMeanRows 263).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 263).c*(generalMeanRows 263).criticalPoint j.val)).2-
      (generalMeanRows 263).J/2-(generalMeanRows 263).error (generalMeanGrid j.val)+
      (generalMeanRows 263).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 263).c)).2-
      (generalMeanRows 263).J/2-(generalMeanRows 263).error 4 := by
  have he : (generalMeanRows 263).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 263) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 263)
    (generalMeanRows_prefactorDomain 263) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0263

/-! Kernel-checked entropy margins for general spectral rectangle 264. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0264
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4928668511) (.branch 2 (.leaf 4754282784) (.leaf 4587888583))) (.branch 5 (.branch 4 (.leaf 4429024430) (.leaf 4277261583)) (.branch 6 (.leaf 4132201187) (.leaf 3993471720)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3860726719) (.leaf 3733642727)) (.branch 10 (.leaf 3611917448) (.leaf 3495268087))) (.branch 13 (.branch 12 (.leaf 3383429840) (.leaf 3276154529)) (.branch 14 (.leaf 3173209365) (.leaf 3074375809))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2979448550) (.branch 17 (.leaf 2888234556) (.leaf 2800552216))) (.branch 20 (.branch 19 (.leaf 2716230545) (.leaf 2635108456)) (.branch 21 (.leaf 2557034098) (.leaf 2481864233)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2409463672) (.leaf 2339704749)) (.branch 25 (.leaf 2272466836) (.leaf 2207635897))) (.branch 28 (.branch 27 (.leaf 2145104068) (.leaf 2084769273)) (.branch 29 (.leaf 2026534869) (.leaf 1970309307)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1916005828) (.branch 32 (.leaf 1863542172) (.leaf 1812840311))) (.branch 35 (.branch 34 (.leaf 1763826198) (.leaf 1716429532)) (.branch 36 (.leaf 1670583544) (.leaf 1626224790)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1583292959) (.leaf 1541730701)) (.branch 40 (.leaf 1501483452) (.leaf 1462499287))) (.branch 43 (.branch 42 (.leaf 1424728763) (.leaf 1388124791)) (.branch 44 (.leaf 1352642502) (.leaf 1318239127))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1284873885) (.branch 47 (.leaf 1252507873) (.leaf 1221103970))) (.branch 50 (.branch 49 (.leaf 1190626739) (.leaf 1161042339)) (.branch 51 (.leaf 1132318443) (.leaf 1104424158)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1077329952) (.leaf 1051007582)) (.branch 55 (.leaf 1025430031) (.leaf 1000571444))) (.branch 58 (.branch 57 (.leaf 976407068) (.leaf 952913203)) (.branch 59 (.leaf 930067141) (.leaf 907847123))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 886232292) (.branch 62 (.leaf 865202647) (.leaf 844739000))) (.branch 65 (.branch 64 (.leaf 824822941) (.leaf 805436799)) (.branch 66 (.leaf 786563605) (.leaf 768187061)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 750291507) (.leaf 732861893)) (.branch 70 (.leaf 715883748) (.leaf 699343157))) (.branch 73 (.branch 72 (.leaf 683226731) (.leaf 667521587)) (.branch 74 (.leaf 652215322) (.leaf 637295995))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 622752103) (.branch 77 (.leaf 608572562) (.leaf 594746691))) (.branch 80 (.branch 79 (.leaf 581264193) (.leaf 568115135)) (.branch 81 (.leaf 555289940) (.leaf 542779363)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 530574482) (.leaf 518666685)) (.branch 85 (.leaf 507047654) (.leaf 495709353))) (.branch 88 (.branch 87 (.leaf 484644018) (.leaf 473844145)) (.branch 89 (.leaf 463302481) (.leaf 453012010)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 442965946) (.branch 92 (.leaf 433157726) (.leaf 423580994))) (.branch 95 (.branch 94 (.leaf 414229602) (.leaf 405097596)) (.branch 96 (.leaf 396179208) (.leaf 387468852)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 378961117) (.leaf 370650756)) (.branch 100 (.leaf 362532686) (.leaf 354601976))) (.branch 103 (.branch 102 (.leaf 346853846) (.leaf 339283659)) (.branch 104 (.leaf 331886914) (.leaf 324659247))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 317596420) (.leaf 310694318)) (.branch 108 (.leaf 303948949) (.leaf 297356432))) (.branch 111 (.branch 110 (.leaf 290912999) (.leaf 284614991)) (.branch 112 (.leaf 278458849) (.leaf 272441116)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 266558433) (.leaf 260807531)) (.branch 116 (.leaf 255185235) (.leaf 249688454))) (.branch 119 (.branch 118 (.leaf 244314182) (.leaf 239059497)) (.branch 120 (.leaf 233921553) (.leaf 228897582)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 264).prefactor = (4865446377026529/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 264).cutoff/(generalMeanRows 264).c)).2 =
    (374631555805619/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 264).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 264).q*(generalMeanRows 264).c/2-2 = (419/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable106.value]
  have hcontinuation : (generalMeanRows 264).q*(generalMeanRows 264).cutoff/2-2 = (1066/501:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable119.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 264).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 264).criticalRate j.val*(generalMeanRows 264).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 264).c*(generalMeanRows 264).criticalPoint j.val)).2-
      (generalMeanRows 264).J/2-(generalMeanRows 264).error (generalMeanGrid j.val)+
      (generalMeanRows 264).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 264).c)).2-
      (generalMeanRows 264).J/2-(generalMeanRows 264).error 4 := by
  have he : (generalMeanRows 264).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 264) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 264)
    (generalMeanRows_prefactorDomain 264) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0264

/-! Kernel-checked entropy margins for general spectral rectangle 265. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0265
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4945768466) (.branch 2 (.leaf 4770777710) (.leaf 4603806206))) (.branch 5 (.branch 4 (.leaf 4444390876) (.leaf 4292101490)) (.branch 6 (.leaf 4146537808) (.leaf 4007327021)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3874121463) (.leaf 3746596554)) (.branch 10 (.leaf 3624448951) (.leaf 3507394877))) (.branch 13 (.branch 12 (.leaf 3395168608) (.leaf 3287521107)) (.branch 14 (.leaf 3184218775) (.leaf 3085042318))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2989785710) (.branch 17 (.leaf 2898255250) (.leaf 2810268698))) (.branch 20 (.branch 19 (.leaf 2725654473) (.leaf 2644250933)) (.branch 21 (.leaf 2565905697) (.leaf 2490475031)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2417823277) (.leaf 2347822326)) (.branch 25 (.leaf 2280351132) (.leaf 2215295263))) (.branch 28 (.branch 27 (.leaf 2152546480) (.leaf 2092002355)) (.branch 29 (.leaf 2033565907) (.leaf 1977145271)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1922653387) (.branch 32 (.leaf 1870007709) (.leaf 1819129939))) (.branch 35 (.branch 34 (.leaf 1769945771) (.leaf 1722384664)) (.branch 36 (.leaf 1676379613) (.leaf 1631866957)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1588786175) (.leaf 1547079716)) (.branch 40 (.leaf 1506692831) (.leaf 1467573410))) (.branch 43 (.branch 42 (.leaf 1429671842) (.leaf 1392940873)) (.branch 44 (.leaf 1357335478) (.leaf 1322812742))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1289331739) (.branch 47 (.leaf 1256853434) (.leaf 1225340576))) (.branch 50 (.branch 49 (.leaf 1194757604) (.leaf 1165070561)) (.branch 51 (.leaf 1136247008) (.leaf 1108255944)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1081067735) (.leaf 1054654040)) (.branch 55 (.leaf 1028987748) (.leaf 1004042914))) (.branch 58 (.branch 57 (.leaf 979794701) (.leaf 956219323)) (.branch 59 (.leaf 933293997) (.leaf 910996888))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 889307065) (.branch 62 (.leaf 868204457) (.leaf 847669812))) (.branch 65 (.branch 64 (.leaf 827684655) (.leaf 808231252)) (.branch 66 (.leaf 789292578) (.leaf 770852277)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 752894634) (.leaf 735404548)) (.branch 70 (.leaf 718367498) (.leaf 701769520))) (.branch 73 (.branch 72 (.leaf 685597178) (.leaf 669837545)) (.branch 74 (.leaf 654478175) (.leaf 639507086))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 624912734) (.branch 77 (.leaf 610683997) (.leaf 596810158))) (.branch 80 (.branch 79 (.leaf 583280882) (.leaf 570086204)) (.branch 81 (.leaf 557216512) (.leaf 544662529)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 532415304) (.leaf 520466193)) (.branch 85 (.leaf 508806849) (.leaf 497429210))) (.branch 88 (.branch 87 (.leaf 486325484) (.leaf 475488142)) (.branch 89 (.leaf 464909903) (.leaf 454583730)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 444502811) (.branch 92 (.leaf 434660561) (.leaf 425050603))) (.branch 95 (.branch 94 (.leaf 415666767) (.leaf 406503077)) (.branch 96 (.leaf 397553746) (.leaf 388813170)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 380275917) (.leaf 371936724)) (.branch 100 (.leaf 363790489) (.leaf 355832263))) (.branch 103 (.branch 102 (.leaf 348057251) (.leaf 340460799)) (.branch 104 (.leaf 333038392) (.leaf 325785648))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 318698317) (.leaf 311772269)) (.branch 108 (.leaf 305003496) (.leaf 298388106))) (.branch 111 (.branch 110 (.leaf 291922319) (.leaf 285602459)) (.branch 112 (.leaf 279424958) (.leaf 273386348)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 267483254) (.leaf 261712400)) (.branch 116 (.leaf 256070597) (.leaf 250554745))) (.branch 119 (.branch 118 (.leaf 245161827) (.leaf 239888911)) (.branch 120 (.leaf 234733141) (.leaf 229691740)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 265).prefactor = (4882326983372843/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 265).cutoff/(generalMeanRows 265).c)).2 =
    (374631555805619/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 265).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 265).q*(generalMeanRows 265).c/2-2 = (419/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable106.value]
  have hcontinuation : (generalMeanRows 265).q*(generalMeanRows 265).cutoff/2-2 = (1066/501:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable119.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 265).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 265).criticalRate j.val*(generalMeanRows 265).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 265).c*(generalMeanRows 265).criticalPoint j.val)).2-
      (generalMeanRows 265).J/2-(generalMeanRows 265).error (generalMeanGrid j.val)+
      (generalMeanRows 265).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 265).c)).2-
      (generalMeanRows 265).J/2-(generalMeanRows 265).error 4 := by
  have he : (generalMeanRows 265).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 265) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 265)
    (generalMeanRows_prefactorDomain 265) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0265

/-! Kernel-checked entropy margins for general spectral rectangle 266. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0266
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4849452847) (.branch 2 (.leaf 4675575255) (.leaf 4509682241))) (.branch 5 (.branch 4 (.leaf 4351314025) (.leaf 4200043372)) (.branch 6 (.leaf 4055472751) (.leaf 3917231809)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3784975099) (.leaf 3658380049)) (.branch 10 (.leaf 3537145131) (.leaf 3420988204))) (.branch 13 (.branch 12 (.leaf 3309645020) (.leaf 3202867870)) (.branch 14 (.leaf 3100424347) (.leaf 3002096226))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2907678440) (.branch 17 (.leaf 2816978145) (.leaf 2729813859))) (.branch 20 (.branch 19 (.leaf 2646014682) (.leaf 2565419568)) (.branch 21 (.leaf 2487876667) (.leaf 2413242708)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2341382439) (.leaf 2272168104)) (.branch 25 (.leaf 2205478960) (.leaf 2141200836))) (.branch 28 (.branch 27 (.leaf 2079225714) (.leaf 2019451351)) (.branch 29 (.leaf 1961780918) (.leaf 1906122674)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1852389656) (.branch 32 (.leaf 1800499391) (.leaf 1750373634))) (.branch 35 (.branch 34 (.leaf 1701938114) (.leaf 1655122304)) (.branch 36 (.leaf 1609859204) (.leaf 1566085139)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1523739568) (.leaf 1482764907)) (.branch 40 (.leaf 1443106365) (.leaf 1404711784))) (.branch 43 (.branch 42 (.leaf 1367531497) (.leaf 1331518190)) (.branch 44 (.leaf 1296626773) (.leaf 1262814262))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1230039660) (.branch 47 (.leaf 1198263858) (.leaf 1167449530))) (.branch 50 (.branch 49 (.leaf 1137561038) (.leaf 1108564350)) (.branch 51 (.leaf 1080426948) (.leaf 1053117757)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1026607065) (.leaf 1000866458)) (.branch 55 (.leaf 975868751) (.leaf 951587927))) (.branch 58 (.branch 57 (.leaf 927999080) (.leaf 905078357)) (.branch 59 (.leaf 882802908) (.leaf 861150834))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 840101145) (.branch 62 (.leaf 819633712) (.leaf 799729225))) (.branch 65 (.branch 64 (.leaf 780369158) (.leaf 761535727)) (.branch 66 (.leaf 743211858) (.leaf 725381151)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 708027852) (.leaf 691136817)) (.branch 70 (.leaf 674693492) (.leaf 658683878))) (.branch 73 (.branch 72 (.leaf 643094510) (.leaf 627912434)) (.branch 74 (.leaf 613125178) (.leaf 598720738))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 584687551) (.branch 77 (.leaf 571014479) (.leaf 557690789))) (.branch 80 (.branch 79 (.leaf 544706136) (.leaf 532050547)) (.branch 81 (.leaf 519714400) (.leaf 507688417)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 495963643) (.leaf 484531435)) (.branch 85 (.leaf 473383448) (.leaf 462511624))) (.branch 88 (.branch 87 (.leaf 451908179) (.leaf 441565592)) (.branch 89 (.leaf 431476593) (.leaf 421634155)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 412031483) (.branch 92 (.leaf 402662006) (.leaf 393519365))) (.branch 95 (.branch 94 (.leaf 384597409) (.leaf 375890183)) (.branch 96 (.leaf 367391923) (.leaf 359097047)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 351000148) (.leaf 343095990)) (.branch 100 (.leaf 335379497) (.leaf 327845751))) (.branch 103 (.branch 102 (.leaf 320489985) (.leaf 313307576)) (.branch 104 (.leaf 306294040) (.leaf 299445030))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 292756328) (.leaf 286223839)) (.branch 108 (.leaf 279843591) (.leaf 273611728))) (.branch 111 (.branch 110 (.leaf 267524505) (.leaf 261578286)) (.branch 112 (.leaf 255769541) (.leaf 250094839)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 244550846) (.leaf 239134325)) (.branch 116 (.leaf 233842129) (.leaf 228671196))) (.branch 119 (.branch 118 (.leaf 223618553) (.leaf 218681308)) (.branch 120 (.leaf 213856648) (.leaf 209141836)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 266).prefactor = (9700870072559/2000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 266).cutoff/(generalMeanRows 266).c)).2 =
    (181959985431671/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 266).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 266).q*(generalMeanRows 266).c/2-2 = (43/50:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable020.value]
  have hcontinuation : (generalMeanRows 266).q*(generalMeanRows 266).cutoff/2-2 = (2126/1005:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable121.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 266).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 266).criticalRate j.val*(generalMeanRows 266).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 266).c*(generalMeanRows 266).criticalPoint j.val)).2-
      (generalMeanRows 266).J/2-(generalMeanRows 266).error (generalMeanGrid j.val)+
      (generalMeanRows 266).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 266).c)).2-
      (generalMeanRows 266).J/2-(generalMeanRows 266).error 4 := by
  have he : (generalMeanRows 266).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 266) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 266)
    (generalMeanRows_prefactorDomain 266) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0266

/-! Kernel-checked entropy margins for general spectral rectangle 267. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0267
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4921815321) (.branch 2 (.leaf 4747702718) (.leaf 4581561214))) (.branch 5 (.branch 4 (.leaf 4422931063) (.leaf 4271385110)) (.branch 6 (.leaf 4126525950) (.leaf 3987983394)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3855412196) (.leaf 3728490014)) (.branch 10 (.leaf 3606915577) (.leaf 3490407025))) (.branch 13 (.branch 12 (.leaf 3378700413) (.leaf 3271548351)) (.branch 14 (.leaf 3168718766) (.leaf 3069993783))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2975168693) (.branch 17 (.leaf 2884051019) (.leaf 2796459655))) (.branch 20 (.branch 19 (.leaf 2712224078) (.leaf 2631183628)) (.branch 21 (.leaf 2553186839) (.leaf 2478090827)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2405760727) (.leaf 2336069168)) (.branch 25 (.leaf 2268895793) (.leaf 2204126810))) (.branch 28 (.branch 27 (.leaf 2141654580) (.leaf 2081377231)) (.branch 29 (.leaf 2023198304) (.leaf 1967026420)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1912774974) (.branch 32 (.leaf 1860361844) (.leaf 1809709129))) (.branch 35 (.branch 34 (.leaf 1760742896) (.leaf 1713392947)) (.branch 36 (.leaf 1667592608) (.leaf 1623278517)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1580390442) (.leaf 1538871099)) (.branch 40 (.leaf 1498665987) (.leaf 1459723235))) (.branch 43 (.branch 42 (.leaf 1421993450) (.leaf 1385429588)) (.branch 44 (.leaf 1349986819) (.leaf 1315622408))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1282295605) (.branch 47 (.leaf 1249967537) (.leaf 1218601105))) (.branch 50 (.branch 49 (.leaf 1188160893) (.leaf 1158613081)) (.branch 51 (.leaf 1129925356) (.leaf 1102066842)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1075008017) (.leaf 1048720650)) (.branch 55 (.leaf 1023177732) (.leaf 998353415))) (.branch 58 (.branch 57 (.leaf 974222956) (.leaf 950762656)) (.branch 59 (.leaf 927949815) (.leaf 905762677))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 884180387) (.branch 62 (.leaf 863182945) (.leaf 842751168))) (.branch 65 (.branch 64 (.leaf 822866646) (.leaf 803511707)) (.branch 66 (.leaf 784669386) (.leaf 766323382)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 748458038) (.leaf 731058302)) (.branch 70 (.leaf 714109704) (.leaf 697598328))) (.branch 73 (.branch 72 (.leaf 681510784) (.leaf 665834190)) (.branch 74 (.leaf 650556143) (.leaf 635664700))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 621148358) (.branch 77 (.leaf 606996034) (.leaf 593197046))) (.branch 80 (.branch 79 (.leaf 579741096) (.leaf 566618253)) (.branch 81 (.leaf 553818937) (.leaf 541333906)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 529154239) (.leaf 517271321)) (.branch 85 (.leaf 505676836) (.leaf 494362749))) (.branch 88 (.branch 87 (.leaf 483321298) (.leaf 472544979)) (.branch 89 (.leaf 462026538) (.leaf 451758963)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 441735468) (.branch 92 (.leaf 431949490) (.leaf 422394678))) (.branch 95 (.branch 94 (.leaf 413064883) (.leaf 403954153)) (.branch 96 (.leaf 395056722) (.leaf 386367007)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 377879598) (.leaf 369589251)) (.branch 100 (.leaf 361490885) (.leaf 353579570))) (.branch 103 (.branch 102 (.leaf 345850530) (.leaf 338299130)) (.branch 104 (.leaf 330920872) (.leaf 323711394))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 316666460) (.leaf 309781961)) (.branch 108 (.leaf 303053903) (.leaf 296478412))) (.branch 111 (.branch 110 (.leaf 290051722) (.leaf 283770175)) (.branch 112 (.leaf 277630217) (.leaf 271628395)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 265761350) (.leaf 260025819)) (.branch 116 (.leaf 254418628) (.leaf 248936690))) (.branch 119 (.branch 118 (.leaf 243577004) (.leaf 238336649)) (.branch 120 (.leaf 233212783) (.leaf 228202642)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 267).prefactor = (303095762784639/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 267).cutoff/(generalMeanRows 267).c)).2 =
    (93283917303509/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 267).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 267).q*(generalMeanRows 267).c/2-2 = (419/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable106.value]
  have hcontinuation : (generalMeanRows 267).q*(generalMeanRows 267).cutoff/2-2 = (4258/2007:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable122.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 267).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 267).criticalRate j.val*(generalMeanRows 267).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 267).c*(generalMeanRows 267).criticalPoint j.val)).2-
      (generalMeanRows 267).J/2-(generalMeanRows 267).error (generalMeanGrid j.val)+
      (generalMeanRows 267).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 267).c)).2-
      (generalMeanRows 267).J/2-(generalMeanRows 267).error 4 := by
  have he : (generalMeanRows 267).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 267) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 267)
    (generalMeanRows_prefactorDomain 267) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0267

/-! Kernel-checked entropy margins for general spectral rectangle 268. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0268
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4847720963) (.branch 2 (.leaf 4673869288) (.leaf 4508008953))) (.branch 5 (.branch 4 (.leaf 4349679240) (.leaf 4198452065)) (.branch 6 (.leaf 4053929130) (.leaf 3915739389)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3783536773) (.leaf 3656998149)) (.branch 10 (.leaf 3535821483) (.leaf 3419724183))) (.branch 13 (.branch 12 (.leaf 3308441595) (.leaf 3201725649)) (.branch 14 (.leaf 3099343616) (.leaf 3001076985))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2906720436) (.branch 17 (.leaf 2816080899) (.leaf 2728976699))) (.branch 20 (.branch 19 (.leaf 2645236762) (.leaf 2564699895)) (.branch 21 (.leaf 2487214118) (.leaf 2412636050)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2340830346) (.leaf 2271669171)) (.branch 25 (.leaf 2205031720) (.leaf 2140803769))) (.branch 28 (.branch 27 (.leaf 2078877259) (.leaf 2019149916)) (.branch 29 (.leaf 1961524891) (.leaf 1905910429)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1852219560) (.branch 32 (.leaf 1800369814) (.leaf 1750282949))) (.branch 35 (.branch 34 (.leaf 1701884706) (.leaf 1655104575)) (.branch 36 (.leaf 1609875576) (.leaf 1566134056)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1523819500) (.leaf 1482874354)) (.branch 40 (.leaf 1443243856) (.leaf 1404875882))) (.branch 43 (.branch 42 (.leaf 1367720799) (.leaf 1331731330)) (.branch 44 (.leaf 1296862420) (.leaf 1263071122))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1230316478) (.branch 47 (.leaf 1198559417) (.leaf 1167762651))) (.branch 50 (.branch 49 (.leaf 1137890583) (.leaf 1108909216)) (.branch 51 (.leaf 1080786073) (.leaf 1053490116)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1026991672) (.leaf 1001262362)) (.branch 55 (.leaf 976275040) (.leaf 952003724))) (.branch 58 (.branch 57 (.leaf 928423543) (.leaf 905510680)) (.branch 59 (.leaf 883242318) (.leaf 861596592))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 840552544) (.branch 62 (.leaf 820090076) (.leaf 800189910))) (.branch 65 (.branch 64 (.leaf 780833549) (.leaf 762003240)) (.branch 66 (.leaf 743681935) (.leaf 725853263)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 708501495) (.leaf 691611514)) (.branch 70 (.leaf 675168790) (.leaf 659159348))) (.branch 73 (.branch 72 (.leaf 643569748) (.leaf 628387055)) (.branch 74 (.leaf 613598822) (.leaf 599193063))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 585158237) (.branch 77 (.leaf 571483224) (.leaf 558157310))) (.branch 80 (.branch 79 (.leaf 545170168) (.leaf 532511841)) (.branch 81 (.leaf 520172724) (.leaf 508143554)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 496415392) (.leaf 484979609)) (.branch 85 (.leaf 473827875) (.leaf 462952143))) (.branch 88 (.branch 87 (.leaf 452344642) (.leaf 441997862)) (.branch 89 (.leaf 431904547) (.leaf 422057680)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 412450477) (.branch 92 (.leaf 403076375) (.leaf 393929026))) (.branch 95 (.branch 94 (.leaf 385002287) (.leaf 376290212)) (.branch 96 (.leaf 367787045) (.leaf 359487212)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 351385313) (.leaf 343476119)) (.branch 100 (.leaf 335754561) (.leaf 328215726))) (.branch 103 (.branch 102 (.leaf 320854854) (.leaf 313667326)) (.branch 104 (.leaf 306648666) (.leaf 299794530))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 293100704) (.leaf 286563099)) (.branch 108 (.leaf 280177746) (.leaf 273940793))) (.branch 111 (.branch 110 (.leaf 267848499) (.leaf 261897232)) (.branch 112 (.leaf 256083463) (.leaf 250403765)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 244854808) (.leaf 239433357)) (.branch 116 (.leaf 234136265) (.leaf 228960476))) (.branch 119 (.branch 118 (.leaf 223903016) (.leaf 218960997)) (.branch 120 (.leaf 214131605) (.leaf 209412108)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 268).prefactor = (2428985777495039/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 268).cutoff/(generalMeanRows 268).c)).2 =
    (91353405780031/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 268).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 268).q*(generalMeanRows 268).c/2-2 = (43/50:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable020.value]
  have hcontinuation : (generalMeanRows 268).q*(generalMeanRows 268).cutoff/2-2 = (4258/2007:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable122.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 268).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 268).criticalRate j.val*(generalMeanRows 268).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 268).c*(generalMeanRows 268).criticalPoint j.val)).2-
      (generalMeanRows 268).J/2-(generalMeanRows 268).error (generalMeanGrid j.val)+
      (generalMeanRows 268).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 268).c)).2-
      (generalMeanRows 268).J/2-(generalMeanRows 268).error 4 := by
  have he : (generalMeanRows 268).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 268) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 268)
    (generalMeanRows_prefactorDomain 268) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0268

/-! Kernel-checked entropy margins for general spectral rectangle 269. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0269
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4857926226) (.branch 2 (.leaf 4683744820) (.leaf 4517561943))) (.branch 5 (.branch 4 (.leaf 4358917013) (.leaf 4207382047)) (.branch 6 (.leaf 4062558820) (.leaf 3924076331)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3791588530) (.leaf 3664772283)) (.branch 10 (.leaf 3543325533) (.leaf 3426965647))) (.branch 13 (.branch 12 (.leaf 3315427915) (.leaf 3208464195)) (.branch 14 (.leaf 3105841673) (.leaf 3007341745))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2912758984) (.branch 17 (.leaf 2821900210) (.leaf 2734583623))) (.branch 20 (.branch 19 (.leaf 2650638025) (.leaf 2569902089)) (.branch 21 (.leaf 2492223698) (.leaf 2417459332)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2345473503) (.leaf 2276138230)) (.branch 25 (.leaf 2209332561) (.leaf 2144942125))) (.branch 28 (.branch 27 (.leaf 2082858715) (.leaf 2022979909)) (.branch 29 (.leaf 1965208709) (.leaf 1909453215)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1855626309) (.branch 32 (.leaf 1803645378) (.leaf 1753432037))) (.branch 35 (.branch 34 (.leaf 1704911885) (.leaf 1658014275)) (.branch 36 (.leaf 1612672087) (.leaf 1568821536)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1526401976) (.leaf 1485355721)) (.branch 40 (.leaf 1445627884) (.leaf 1407166216))) (.branch 43 (.branch 42 (.leaf 1369920965) (.leaf 1333844732)) (.branch 44 (.leaf 1298892351) (.leaf 1265020759))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1232188891) (.branch 47 (.leaf 1200357567) (.leaf 1169489397))) (.branch 50 (.branch 49 (.leaf 1139548682) (.leaf 1110501328)) (.branch 51 (.leaf 1082314762) (.leaf 1054957854)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1028400840) (.leaf 1002615257)) (.branch 55 (.leaf 977573872) (.leaf 953250623))) (.branch 58 (.branch 57 (.leaf 929620559) (.leaf 906659787)) (.branch 59 (.leaf 884345416) (.leaf 862655510))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 841569042) (.branch 62 (.leaf 821065846) (.leaf 801126580))) (.branch 65 (.branch 64 (.leaf 781732685) (.leaf 762866347)) (.branch 66 (.leaf 744510461) (.leaf 726648599)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 709264978) (.leaf 692344430)) (.branch 70 (.leaf 675872374) (.leaf 659834786))) (.branch 73 (.branch 72 (.leaf 644218180) (.leaf 629009576)) (.branch 74 (.leaf 614196483) (.leaf 599766874))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 585709167) (.branch 77 (.leaf 572012204) (.leaf 558665234))) (.branch 80 (.branch 79 (.leaf 545657893) (.leaf 532980191)) (.branch 81 (.leaf 520622489) (.leaf 508575493)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 496830233) (.leaf 485378049)) (.branch 85 (.leaf 474210584) (.leaf 463319764))) (.branch 88 (.branch 87 (.leaf 452697792) (.leaf 442337133)) (.branch 89 (.leaf 432230505) (.leaf 422370870)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 412751419) (.branch 92 (.leaf 403365571) (.leaf 394206956))) (.branch 95 (.branch 94 (.leaf 385269411) (.leaf 376546971)) (.branch 96 (.leaf 368033862) (.leaf 359724492)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 351613446) (.leaf 343695477)) (.branch 100 (.leaf 335965501) (.leaf 328418591))) (.branch 103 (.branch 102 (.leaf 321049972) (.leaf 313855013)) (.branch 104 (.leaf 306829223) (.leaf 299968246))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 293267857) (.leaf 286723954)) (.branch 108 (.leaf 280332558) (.leaf 274089806))) (.branch 111 (.branch 110 (.leaf 267991947) (.leaf 262035338)) (.branch 112 (.leaf 256216444) (.leaf 250531826)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 244978146) (.leaf 239552161)) (.branch 116 (.leaf 234250718) (.leaf 229070750))) (.branch 119 (.branch 118 (.leaf 224009279) (.leaf 219063407)) (.branch 120 (.leaf 214230316) (.leaf 209507267)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 269).prefactor = (2429455065413449/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 269).cutoff/(generalMeanRows 269).c)).2 =
    (181959985431671/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 269).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 269).q*(generalMeanRows 269).c/2-2 = (43/50:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable020.value]
  have hcontinuation : (generalMeanRows 269).q*(generalMeanRows 269).cutoff/2-2 = (2126/1005:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable121.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 269).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 269).criticalRate j.val*(generalMeanRows 269).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 269).c*(generalMeanRows 269).criticalPoint j.val)).2-
      (generalMeanRows 269).J/2-(generalMeanRows 269).error (generalMeanGrid j.val)+
      (generalMeanRows 269).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 269).c)).2-
      (generalMeanRows 269).J/2-(generalMeanRows 269).error 4 := by
  have he : (generalMeanRows 269).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 269) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 269)
    (generalMeanRows_prefactorDomain 269) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0269

/-! Kernel-checked entropy margins for general spectral rectangle 270. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0270
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4866414410) (.branch 2 (.leaf 4691928659) (.leaf 4525455413))) (.branch 5 (.branch 4 (.leaf 4366533285) (.leaf 4214733544)) (.branch 6 (.leaf 4069657270) (.leaf 3930932812)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3798213518) (.leaf 3671175687)) (.branch 10 (.leaf 3549516734) (.leaf 3432953534))) (.branch 13 (.branch 12 (.leaf 3321220914) (.leaf 3214070297)) (.branch 14 (.leaf 3111268465) (.leaf 3012596429))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2917848406) (.branch 17 (.leaf 2826830875) (.leaf 2739361721))) (.branch 20 (.branch 19 (.leaf 2655269446) (.leaf 2574392441)) (.branch 21 (.leaf 2496578324) (.leaf 2421683324)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2349571714) (.leaf 2280115293)) (.branch 25 (.leaf 2213192896) (.leaf 2148689951))) (.branch 28 (.branch 27 (.leaf 2086498064) (.leaf 2026514632)) (.branch 29 (.leaf 1968642490) (.leaf 1912789574)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1858868618) (.branch 32 (.leaf 1806796861) (.leaf 1756495783))) (.branch 35 (.branch 34 (.leaf 1707890853) (.leaf 1660911299)) (.branch 36 (.leaf 1615489886) (.leaf 1571562716)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1529069036) (.leaf 1487951061)) (.branch 40 (.leaf 1448153808) (.leaf 1409624937))) (.branch 43 (.branch 42 (.leaf 1372314608) (.leaf 1336175340)) (.branch 44 (.leaf 1301161886) (.leaf 1267231111))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1234341876) (.branch 47 (.leaf 1202454935) (.leaf 1171532829))) (.branch 50 (.branch 49 (.leaf 1141539799) (.leaf 1112441691)) (.branch 51 (.leaf 1084205875) (.leaf 1056801167)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1030197750) (.leaf 1004367112)) (.branch 55 (.leaf 979281972) (.leaf 954916224))) (.branch 58 (.branch 57 (.leaf 931244872) (.leaf 908243981)) (.branch 59 (.leaf 885890620) (.leaf 864162816))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 843039503) (.branch 62 (.leaf 822500482) (.leaf 802526377))) (.branch 65 (.branch 64 (.leaf 783098596) (.leaf 764199293)) (.branch 66 (.leaf 745811333) (.leaf 727918262)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 710504267) (.leaf 693554154)) (.branch 70 (.leaf 677053316) (.leaf 660987706))) (.branch 73 (.branch 72 (.leaf 645343813) (.leaf 630108635)) (.branch 74 (.leaf 615269659) (.leaf 600814838))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 586732568) (.branch 77 (.leaf 573011673) (.leaf 559641382))) (.branch 80 (.branch 79 (.leaf 546611314) (.leaf 533911459)) (.branch 81 (.leaf 521532165) (.leaf 509464120)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 497698337) (.leaf 486226143)) (.branch 85 (.leaf 475039165) (.leaf 464129316))) (.branch 88 (.branch 87 (.leaf 453488784) (.leaf 443110022)) (.branch 89 (.leaf 432985735) (.leaf 423108872)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 413472614) (.branch 92 (.leaf 404070366) (.leaf 394895748))) (.branch 95 (.branch 94 (.leaf 385942586) (.leaf 377204906)) (.branch 96 (.leaf 368676922) (.leaf 360353033)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 352227815) (.leaf 344296011)) (.branch 100 (.leaf 336552528) (.leaf 328992432))) (.branch 103 (.branch 102 (.leaf 321610938) (.leaf 314403408)) (.branch 104 (.leaf 307365341) (.leaf 300492376))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 293780279) (.leaf 287224942)) (.branch 108 (.leaf 280822379) (.leaf 274568719))) (.branch 111 (.branch 110 (.leaf 268460205) (.leaf 262493189)) (.branch 112 (.leaf 256664127) (.leaf 250969576)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 245406193) (.leaf 239970727)) (.branch 116 (.leaf 234660020) (.leaf 229471002))) (.branch 119 (.branch 118 (.leaf 224400687) (.leaf 219446173)) (.branch 120 (.leaf 214604638) (.leaf 209873336)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 270).prefactor = (2433700016891831/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 270).cutoff/(generalMeanRows 270).c)).2 =
    (181959985431671/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 270).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 270).q*(generalMeanRows 270).c/2-2 = (43/50:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable020.value]
  have hcontinuation : (generalMeanRows 270).q*(generalMeanRows 270).cutoff/2-2 = (2126/1005:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable121.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 270).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 270).criticalRate j.val*(generalMeanRows 270).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 270).c*(generalMeanRows 270).criticalPoint j.val)).2-
      (generalMeanRows 270).J/2-(generalMeanRows 270).error (generalMeanGrid j.val)+
      (generalMeanRows 270).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 270).c)).2-
      (generalMeanRows 270).J/2-(generalMeanRows 270).error 4 := by
  have he : (generalMeanRows 270).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 270) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 270)
    (generalMeanRows_prefactorDomain 270) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0270

/-! Kernel-checked entropy margins for general spectral rectangle 271. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0271
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4859628230) (.branch 2 (.leaf 4685423338) (.leaf 4519210069))) (.branch 5 (.branch 4 (.leaf 4360528786) (.leaf 4208952360)) (.branch 6 (.leaf 4064083342) (.leaf 3925551426)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3793011193) (.leaf 3666140075)) (.branch 10 (.leaf 3544636523) (.leaf 3428218364))) (.branch 13 (.branch 12 (.leaf 3316621297) (.leaf 3209597545)) (.branch 14 (.leaf 3106914623) (.leaf 3008354215))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2913711155) (.branch 17 (.leaf 2822792487) (.leaf 2735416614))) (.branch 20 (.branch 19 (.leaf 2651412511) (.leaf 2570619005)) (.branch 21 (.leaf 2492884112) (.leaf 2418064424)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2346024548) (.leaf 2276636587)) (.branch 25 (.leaf 2209779655) (.leaf 2145339434))) (.branch 28 (.branch 27 (.leaf 2083207763) (.leaf 2023282250)) (.branch 29 (.leaf 1965465924) (.leaf 1909666897)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1855798063) (.branch 32 (.leaf 1803776807) (.leaf 1753524741))) (.branch 35 (.branch 34 (.leaf 1704967457) (.leaf 1658034290)) (.branch 36 (.leaf 1612658105) (.leaf 1568775094)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1526324586) (.leaf 1485248868)) (.branch 40 (.leaf 1445493023) (.leaf 1407004772))) (.branch 43 (.branch 42 (.leaf 1369734328) (.leaf 1333634259)) (.branch 44 (.leaf 1298659361) (.leaf 1264766537))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1231914684) (.branch 47 (.leaf 1200064584) (.leaf 1169178810))) (.branch 50 (.branch 49 (.leaf 1139221625) (.leaf 1110158896)) (.branch 51 (.leaf 1081958014) (.leaf 1054587810)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1028018484) (.leaf 1002221535)) (.branch 55 (.leaf 977169694) (.leaf 952836864))) (.branch 58 (.branch 57 (.leaf 929198060) (.leaf 906229352)) (.branch 59 (.leaf 883907817) (.leaf 862211485))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 841119297) (.branch 62 (.leaf 820611057) (.leaf 800667392))) (.branch 65 (.branch 64 (.leaf 781269712) (.leaf 762400175)) (.branch 66 (.leaf 744041648) (.leaf 726177675)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 708792447) (.leaf 691870771)) (.branch 70 (.leaf 675398041) (.leaf 659360209))) (.branch 73 (.branch 72 (.leaf 643743765) (.leaf 628535708)) (.branch 74 (.leaf 613723525) (.leaf 599295169))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 585239037) (.branch 77 (.leaf 571543953) (.leaf 558199146))) (.branch 80 (.branch 79 (.leaf 545194236) (.leaf 532519215)) (.branch 81 (.leaf 520164428) (.leaf 508120565)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 496378641) (.leaf 484929982)) (.branch 85 (.leaf 473766217) (.leaf 462879260))) (.branch 88 (.branch 87 (.leaf 452261299) (.leaf 441904789)) (.branch 89 (.leaf 431802436) (.leaf 421947190)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 412332235) (.branch 92 (.leaf 402950975) (.leaf 393797034))) (.branch 95 (.branch 94 (.leaf 384864239) (.leaf 376146617)) (.branch 96 (.leaf 367638386) (.leaf 359333945)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 351227872) (.leaf 343314914)) (.branch 100 (.leaf 335589979) (.leaf 328048136))) (.branch 103 (.branch 102 (.leaf 320684603) (.leaf 313494742)) (.branch 104 (.leaf 306474058) (.leaf 299618190))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 292922908) (.leaf 286384106)) (.branch 108 (.leaf 279997802) (.leaf 273760126))) (.branch 111 (.branch 110 (.leaf 267667326) (.leaf 261715756)) (.branch 112 (.leaf 255901875) (.leaf 250222244)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 244673521) (.leaf 239252459)) (.branch 116 (.leaf 233955904) (.leaf 228780787))) (.branch 119 (.branch 118 (.leaf 223724128) (.leaf 218783026)) (.branch 120 (.leaf 213954663) (.leaf 209236296)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 271).prefactor = (4851332677664933/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 271).cutoff/(generalMeanRows 271).c)).2 =
    (5662946035573/15625000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 271).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 271).q*(generalMeanRows 271).c/2-2 = (43/50:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable020.value]
  have hcontinuation : (generalMeanRows 271).q*(generalMeanRows 271).cutoff/2-2 = (386/183:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable123.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 271).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 271).criticalRate j.val*(generalMeanRows 271).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 271).c*(generalMeanRows 271).criticalPoint j.val)).2-
      (generalMeanRows 271).J/2-(generalMeanRows 271).error (generalMeanGrid j.val)+
      (generalMeanRows 271).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 271).c)).2-
      (generalMeanRows 271).J/2-(generalMeanRows 271).error 4 := by
  have he : (generalMeanRows 271).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 271) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 271)
    (generalMeanRows_prefactorDomain 271) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0271

/-! Kernel-checked entropy margins for general spectral rectangle 272. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0272
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4868153856) (.branch 2 (.leaf 4693643343) (.leaf 4527138473))) (.branch 5 (.branch 4 (.leaf 4368178803) (.leaf 4216336455)) (.branch 6 (.leaf 4071213282) (.leaf 3932438329)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3799665570) (.leaf 3672571872)) (.branch 10 (.leaf 3550855157) (.leaf 3434232756))) (.branch 13 (.branch 12 (.leaf 3322439905) (.leaf 3215228393)) (.branch 14 (.leaf 3112365327) (.leaf 3013632007))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2918822907) (.branch 17 (.leaf 2827744733) (.leaf 2740215569))) (.branch 20 (.branch 19 (.leaf 2656064092) (.leaf 2575128844)) (.branch 21 (.leaf 2497257574) (.leaf 2422306624)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2350140363) (.leaf 2280630669)) (.branch 25 (.leaf 2213656445) (.leaf 2149103171))) (.branch 28 (.branch 27 (.leaf 2086862497) (.leaf 2026831853)) (.branch 29 (.leaf 1968914095) (.leaf 1913017175)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1859053835) (.branch 32 (.leaf 1806941314) (.leaf 1756601087))) (.branch 35 (.branch 34 (.leaf 1707958615) (.leaf 1660943110)) (.branch 36 (.leaf 1615487318) (.leaf 1571527319)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1529002336) (.leaf 1487854556)) (.branch 40 (.leaf 1448028965) (.leaf 1409473191))) (.branch 43 (.branch 42 (.leaf 1372137360) (.leaf 1335973958)) (.branch 44 (.leaf 1300937701) (.leaf 1266985416))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1234075928) (.branch 47 (.leaf 1202169952) (.leaf 1171229992))) (.branch 50 (.branch 49 (.leaf 1141220250) (.leaf 1112106535)) (.branch 51 (.leaf 1083856178) (.leaf 1056437956)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1029822017) (.leaf 1003979810)) (.branch 55 (.leaf 978884019) (.leaf 954508501))) (.branch 58 (.branch 57 (.leaf 930828225) (.leaf 907819221)) (.branch 59 (.leaf 885458526) (.leaf 863724130))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 842594939) (.branch 62 (.leaf 822050719) (.leaf 802072066))) (.branch 65 (.branch 64 (.leaf 782640355) (.leaf 763737714)) (.branch 66 (.leaf 745346978) (.leaf 727451665)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 710035938) (.leaf 693084575)) (.branch 70 (.leaf 676582944) (.leaf 660516976))) (.branch 73 (.branch 72 (.leaf 644873135) (.leaf 629638397)) (.branch 74 (.leaf 614800228) (.leaf 600346559))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 586265768) (.branch 77 (.leaf 572546657) (.leaf 559178439))) (.branch 80 (.branch 79 (.leaf 546150713) (.leaf 533453455)) (.branch 81 (.leaf 521076993) (.leaf 509012001)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 497249477) (.leaf 485780733)) (.branch 85 (.leaf 474597382) (.leaf 463691325))) (.branch 88 (.branch 87 (.leaf 453054736) (.leaf 442680057)) (.branch 89 (.leaf 432559981) (.leaf 422687445)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 413055621) (.branch 92 (.leaf 403657904) (.leaf 394487903))) (.branch 95 (.branch 94 (.leaf 385539437) (.leaf 376806521)) (.branch 96 (.leaf 368283362) (.leaf 359964353)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 351844059) (.leaf 343917218)) (.branch 100 (.leaf 336178731) (.leaf 328623657))) (.branch 103 (.branch 102 (.leaf 321247205) (.leaf 314044730)) (.branch 104 (.leaf 307011729) (.leaf 300143834))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 293436806) (.leaf 286886532)) (.branch 108 (.leaf 280489024) (.leaf 274240405))) (.branch 111 (.branch 110 (.leaf 268136916) (.leaf 262174905)) (.branch 112 (.leaf 256350824) (.leaf 250661228)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 245102771) (.leaf 239672198)) (.branch 116 (.leaf 234366351) (.leaf 229182155))) (.branch 119 (.branch 118 (.leaf 224116624) (.leaf 219166854)) (.branch 120 (.leaf 214330021) (.leaf 209603376)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 272).prefactor = (2429921875372291/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 272).cutoff/(generalMeanRows 272).c)).2 =
    (5662946035573/15625000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 272).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 272).q*(generalMeanRows 272).c/2-2 = (43/50:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable020.value]
  have hcontinuation : (generalMeanRows 272).q*(generalMeanRows 272).cutoff/2-2 = (386/183:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable123.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 272).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 272).criticalRate j.val*(generalMeanRows 272).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 272).c*(generalMeanRows 272).criticalPoint j.val)).2-
      (generalMeanRows 272).J/2-(generalMeanRows 272).error (generalMeanGrid j.val)+
      (generalMeanRows 272).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 272).c)).2-
      (generalMeanRows 272).J/2-(generalMeanRows 272).error 4 := by
  have he : (generalMeanRows 272).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 272) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 272)
    (generalMeanRows_prefactorDomain 272) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0272

/-! Kernel-checked entropy margins for general spectral rectangle 273. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0273
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4797429075) (.branch 2 (.leaf 4623187823) (.leaf 4456965006))) (.branch 5 (.branch 4 (.leaf 4298300119) (.leaf 4146765182)) (.branch 6 (.leaf 4001961900) (.leaf 3863519137)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3731090654) (.leaf 3604353071)) (.branch 10 (.leaf 3483004047) (.leaf 3366760618))) (.branch 13 (.branch 12 (.leaf 3255357714) (.leaf 3148546798)) (.branch 14 (.leaf 3046094637) (.leaf 2947782182))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2853403546) (.branch 17 (.leaf 2762765068) (.leaf 2675684460))) (.branch 20 (.branch 19 (.leaf 2591990018) (.leaf 2511519908)) (.branch 21 (.leaf 2434121495) (.leaf 2359650739)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2287971629) (.leaf 2218955663)) (.branch 25 (.leaf 2152481367) (.leaf 2088433848))) (.branch 28 (.branch 27 (.leaf 2026704386) (.leaf 1967190047)) (.branch 29 (.leaf 1909793327) (.leaf 1854421826)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1800987935) (.branch 32 (.leaf 1749408556) (.leaf 1699604830))) (.branch 35 (.branch 34 (.leaf 1651501888) (.leaf 1605028624)) (.branch 36 (.leaf 1560117473) (.leaf 1516704211)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1474727764) (.leaf 1434130030)) (.branch 40 (.leaf 1394855716) (.leaf 1356852177))) (.branch 43 (.branch 42 (.leaf 1320069275) (.leaf 1284459240)) (.branch 44 (.leaf 1249976541) (.leaf 1216577764))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1184221503) (.branch 47 (.leaf 1152868248) (.leaf 1122480287))) (.branch 50 (.branch 49 (.leaf 1093021615) (.leaf 1064457838)) (.branch 51 (.leaf 1036756095) (.leaf 1009884978)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 983814456) (.leaf 958515807)) (.branch 55 (.leaf 933961550) (.leaf 910125384))) (.branch 58 (.branch 57 (.leaf 886982131) (.leaf 864507674)) (.branch 59 (.leaf 842678913) (.leaf 821473708))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 800870840) (.branch 62 (.leaf 780849956) (.leaf 761391538))) (.branch 65 (.branch 64 (.leaf 742476857) (.leaf 724087935)) (.branch 66 (.leaf 706207516) (.leaf 688819024)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 671906535) (.leaf 655454750)) (.branch 70 (.leaf 639448961) (.leaf 623875025))) (.branch 73 (.branch 72 (.leaf 608719341) (.leaf 593968823)) (.branch 74 (.leaf 579610880) (.leaf 565633388))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 552024675) (.branch 77 (.leaf 538773500) (.leaf 525869032))) (.branch 80 (.branch 79 (.leaf 513300833) (.leaf 501058842)) (.branch 81 (.leaf 489133358) (.leaf 477515025)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 466194818) (.leaf 455164025)) (.branch 85 (.leaf 444414242) (.leaf 433937352))) (.branch 88 (.branch 87 (.leaf 423725518) (.leaf 413771168)) (.branch 89 (.leaf 404066989) (.leaf 394605911)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 385381103) (.branch 92 (.leaf 376385958) (.leaf 367614087))) (.branch 95 (.branch 94 (.leaf 359059311) (.leaf 350715650)) (.branch 96 (.leaf 342577318) (.leaf 334638715)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 326894417) (.leaf 319339175)) (.branch 100 (.leaf 311967903) (.leaf 304775673))) (.branch 103 (.branch 102 (.leaf 297757712) (.leaf 290909393)) (.branch 104 (.leaf 284226231) (.leaf 277703877))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 271338116) (.leaf 265124858)) (.branch 108 (.leaf 259060134) (.leaf 253140096))) (.branch 111 (.branch 110 (.leaf 247361009) (.leaf 241719246)) (.branch 112 (.leaf 236211288) (.leaf 230833718)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 225583217) (.leaf 220456563)) (.branch 116 (.leaf 215450623) (.leaf 210562357))) (.branch 119 (.branch 118 (.leaf 205788808) (.leaf 201127104)) (.branch 120 (.leaf 196574453) (.leaf 192128141)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 273).prefactor = (2430386233155157/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 273).cutoff/(generalMeanRows 273).c)).2 =
    (70655293995927/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 273).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 273).q*(generalMeanRows 273).c/2-2 = (441/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable108.value]
  have hcontinuation : (generalMeanRows 273).q*(generalMeanRows 273).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable030.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 273).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 273).criticalRate j.val*(generalMeanRows 273).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 273).c*(generalMeanRows 273).criticalPoint j.val)).2-
      (generalMeanRows 273).J/2-(generalMeanRows 273).error (generalMeanGrid j.val)+
      (generalMeanRows 273).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 273).c)).2-
      (generalMeanRows 273).J/2-(generalMeanRows 273).error 4 := by
  have he : (generalMeanRows 273).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 273) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 273)
    (generalMeanRows_prefactorDomain 273) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0273

/-! Kernel-checked entropy margins for general spectral rectangle 274. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0274
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4805879839) (.branch 2 (.leaf 4631331659) (.leaf 4464816036))) (.branch 5 (.branch 4 (.leaf 4305871658) (.leaf 4154069789)) (.branch 6 (.leaf 4009011433) (.leaf 3870324801)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3737663042) (.leaf 3610702209)) (.branch 10 (.leaf 3489139426) (.leaf 3372691232))) (.branch 13 (.branch 12 (.leaf 3261092090) (.leaf 3154093024)) (.branch 14 (.leaf 3051460391) (.leaf 2952974757))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2858429871) (.branch 17 (.leaf 2767631732) (.leaf 2680397730))) (.branch 20 (.branch 19 (.leaf 2596555859) (.leaf 2515943999)) (.branch 21 (.leaf 2438409247) (.leaf 2363807310)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2292001936) (.leaf 2222864397)) (.branch 25 (.leaf 2156273005) (.leaf 2092112665))) (.branch 28 (.branch 27 (.leaf 2030274466) (.leaf 1970655290)) (.branch 29 (.leaf 1913157465) (.leaf 1857688426)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1804160411) (.branch 32 (.leaf 1752490174) (.leaf 1702598717))) (.branch 35 (.branch 34 (.leaf 1654411041) (.leaf 1607855913)) (.branch 36 (.leaf 1562865651) (.leaf 1519375915)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1477325526) (.leaf 1436656278)) (.branch 40 (.leaf 1397312781) (.leaf 1359242298))) (.branch 43 (.branch 42 (.leaf 1322394603) (.leaf 1286721840)) (.branch 44 (.leaf 1252178399) (.leaf 1218720790))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1186307532) (.branch 47 (.leaf 1154899047) (.leaf 1124457558))) (.branch 50 (.branch 49 (.leaf 1094946994) (.leaf 1066332901)) (.branch 51 (.leaf 1038582361) (.leaf 1011663910)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 985547465) (.leaf 960204251)) (.branch 55 (.leaf 935606741) (.leaf 911728588))) (.branch 58 (.branch 57 (.leaf 888544567) (.leaf 866030521)) (.branch 59 (.leaf 844163308) (.leaf 822920750))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 802281589) (.branch 62 (.leaf 782225438) (.leaf 762732744))) (.branch 65 (.branch 64 (.leaf 743784744) (.leaf 725363430)) (.branch 66 (.leaf 707451514) (.leaf 690032392)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 673090112) (.leaf 656609347)) (.branch 70 (.leaf 640575363) (.leaf 624973993))) (.branch 73 (.branch 72 (.leaf 609791612) (.leaf 595015111)) (.branch 74 (.leaf 580631875) (.leaf 566629762))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 552997078) (.branch 77 (.leaf 539722560) (.leaf 526795361))) (.branch 80 (.branch 79 (.leaf 514205022) (.leaf 501941467)) (.branch 81 (.leaf 489994976) (.leaf 478356177)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 467016029) (.leaf 455965806)) (.branch 85 (.leaf 445197087) (.leaf 434701741))) (.branch 88 (.branch 87 (.leaf 424471918) (.leaf 414500034)) (.branch 89 (.leaf 404778760) (.leaf 395301017)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 386059960) (.branch 92 (.leaf 377048969) (.leaf 368261647))) (.branch 95 (.branch 94 (.leaf 359691801) (.leaf 351333442)) (.branch 96 (.leaf 343180775) (.leaf 335228187)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 327470248) (.leaf 319901697)) (.branch 100 (.leaf 312517440) (.leaf 305312541))) (.branch 103 (.branch 102 (.leaf 298282218) (.leaf 291421835)) (.branch 104 (.leaf 284726901) (.leaf 278193058))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 271816084) (.leaf 265591880)) (.branch 108 (.leaf 259516473) (.leaf 253586007))) (.branch 111 (.branch 110 (.leaf 247796740) (.leaf 242145039)) (.branch 112 (.leaf 236627379) (.leaf 231240336)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 225980587) (.leaf 220844901)) (.branch 116 (.leaf 215830143) (.leaf 210933266))) (.branch 119 (.branch 118 (.leaf 206151309) (.leaf 201481393)) (.branch 120 (.leaf 196920723) (.leaf 192466578)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 274).prefactor = (97386696228029/20000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 274).cutoff/(generalMeanRows 274).c)).2 =
    (70655293995927/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 274).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 274).q*(generalMeanRows 274).c/2-2 = (441/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable108.value]
  have hcontinuation : (generalMeanRows 274).q*(generalMeanRows 274).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable030.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 274).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 274).criticalRate j.val*(generalMeanRows 274).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 274).c*(generalMeanRows 274).criticalPoint j.val)).2-
      (generalMeanRows 274).J/2-(generalMeanRows 274).error (generalMeanGrid j.val)+
      (generalMeanRows 274).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 274).c)).2-
      (generalMeanRows 274).J/2-(generalMeanRows 274).error 4 := by
  have he : (generalMeanRows 274).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 274) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 274)
    (generalMeanRows_prefactorDomain 274) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0274

/-! Kernel-checked entropy margins for general spectral rectangle 275. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0275
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4795634109) (.branch 2 (.leaf 4621414984) (.leaf 4455221315))) (.branch 5 (.branch 4 (.leaf 4296591651) (.leaf 4145097153)) (.branch 6 (.leaf 4000338749) (.leaf 3861944603)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3729567842) (.leaf 3602884519)) (.branch 10 (.leaf 3481591775) (.leaf 3365406190))) (.branch 13 (.branch 12 (.leaf 3254062278) (.leaf 3147311132)) (.branch 14 (.leaf 3044919190) (.leaf 2946667109))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2852348740) (.branch 17 (.leaf 2761770192) (.leaf 2674748972))) (.branch 20 (.branch 19 (.leaf 2591113200) (.leaf 2510700884)) (.branch 21 (.leaf 2433359254) (.leaf 2358944156)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2287319477) (.leaf 2218356633)) (.branch 25 (.leaf 2151934078) (.leaf 2087936864))) (.branch 28 (.branch 27 (.leaf 2026256224) (.leaf 1966789188)) (.branch 29 (.leaf 1909438228) (.leaf 1854110925)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1800719660) (.branch 32 (.leaf 1749181330) (.leaf 1699417078))) (.branch 35 (.branch 34 (.leaf 1651352044) (.leaf 1604915134)) (.branch 36 (.leaf 1560038799) (.leaf 1516658834)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1474714189) (.leaf 1434146788)) (.branch 40 (.leaf 1394901365) (.leaf 1356925307))) (.branch 43 (.branch 42 (.leaf 1320168506) (.leaf 1284583227)) (.branch 44 (.leaf 1250123971) (.leaf 1216747361))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1184412026) (.branch 47 (.leaf 1153078494) (.leaf 1122709089))) (.branch 50 (.branch 49 (.leaf 1093267841) (.leaf 1064720396)) (.branch 51 (.leaf 1037033929) (.leaf 1010177068)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 984119819) (.leaf 958833495)) (.branch 55 (.leaf 934290652) (.leaf 910465023))) (.branch 58 (.branch 57 (.leaf 887331465) (.leaf 864865895)) (.branch 59 (.leaf 843045245) (.leaf 821847410))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 801251200) (.branch 62 (.leaf 781236294) (.leaf 761783205))) (.branch 65 (.branch 64 (.leaf 742873231) (.leaf 724488426)) (.branch 66 (.leaf 706611559) (.leaf 689226081)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 672316097) (.leaf 655866330)) (.branch 70 (.leaf 639862097) (.leaf 624289280))) (.branch 73 (.branch 72 (.leaf 609134301) (.leaf 594384095)) (.branch 74 (.leaf 580026092) (.leaf 566048190))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 552438737) (.branch 77 (.leaf 539186509) (.leaf 526280695))) (.branch 80 (.branch 79 (.leaf 513710873) (.leaf 501467001)) (.branch 81 (.leaf 489539393) (.leaf 477918709)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 466595938) (.leaf 455562385)) (.branch 85 (.leaf 444809656) (.leaf 434329650))) (.branch 88 (.branch 87 (.leaf 424114541) (.leaf 414156770)) (.branch 89 (.leaf 404449035) (.leaf 394984278)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 385755676) (.branch 92 (.leaf 376756634) (.leaf 367980772))) (.branch 95 (.branch 94 (.leaf 359421920) (.leaf 351074106)) (.branch 96 (.leaf 342931554) (.leaf 334988669)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 327240038) (.leaf 319680415)) (.branch 100 (.leaf 312304723) (.leaf 305108040))) (.branch 103 (.branch 102 (.leaf 298085599) (.leaf 291232778)) (.branch 104 (.leaf 284545098) (.leaf 278018215))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 271647919) (.leaf 265430122)) (.branch 108 (.leaf 259360863) (.leaf 253436296))) (.branch 111 (.branch 110 (.leaf 247652689) (.leaf 242006420)) (.branch 112 (.leaf 236493973) (.leaf 231111933)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 225856985) (.leaf 220725909)) (.branch 116 (.leaf 215715575) (.leaf 210822944))) (.branch 119 (.branch 118 (.leaf 206045063) (.leaf 201379061)) (.branch 120 (.leaf 196822148) (.leaf 192371612)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 275).prefactor = (4868369755466683/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 275).cutoff/(generalMeanRows 275).c)).2 =
    (177382836765551/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 275).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 275).q*(generalMeanRows 275).c/2-2 = (441/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable108.value]
  have hcontinuation : (generalMeanRows 275).q*(generalMeanRows 275).cutoff/2-2 = (386/183:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable123.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 275).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 275).criticalRate j.val*(generalMeanRows 275).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 275).c*(generalMeanRows 275).criticalPoint j.val)).2-
      (generalMeanRows 275).J/2-(generalMeanRows 275).error (generalMeanGrid j.val)+
      (generalMeanRows 275).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 275).c)).2-
      (generalMeanRows 275).J/2-(generalMeanRows 275).error 4 := by
  have he : (generalMeanRows 275).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 275) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 275)
    (generalMeanRows_prefactorDomain 275) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0275

/-! Kernel-checked entropy margins for general spectral rectangle 276. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0276
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4804047466) (.branch 2 (.leaf 4629522695) (.leaf 4463037459))) (.branch 5 (.branch 4 (.leaf 4304129499) (.leaf 4152369221)) (.branch 6 (.leaf 4007356857) (.leaf 3868719915)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3736110915) (.leaf 3609205341)) (.branch 10 (.leaf 3487699805) (.leaf 3371310386))) (.branch 13 (.branch 12 (.leaf 3259771134) (.leaf 3152832707)) (.branch 14 (.leaf 3050261131) (.leaf 2951836678))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2857352839) (.branch 17 (.leaf 2766615382) (.leaf 2679441494))) (.branch 20 (.branch 19 (.leaf 2595658993) (.leaf 2515105603)) (.branch 21 (.leaf 2437628287) (.leaf 2363082636)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2291332301) (.leaf 2222248469)) (.branch 25 (.leaf 2155709384) (.leaf 2091599895))) (.branch 28 (.branch 27 (.leaf 2029811044) (.leaf 1970239681)) (.branch 29 (.leaf 1912788106) (.leaf 1857363737)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1803878803) (.branch 32 (.leaf 1752250055) (.leaf 1702398498))) (.branch 35 (.branch 34 (.leaf 1654249140) (.leaf 1607730762)) (.branch 36 (.leaf 1562775697) (.leaf 1519319628)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1477301396) (.leaf 1436662824)) (.branch 40 (.leaf 1397348550) (.leaf 1359305867))) (.branch 43 (.branch 42 (.leaf 1322484581) (.leaf 1286836872)) (.branch 44 (.leaf 1252317161) (.leaf 1218881996))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1186489933) (.branch 47 (.leaf 1155101430) (.leaf 1124678745))) (.branch 50 (.branch 49 (.leaf 1095185847) (.leaf 1066588319)) (.branch 51 (.leaf 1038853279) (.leaf 1011949301)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 985846337) (.leaf 960515652)) (.branch 55 (.leaf 935929751) (.leaf 912062324))) (.branch 58 (.branch 57 (.leaf 888888180) (.leaf 866383197)) (.branch 59 (.leaf 844524266) (.leaf 823289242))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 802656897) (.branch 62 (.leaf 782606878) (.leaf 763119661))) (.branch 65 (.branch 64 (.leaf 744176512) (.leaf 725759453)) (.branch 66 (.leaf 707851223) (.leaf 690435245)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 673495594) (.leaf 657016968)) (.branch 70 (.leaf 640984657) (.leaf 625384520))) (.branch 73 (.branch 72 (.leaf 610202953) (.leaf 595426870)) (.branch 74 (.leaf 581043678) (.leaf 567041253))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 553407924) (.branch 77 (.leaf 540132446) (.leaf 527203990))) (.branch 80 (.branch 79 (.leaf 514612116) (.leaf 502346764)) (.branch 81 (.leaf 490398230) (.leaf 478757159)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 467414524) (.leaf 456361614)) (.branch 85 (.leaf 445590021) (.leaf 435091629))) (.branch 88 (.branch 87 (.leaf 424858598) (.leaf 414883358)) (.branch 89 (.leaf 405158592) (.leaf 395677230)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 386432438) (.branch 92 (.leaf 377417608) (.leaf 368626350))) (.branch 95 (.branch 94 (.leaf 360052482) (.leaf 351690023)) (.branch 96 (.leaf 343533186) (.leaf 335576366)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 327814141) (.leaf 320241256)) (.branch 100 (.leaf 312852624) (.leaf 305643315))) (.branch 103 (.branch 102 (.leaf 298608554) (.leaf 291743710)) (.branch 104 (.leaf 285044298) (.leaf 278505965))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 272124492) (.leaf 265895787)) (.branch 108 (.leaf 259815880) (.leaf 253880919))) (.branch 111 (.branch 110 (.leaf 248087166) (.leaf 242430991)) (.branch 112 (.leaf 236908873) (.leaf 231517391)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 226253224) (.leaf 221113145)) (.branch 116 (.leaf 216094021) (.leaf 211192807))) (.branch 119 (.branch 118 (.leaf 206406544) (.leaf 201732356)) (.branch 120 (.leaf 197167449) (.leaf 192709104)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 276).prefactor = (975382143605399/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 276).cutoff/(generalMeanRows 276).c)).2 =
    (177382836765551/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 276).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 276).q*(generalMeanRows 276).c/2-2 = (441/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable108.value]
  have hcontinuation : (generalMeanRows 276).q*(generalMeanRows 276).cutoff/2-2 = (386/183:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable123.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 276).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 276).criticalRate j.val*(generalMeanRows 276).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 276).c*(generalMeanRows 276).criticalPoint j.val)).2-
      (generalMeanRows 276).J/2-(generalMeanRows 276).error (generalMeanGrid j.val)+
      (generalMeanRows 276).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 276).c)).2-
      (generalMeanRows 276).J/2-(generalMeanRows 276).error 4 := by
  have he : (generalMeanRows 276).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 276) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 276)
    (generalMeanRows_prefactorDomain 276) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0276

/-! Kernel-checked entropy margins for general spectral rectangle 277. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0277
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4814345490) (.branch 2 (.leaf 4639489839) (.leaf 4472680896))) (.branch 5 (.branch 4 (.leaf 4313456535) (.leaf 4161387264)) (.branch 6 (.leaf 4016073385) (.leaf 3877142454)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3744247008) (.leaf 3617062531)) (.branch 10 (.leaf 3495285613) (.leaf 3378632293))) (.branch 13 (.branch 12 (.leaf 3266836567) (.leaf 3159649020)) (.branch 14 (.leaf 3056835598) (.leaf 2958176480))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2863465051) (.branch 17 (.leaf 2772506969) (.leaf 2685119302))) (.branch 20 (.branch 19 (.leaf 2601129743) (.leaf 2520375883)) (.branch 21 (.leaf 2442704552) (.leaf 2367971202)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2296039342) (.leaf 2226780016)) (.branch 25 (.leaf 2160071321) (.leaf 2095797962))) (.branch 28 (.branch 27 (.leaf 2033850833) (.leaf 1974126638)) (.branch 29 (.leaf 1916527529) (.leaf 1860960780)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1807338474) (.branch 32 (.leaf 1755577219) (.leaf 1705597877))) (.branch 35 (.branch 34 (.leaf 1657325318) (.leaf 1610688183)) (.branch 36 (.leaf 1565618669) (.leaf 1522052325)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1479927863) (.leaf 1439186976)) (.branch 40 (.leaf 1399774175) (.leaf 1361636630))) (.branch 43 (.branch 42 (.leaf 1324724027) (.leaf 1288988426)) (.branch 44 (.leaf 1254384135) (.leaf 1220867590))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1188397236) (.branch 47 (.leaf 1156933424) (.leaf 1126438312))) (.branch 50 (.branch 49 (.leaf 1096875764) (.leaf 1068211267)) (.branch 51 (.leaf 1040411844) (.leaf 1013445976)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 987283526) (.leaf 961895670)) (.branch 55 (.leaf 937254831) (.leaf 913334616))) (.branch 58 (.branch 57 (.leaf 890109755) (.leaf 867556050)) (.branch 59 (.leaf 845650318) (.leaf 824370341))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 803694824) (.branch 62 (.leaf 783603344) (.leaf 764076313))) (.branch 65 (.branch 64 (.leaf 745094935) (.leaf 726641172)) (.branch 66 (.leaf 708697704) (.leaf 691247897)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 674275773) (.leaf 657765977)) (.branch 70 (.leaf 641703748) (.leaf 626074896))) (.branch 73 (.branch 72 (.leaf 610865771) (.leaf 596063242)) (.branch 74 (.leaf 581654670) (.leaf 567627891))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 553971193) (.branch 77 (.leaf 540673292) (.leaf 527723321))) (.branch 80 (.branch 79 (.leaf 515110805) (.leaf 502825647)) (.branch 81 (.leaf 490858112) (.leaf 479198811)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 467838687) (.leaf 456768998)) (.branch 85 (.leaf 445981310) (.leaf 435467477))) (.branch 88 (.branch 87 (.leaf 425219634) (.leaf 415230184)) (.branch 89 (.leaf 405491786) (.leaf 395997348)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 386740012) (.branch 92 (.leaf 377713148) (.leaf 368910347))) (.branch 95 (.branch 94 (.leaf 360325405) (.leaf 351952323)) (.branch 96 (.leaf 343785294) (.leaf 335818698)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 328047093) (.leaf 320465211)) (.branch 100 (.leaf 313067946) (.leaf 305850355))) (.branch 103 (.branch 102 (.leaf 298807648) (.leaf 291935181)) (.branch 104 (.leaf 285228453) (.leaf 278683101))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 272294893) (.leaf 266059725)) (.branch 108 (.leaf 259973617) (.leaf 254032704))) (.branch 111 (.branch 110 (.leaf 248233239) (.leaf 242571582)) (.branch 112 (.leaf 237044203) (.leaf 231647671)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 226378656) (.leaf 221233924)) (.branch 116 (.leaf 216210332) (.leaf 211304829))) (.branch 119 (.branch 118 (.leaf 206514448) (.leaf 201836306)) (.branch 120 (.leaf 197267602) (.leaf 192805612)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 277).prefactor = (2438956119614869/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 277).cutoff/(generalMeanRows 277).c)).2 =
    (70655293995927/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 277).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 277).q*(generalMeanRows 277).c/2-2 = (441/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable108.value]
  have hcontinuation : (generalMeanRows 277).q*(generalMeanRows 277).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable030.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 277).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 277).criticalRate j.val*(generalMeanRows 277).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 277).c*(generalMeanRows 277).criticalPoint j.val)).2-
      (generalMeanRows 277).J/2-(generalMeanRows 277).error (generalMeanGrid j.val)+
      (generalMeanRows 277).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 277).c)).2-
      (generalMeanRows 277).J/2-(generalMeanRows 277).error 4 := by
  have he : (generalMeanRows 277).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 277) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 277)
    (generalMeanRows_prefactorDomain 277) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0277

/-! Kernel-checked entropy margins for general spectral rectangle 278. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0278
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4743242433) (.branch 2 (.leaf 4568708284) (.leaf 4402240178))) (.branch 5 (.branch 4 (.leaf 4243374951) (.leaf 4091682120)) (.branch 6 (.leaf 3946761041) (.leaf 3808238365)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3675765760) (.leaf 3549017879)) (.branch 10 (.leaf 3427690514) (.leaf 3311498939))) (.branch 13 (.branch 12 (.leaf 3200176415) (.leaf 3093472820)) (.branch 14 (.leaf 2991153422) (.leaf 2892997747))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2798798554) (.branch 17 (.leaf 2708360895) (.leaf 2621501258))) (.branch 20 (.branch 19 (.leaf 2538046777) (.leaf 2457834505)) (.branch 21 (.leaf 2380710755) (.leaf 2306530480)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2235156709) (.leaf 2166460025)) (.branch 25 (.leaf 2100318082) (.leaf 2036615156))) (.branch 28 (.branch 27 (.leaf 1975241730) (.leaf 1916094113)) (.branch 29 (.leaf 1859074076) (.leaf 1804088528)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1751049201) (.branch 32 (.leaf 1699872364) (.leaf 1650478555))) (.branch 35 (.branch 34 (.leaf 1602792331) (.leaf 1556742035)) (.branch 36 (.leaf 1512259576) (.leaf 1469280229)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1427742440) (.leaf 1387587649)) (.branch 40 (.leaf 1348760124) (.leaf 1311206804))) (.branch 43 (.branch 42 (.leaf 1274877150) (.leaf 1239723012)) (.branch 44 (.leaf 1205698495) (.leaf 1172759837))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1140865300) (.branch 47 (.leaf 1109975058) (.leaf 1080051099))) (.branch 50 (.branch 49 (.leaf 1051057127) (.leaf 1022958477)) (.branch 51 (.leaf 995722025) (.leaf 969316114)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 943710475) (.leaf 918876162)) (.branch 55 (.leaf 894785479) (.leaf 871411920))) (.branch 58 (.branch 57 (.leaf 848730113) (.leaf 826715758)) (.branch 59 (.leaf 805345578) (.leaf 784597269))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 764449453) (.branch 62 (.leaf 744881629) (.leaf 725874137))) (.branch 65 (.branch 64 (.leaf 707408114) (.leaf 689465459)) (.branch 66 (.leaf 672028793) (.leaf 655081430)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 638607340) (.leaf 622591124)) (.branch 70 (.leaf 607017980) (.leaf 591873679))) (.branch 73 (.branch 72 (.leaf 577144537) (.leaf 562817392)) (.branch 74 (.leaf 548879579) (.leaf 535318910))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 522123650) (.branch 77 (.leaf 509282501) (.leaf 496784578))) (.branch 80 (.branch 79 (.leaf 484619394) (.leaf 472776844)) (.branch 81 (.leaf 461247186) (.leaf 450021026)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 439089305) (.leaf 428443283)) (.branch 85 (.leaf 418074526) (.leaf 407974894))) (.branch 88 (.branch 87 (.leaf 398136528) (.leaf 388551839)) (.branch 89 (.leaf 379213499) (.leaf 370114425)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 361247774) (.branch 92 (.leaf 352606933) (.leaf 344185506))) (.branch 95 (.branch 94 (.leaf 335977311) (.leaf 327976367)) (.branch 96 (.leaf 320176889) (.leaf 312573279)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 305160118) (.leaf 297932162)) (.branch 100 (.leaf 290884333) (.leaf 284011714))) (.branch 103 (.branch 102 (.leaf 277309540) (.leaf 270773199)) (.branch 104 (.leaf 264398219) (.leaf 258180266))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 252115140) (.leaf 246198768)) (.branch 108 (.leaf 240427202) (.leaf 234796612))) (.branch 111 (.branch 110 (.leaf 229303282) (.leaf 223943609)) (.branch 112 (.leaf 218714095) (.leaf 213611346)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 208632067) (.leaf 203773060)) (.branch 116 (.leaf 199031219) (.leaf 194403528))) (.branch 119 (.branch 118 (.leaf 189887057) (.leaf 185478963)) (.branch 120 (.leaf 181176479) (.leaf 176976919)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 278).prefactor = (488650477636371/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 278).cutoff/(generalMeanRows 278).c)).2 =
    (345671870594417/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 278).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 278).q*(generalMeanRows 278).c/2-2 = (113/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable124.value]
  have hcontinuation : (generalMeanRows 278).q*(generalMeanRows 278).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable030.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 278).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 278).criticalRate j.val*(generalMeanRows 278).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 278).c*(generalMeanRows 278).criticalPoint j.val)).2-
      (generalMeanRows 278).J/2-(generalMeanRows 278).error (generalMeanGrid j.val)+
      (generalMeanRows 278).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 278).c)).2-
      (generalMeanRows 278).J/2-(generalMeanRows 278).error 4 := by
  have he : (generalMeanRows 278).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 278) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 278)
    (generalMeanRows_prefactorDomain 278) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0278

/-! Kernel-checked entropy margins for general spectral rectangle 279. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0279
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4802148643) (.branch 2 (.leaf 4627650987) (.leaf 4461199656))) (.branch 5 (.branch 4 (.leaf 4302331450) (.leaf 4150615929)) (.branch 6 (.leaf 4005652554) (.leaf 3867068146)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3734514596) (.leaf 3607666828)) (.branch 10 (.leaf 3486220948) (.leaf 3369892583))) (.branch 13 (.branch 12 (.leaf 3258415376) (.leaf 3151539621)) (.branch 14 (.leaf 3049031022) (.leaf 2950669563))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2856248481) (.branch 17 (.leaf 2765573318) (.leaf 2678461064))) (.branch 20 (.branch 19 (.leaf 2594739364) (.leaf 2514245791)) (.branch 21 (.leaf 2436827179) (.leaf 2362339007)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2290644831) (.leaf 2221615760)) (.branch 25 (.leaf 2155129970) (.leaf 2091072260))) (.branch 28 (.branch 27 (.leaf 2029333628) (.leaf 1969810893)) (.branch 29 (.leaf 1912406333) (.leaf 1857027351)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1803586170) (.branch 32 (.leaf 1751999539) (.leaf 1702188468))) (.branch 35 (.branch 34 (.leaf 1654077977) (.leaf 1607596861)) (.branch 36 (.leaf 1562677472) (.leaf 1519255515)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1477269857) (.leaf 1436662350)) (.branch 40 (.leaf 1397377660) (.leaf 1359363114))) (.branch 43 (.branch 42 (.leaf 1322568552) (.leaf 1286946187)) (.branch 44 (.leaf 1252450478) (.leaf 1219038010))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1186667375) (.branch 47 (.leaf 1155299070) (.leaf 1124895392))) (.branch 50 (.branch 49 (.leaf 1095420347) (.leaf 1066839557)) (.branch 51 (.leaf 1039120178) (.leaf 1012230822)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 986141478) (.leaf 960823448)) (.branch 55 (.leaf 936249274) (.leaf 912392682))) (.branch 58 (.branch 57 (.leaf 889228517) (.leaf 866732690)) (.branch 59 (.leaf 844882128) (.leaf 823654717))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 803029264) (.branch 62 (.leaf 782985445) (.leaf 763503768))) (.branch 65 (.branch 64 (.leaf 744565529) (.leaf 726152779)) (.branch 66 (.leaf 708248285) (.leaf 690835498)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 673898520) (.leaf 657422074)) (.branch 70 (.leaf 641391475) (.leaf 625792606))) (.branch 73 (.branch 72 (.leaf 610611886) (.leaf 595836252)) (.branch 74 (.leaf 581453132) (.leaf 567450424))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 553816476) (.branch 77 (.leaf 540540063) (.leaf 527610374))) (.branch 80 (.branch 79 (.leaf 515016988) (.leaf 502749859)) (.branch 81 (.leaf 490799304) (.leaf 479155981)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 467810878) (.leaf 456755299)) (.branch 85 (.leaf 445980851) (.leaf 435479430))) (.branch 88 (.branch 87 (.leaf 425243210) (.leaf 415264631)) (.branch 89 (.leaf 405536390) (.leaf 396051426)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 386802917) (.branch 92 (.leaf 377784264) (.leaf 368989087))) (.branch 95 (.branch 94 (.leaf 360411214) (.leaf 352044672)) (.branch 96 (.leaf 343883681) (.leaf 335922646)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 328156151) (.leaf 320578948)) (.branch 100 (.leaf 313185958) (.leaf 305972258))) (.branch 103 (.branch 102 (.leaf 298933075) (.leaf 292063788)) (.branch 104 (.leaf 285359915) (.leaf 278817108))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 272431155) (.leaf 266197967)) (.branch 108 (.leaf 260113577) (.leaf 254174139))) (.branch 111 (.branch 110 (.leaf 248375917) (.leaf 242715287)) (.branch 112 (.leaf 237188729) (.leaf 231792826)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 226524260) (.leaf 221379806)) (.branch 116 (.leaf 216356334) (.leaf 211450801))) (.branch 119 (.branch 118 (.leaf 206660251) (.leaf 201981809)) (.branch 120 (.leaf 197412683) (.leaf 192950157)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 279).prefactor = (4884424368468543/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 279).cutoff/(generalMeanRows 279).c)).2 =
    (178128549058887/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 279).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 279).q*(generalMeanRows 279).c/2-2 = (441/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable108.value]
  have hcontinuation : (generalMeanRows 279).q*(generalMeanRows 279).cutoff/2-2 = (2126/1005:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable121.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 279).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 279).criticalRate j.val*(generalMeanRows 279).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 279).c*(generalMeanRows 279).criticalPoint j.val)).2-
      (generalMeanRows 279).J/2-(generalMeanRows 279).error (generalMeanGrid j.val)+
      (generalMeanRows 279).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 279).c)).2-
      (generalMeanRows 279).J/2-(generalMeanRows 279).error 4 := by
  have he : (generalMeanRows 279).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 279) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 279)
    (generalMeanRows_prefactorDomain 279) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0279

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock03 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 3 i) := by
  fin_cases i
  · exact EntropyRow0210.numerical
  · exact EntropyRow0211.numerical
  · exact EntropyRow0212.numerical
  · exact EntropyRow0213.numerical
  · exact EntropyRow0214.numerical
  · exact EntropyRow0215.numerical
  · exact EntropyRow0216.numerical
  · exact EntropyRow0217.numerical
  · exact EntropyRow0218.numerical
  · exact EntropyRow0219.numerical
  · exact EntropyRow0220.numerical
  · exact EntropyRow0221.numerical
  · exact EntropyRow0222.numerical
  · exact EntropyRow0223.numerical
  · exact EntropyRow0224.numerical
  · exact EntropyRow0225.numerical
  · exact EntropyRow0226.numerical
  · exact EntropyRow0227.numerical
  · exact EntropyRow0228.numerical
  · exact EntropyRow0229.numerical
  · exact EntropyRow0230.numerical
  · exact EntropyRow0231.numerical
  · exact EntropyRow0232.numerical
  · exact EntropyRow0233.numerical
  · exact EntropyRow0234.numerical
  · exact EntropyRow0235.numerical
  · exact EntropyRow0236.numerical
  · exact EntropyRow0237.numerical
  · exact EntropyRow0238.numerical
  · exact EntropyRow0239.numerical
  · exact EntropyRow0240.numerical
  · exact EntropyRow0241.numerical
  · exact EntropyRow0242.numerical
  · exact EntropyRow0243.numerical
  · exact EntropyRow0244.numerical
  · exact EntropyRow0245.numerical
  · exact EntropyRow0246.numerical
  · exact EntropyRow0247.numerical
  · exact EntropyRow0248.numerical
  · exact EntropyRow0249.numerical
  · exact EntropyRow0250.numerical
  · exact EntropyRow0251.numerical
  · exact EntropyRow0252.numerical
  · exact EntropyRow0253.numerical
  · exact EntropyRow0254.numerical
  · exact EntropyRow0255.numerical
  · exact EntropyRow0256.numerical
  · exact EntropyRow0257.numerical
  · exact EntropyRow0258.numerical
  · exact EntropyRow0259.numerical
  · exact EntropyRow0260.numerical
  · exact EntropyRow0261.numerical
  · exact EntropyRow0262.numerical
  · exact EntropyRow0263.numerical
  · exact EntropyRow0264.numerical
  · exact EntropyRow0265.numerical
  · exact EntropyRow0266.numerical
  · exact EntropyRow0267.numerical
  · exact EntropyRow0268.numerical
  · exact EntropyRow0269.numerical
  · exact EntropyRow0270.numerical
  · exact EntropyRow0271.numerical
  · exact EntropyRow0272.numerical
  · exact EntropyRow0273.numerical
  · exact EntropyRow0274.numerical
  · exact EntropyRow0275.numerical
  · exact EntropyRow0276.numerical
  · exact EntropyRow0277.numerical
  · exact EntropyRow0278.numerical
  · exact EntropyRow0279.numerical
end SingularValueBounds.KL.Certificates
