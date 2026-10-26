import SingularValueBounds.KL.Certificates.EndpointMeanEntropyAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanSmall
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer entropy certificates, independently checked by Lean's kernel. -/
namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy00
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨431,6111,200⟩,⟨6111,8000,195⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1568320125780844) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2339689114284711)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1915561063170168) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2585768002840893))) (.branch (.branch (.leaf 1733266126544277) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2117029788701409) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2013777377421405) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1648731575998764) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2459652921034783)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2225576539257241)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2718349789616320))) (.branch (.branch (.leaf 1822135200553980) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2170624721864449)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2651230221439300))) (.branch (.branch (.leaf 1777145216984561) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1608023268480333) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2398921212670000)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1964055348907627) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1868264203185063) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2281919595192519)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2064758233395649) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1690470497540275) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2521922207833186)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 0) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 0*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 0) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 0) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 0 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 0) (endpointSmallBound 0)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 0 :=
  endpointSmallNumerical_le_of_runs 0 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy00

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy01
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨431,6111,200⟩,⟨6111,8000,195⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1568343946195928) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2339815916903190)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1915621769516861) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2585943059946367))) (.branch (.branch (.leaf 1733305453576888) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2117119113312243) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2013851393185520) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1648762492157268) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2459802371233233)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2225683383082827)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2718553706757594))) (.branch (.branch (.leaf 1822184403278256) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2170722515963995)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2651419282555361))) (.branch (.branch (.leaf 1777189288946379) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1608050481167761) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2399058986539436)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1964122472500523) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1868318943483595) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2282036098422333)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2064839640943161) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1690505445708116) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2522084073790321)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 1) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 1*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 1) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 1) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 1 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 1) (endpointSmallBound 1)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 1 :=
  endpointSmallNumerical_le_of_runs 1 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy01

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy02
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨431,6111,200⟩,⟨6111,8000,195⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1568383653055606) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2340027318815455)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1915722969372203) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2586234923126499))) (.branch (.branch (.leaf 1733371010952757) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2117268026777086) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2013974782665384) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1648814027858335) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2460051535867517)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2225861506506248)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2718893694388772))) (.branch (.branch (.leaf 1822266424640672) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2170885550495998)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2651734497510945))) (.branch (.branch (.leaf 1777262756568336) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1608095843106155) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2399288681937337)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1964234371226863) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1868410196826641) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2282230327351692)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2064975354340722) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1690563703081078) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2522353941032693)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 2) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 2*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 2) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 2) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 2 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 2) (endpointSmallBound 2)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 2 :=
  endpointSmallNumerical_le_of_runs 2 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy02

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy03
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨431,6111,200⟩,⟨6111,8000,195⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1568439254459770) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2340323414405664)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1915864695102428) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2586643742452405))) (.branch (.branch (.leaf 1733462815759188) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2117476585917590) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2014147589177409) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1648886195092293) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2460400534581510)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2226110983222469)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2719369939223278))) (.branch (.branch (.leaf 1822381288438697) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2171113890342161)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2652176033791189))) (.branch (.branch (.leaf 1777365640117977) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1608159364132865) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2399610405214823)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1964391082581426) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1868537991067612) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2282502365548381)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2065165423333417) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1690645283984446) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2522731943727531)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 3) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 3*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 3) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 3) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 3 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 3) (endpointSmallBound 3)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 3 :=
  endpointSmallNumerical_le_of_runs 3 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy03

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy04
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨431,6111,200⟩,⟨6111,8000,195⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1568510762061656) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2340704336605588)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1916046992558137) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2587169728956346))) (.branch (.branch (.leaf 1733580892320389) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2117744870956569) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2014369873805023) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1648979010957428) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2460849535649664)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2226431917124589)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2719982703653660))) (.branch (.branch (.leaf 1822529028423902) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2171407626926520)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2652744126948687))) (.branch (.branch (.leaf 1777497968341382) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1608241058436420) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2400024306099394)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1964592659607625) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1868702365635859) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2282852330691622)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2065409918071453) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1690750208927904) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2523218270524527)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 4) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 4*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 4) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 4) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 4 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 4) (endpointSmallBound 4)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 4 :=
  endpointSmallNumerical_le_of_runs 4 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy04

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy05
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨431,6111,200⟩,⟨6111,8000,195⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1568598190917683) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2341170256629690)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1916269920790291) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2587813154507411))) (.branch (.branch (.leaf 1733725272015687) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2118072985245905) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2014641715291783) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1649092497518544) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2461398755840664)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2226824442026697)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2720732325728016))) (.branch (.branch (.leaf 1822709688097821) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2171766878041329)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2653439080456055))) (.branch (.branch (.leaf 1777659778289267) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1608340944317934) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2400530577505174)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1964839170628881) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1868903371332162) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2283280374355032)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2065708928917276) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1690878504297058) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2523813164458419)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 5) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 5*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 5) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 5) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 5 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 5) (endpointSmallBound 5)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 5 :=
  endpointSmallNumerical_le_of_runs 5 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy05

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy06
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨431,6111,200⟩,⟨6111,8000,195⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1568701559451833) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2341721384188341)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1916533552085935) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2588574352138665))) (.branch (.branch (.leaf 1733895993247864) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2118461055313674) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2014963210020431) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1649226681783981) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2462048460684692)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2227288721799175)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2721619219640914))) (.branch (.branch (.leaf 1822923320706109) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2172191787912152)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2654261266096135))) (.branch (.branch (.leaf 1777851115305921) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1608459044179855) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2401129455695333)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1965130699298053) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1869141070351535) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2283786682177351)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2066062566506018) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1691030202413053) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2524516923240138)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 6) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 6*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 6) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 6) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 6 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 6) (endpointSmallBound 6)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 6 :=
  endpointSmallNumerical_le_of_runs 6 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy06

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy07
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨431,6111,200⟩,⟨6111,8000,195⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1568820889467119) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2342357967694598)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1916837972027382) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2589453716517896))) (.branch (.branch (.leaf 1734093101465096) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2118909231012854) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2015334472119053) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1649381595714185) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2462798964782523)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2227824950531640)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2722643876293991))) (.branch (.branch (.leaf 1823169989280655) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2172682527350697)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2655211124470336))) (.branch (.branch (.leaf 1778072033071755) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1608595384529106) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2401821220574581)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1965467344647091) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1869415536321295) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2284371474051981)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2066470961850145) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1691205341520344) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2525329899627274)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 7) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 7*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 7) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 7) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 7 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 7) (endpointSmallBound 7)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 7 :=
  endpointSmallNumerical_le_of_runs 7 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy07

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy08
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨431,6111,200⟩,⟨6111,8000,195⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1568956206152476) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2343080294581295)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1917183279566085) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2590451704458114))) (.branch (.branch (.leaf 1734316649199695) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2119417685651380) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2015755633566259) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1649557276244790) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2463650632203994)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2228433352756865)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2723806864020021))) (.branch (.branch (.leaf 1823449766685396) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2173239293933165)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2656289165628044))) (.branch (.branch (.leaf 1778322593629835) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1608749995994802) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2402606196037724)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1965849221195184) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1869726854355258) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2285035004375593)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2066934266463141) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1691403965816424) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2526252501894795)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 8) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 8*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 8) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 8) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 8 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 8) (endpointSmallBound 8)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 8 :=
  endpointSmallNumerical_le_of_runs 8 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy08

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy09
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨432,6111,200⟩,⟨6111,8000,195⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1569107538099035) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2343888691628027)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1917569587105177) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2591568835554570))) (.branch (.branch (.leaf 1734566696102795) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2119986616189928) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2016226844316191) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1649753765304695) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2464603876964123)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2229114183690024)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2725108829400548))) (.branch (.branch (.leaf 1823762735671485) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2173862312222032)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2657495969768407))) (.branch (.branch (.leaf 1778602867442095) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1608922913347576) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2403484750361841)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1966276459038231) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1870075121134364) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2285777562339992)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2067452652513621) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1691626125485026) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2527285194367156)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 9) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 9*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 9) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 9) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 9 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 9) (endpointSmallBound 9)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 9 :=
  endpointSmallNumerical_le_of_runs 9 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy09

