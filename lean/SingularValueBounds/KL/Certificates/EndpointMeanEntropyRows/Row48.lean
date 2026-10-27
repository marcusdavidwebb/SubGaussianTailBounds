import SingularValueBounds.KL.Certificates.EndpointMeanEntropyAssembly
import SingularValueBounds.KL.Certificates.EndpointPrefactorEvaluation

-- Elaborate the finite corner checks sequentially.
set_option Elab.async false

/-! Exact integer entropy certificates, independently checked by Lean's kernel.
Each corner is checked separately. Adjacent boxes reuse their shared vertices after
checking that the previous rate table contains the same prefactor values. -/
namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox48_24
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1049,1073,116⟩,⟨1073,1129,117⟩,⟨1129,1190,118⟩,⟨1190,1260,119⟩,⟨1260,1338,120⟩,⟨1338,1427,121⟩,⟨1427,1529,122⟩,⟨1529,1648,123⟩,⟨1648,1788,124⟩,⟨1788,1955,125⟩,⟨1955,2070,126⟩,⟨2070,2152,125⟩,⟨2152,2242,124⟩,⟨2242,2340,123⟩,⟨2340,2446,122⟩,⟨2446,2562,121⟩,⟨2562,2690,120⟩,⟨2690,2832,119⟩,⟨2832,2989,118⟩,⟨2989,3165,117⟩,⟨3165,3363,116⟩,⟨3363,3587,115⟩,⟨3587,3843,114⟩,⟨3843,4139,113⟩,⟨4139,4484,112⟩,⟨4484,4891,111⟩,⟨4891,5380,110⟩,⟨5380,5978,109⟩,⟨5978,6725,108⟩,⟨6725,7686,107⟩,⟨7686,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3440047341090105) (.leaf 0))) (.branch (.branch (.leaf 2394014518554134) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2789374315902202) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3977868167420851) (.leaf 0))) (.branch (.branch (.leaf 2571239980732030) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3067485197070730) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3681247361512474) (.leaf 0))) (.branch (.branch (.leaf 2478357766231384) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2919283499098667) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2674238748865373) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3238800597721925) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3554851228609880) (.leaf 0))) (.branch (.branch (.leaf 2435203573901033) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2852286907644420) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2621360602260036) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3149885181305208) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3821352416342382) (.leaf 0))) (.branch (.branch (.leaf 2523641687148261) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2990833373443611) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2730141632321189) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3335150618453747) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3478361681039784) (.leaf 0))) (.branch (.branch (.leaf 2408598530273496) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2811980331374723) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4031104232006891) (.leaf 0))) (.branch (.branch (.leaf 2589260051705327) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3096457050603700) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3726057688744699) (.leaf 0))) (.branch (.branch (.leaf 2494543102066703) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2944794059398804) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2694377156658559) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3271958846603274) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3596215935219348) (.leaf 0))) (.branch (.branch (.leaf 2450561732635111) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2876283996455473) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2640400712918718) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3180846530614374) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3870084746425754) (.leaf 0))) (.branch (.branch (.leaf 2540712381120673) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3017995854497407) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2751465318015867) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3370746307116684) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3725759275283953) (.leaf 0))) (.branch (.branch (.leaf 2450265545563435) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2903407416291748) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4512944155828678) (.leaf 0))) (.branch (.branch (.leaf 2649936850483568) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3241217640289872) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4063879284702269) (.leaf 0))) (.branch (.branch (.leaf 2544645888551083) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3058978452674702) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2768483132007698) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3458951605308289) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3883995000991799) (.leaf 0))) (.branch (.branch (.leaf 2496215057168999) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2978286262774414) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2707379614873862) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3344942676560759) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4270945218561931) (.leaf 0))) (.branch (.branch (.leaf 2595796010261176) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3146295438888779) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2833663680202393) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3585101691509562) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3772582128804669) (.leaf 0))) (.branch (.branch (.leaf 2466206290125095) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2929015062729975) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4583573248481758) (.leaf 0))) (.branch (.branch (.leaf 2669933434832615) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3275023784141216) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4120556392490519) (.leaf 0))) (.branch (.branch (.leaf 2562461575807264) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3088264940361774) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2791042518877191) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3498435380585673) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3935355755242783) (.leaf 0))) (.branch (.branch (.leaf 2513058959410273) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3005643263570891) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2728604167653275) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3381417118386511) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4333939149780680) (.leaf 0))) (.branch (.branch (.leaf 2614659681074214) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3177720012846026) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2857678633322761) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3628005043204503) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 24) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 48 24 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 24 (0 : Fin 4)) (endpointMeanCornerA 48 24 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 24 (1 : Fin 4)) (endpointMeanCornerA 48 24 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 24 (2 : Fin 4)) (endpointMeanCornerA 48 24 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 24 (3 : Fin 4)) (endpointMeanCornerA 48 24 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 24 h) (endpointMeanCornerA 48 24 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 48 24) (prefactors h) runs ≤
      endpointMeanCorner 48 24 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 48 24 h ≤ endpointMeanCorner 48 24 h :=
  endpointMeanNumericCorner_le_of_runs 48 24 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox48_24

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox48_25
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1056,1099,116⟩,⟨1099,1156,117⟩,⟨1156,1219,118⟩,⟨1219,1290,119⟩,⟨1290,1371,120⟩,⟨1371,1462,121⟩,⟨1462,1568,122⟩,⟨1568,1690,123⟩,⟨1690,1834,124⟩,⟨1834,2005,125⟩,⟨2005,2070,126⟩,⟨2070,2152,125⟩,⟨2152,2242,124⟩,⟨2242,2340,123⟩,⟨2340,2446,122⟩,⟨2446,2562,121⟩,⟨2562,2690,120⟩,⟨2690,2832,119⟩,⟨2832,2989,118⟩,⟨2989,3165,117⟩,⟨3165,3363,116⟩,⟨3363,3587,115⟩,⟨3587,3843,114⟩,⟨3843,4139,113⟩,⟨4139,4484,112⟩,⟨4484,4891,111⟩,⟨4891,5380,110⟩,⟨5380,5978,109⟩,⟨5978,6725,108⟩,⟨6725,7686,107⟩,⟨7686,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3478361681039784) (.leaf 0))) (.branch (.branch (.leaf 2408598530273496) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2811980331374723) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4031104232006891) (.leaf 0))) (.branch (.branch (.leaf 2589260051705327) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3096457050603700) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3726057688744699) (.leaf 0))) (.branch (.branch (.leaf 2494543102066703) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2944794059398804) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2694377156658559) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3271958846603274) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3596215935219348) (.leaf 0))) (.branch (.branch (.leaf 2450561732635111) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2876283996455473) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2640400712918718) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3180846530614374) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3870084746425754) (.leaf 0))) (.branch (.branch (.leaf 2540712381120673) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3017995854497407) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2751465318015867) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3370746307116684) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3568066518740023) (.leaf 0))) (.branch (.branch (.leaf 2442462759328964) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2864645301725625) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4156203157831127) (.leaf 0))) (.branch (.branch (.leaf 2631165821725710) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3164100819081455) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3831149102695663) (.leaf 0))) (.branch (.branch (.leaf 2532152699923665) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3004287518458175) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2741249256783983) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3349477604982673) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3693141497064489) (.leaf 0))) (.branch (.branch (.leaf 2486236118790232) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2932218047075461) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2684697123601007) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3253180914473793) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3984482577619040) (.leaf 0))) (.branch (.branch (.leaf 2580394481325837) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3081377404351105) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2801118935540416) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3454022669637550) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3772582128804669) (.leaf 0))) (.branch (.branch (.leaf 2466206290125095) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2929015062729975) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4583573248481758) (.leaf 0))) (.branch (.branch (.leaf 2669933434832615) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3275023784141216) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4120556392490519) (.leaf 0))) (.branch (.branch (.leaf 2562461575807264) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3088264940361774) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2791042518877191) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3498435380585673) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3935355755242783) (.leaf 0))) (.branch (.branch (.leaf 2513058959410273) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3005643263570891) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2728604167653275) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3381417118386511) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4333939149780680) (.leaf 0))) (.branch (.branch (.leaf 2614659681074214) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3177720012846026) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2857678633322761) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3628005043204503) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3882464254169605) (.leaf 0))) (.branch (.branch (.leaf 2503246018779000) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2988742884029776) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4750158730168115) (.leaf 0))) (.branch (.branch (.leaf 2716476627255015) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3354082084280850) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4253863926181417) (.leaf 0))) (.branch (.branch (.leaf 2603891569564031) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3156657776593132) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2843602676381411) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3590920110333786) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4056016511452104) (.leaf 0))) (.branch (.branch (.leaf 2552212803228656) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3069489539128996) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2778029301362843) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3466781642098897) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4482298340594617) (.leaf 0))) (.branch (.branch (.leaf 2658545864634581) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3251155660724859) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2913659973383778) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3728590347205245) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 25) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 48 25 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 25 (0 : Fin 4)) (endpointMeanCornerA 48 25 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 25 (0 : Fin 4) = endpointMeanCornerK 48 24 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 25 (0 : Fin 4) = endpointMeanCornerA 48 24 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_24.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_24.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_24.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_24.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 25 (1 : Fin 4)) (endpointMeanCornerA 48 25 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 25 (2 : Fin 4)) (endpointMeanCornerA 48 25 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 25 (2 : Fin 4) = endpointMeanCornerK 48 24 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 25 (2 : Fin 4) = endpointMeanCornerA 48 24 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_24.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_24.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_24.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_24.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 25 (3 : Fin 4)) (endpointMeanCornerA 48 25 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 25 h) (endpointMeanCornerA 48 25 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 48 25) (prefactors h) runs ≤
      endpointMeanCorner 48 25 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 48 25 h ≤ endpointMeanCorner 48 25 h :=
  endpointMeanNumericCorner_le_of_runs 48 25 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox48_25

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox48_26
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1066,1081,115⟩,⟨1081,1134,116⟩,⟨1134,1193,117⟩,⟨1193,1259,118⟩,⟨1259,1333,119⟩,⟨1333,1417,120⟩,⟨1417,1512,121⟩,⟨1512,1621,122⟩,⟨1621,1749,123⟩,⟨1749,1898,124⟩,⟨1898,2025,125⟩,⟨2025,2056,125⟩,⟨2056,2072,125⟩,⟨2072,2088,125⟩,⟨2088,2152,125⟩,⟨2152,2242,124⟩,⟨2242,2340,123⟩,⟨2340,2446,122⟩,⟨2446,2562,121⟩,⟨2562,2690,120⟩,⟨2690,2832,119⟩,⟨2832,2989,118⟩,⟨2989,3165,117⟩,⟨3165,3363,116⟩,⟨3363,3587,115⟩,⟨3587,3843,114⟩,⟨3843,4139,113⟩,⟨4139,4484,112⟩,⟨4484,4891,111⟩,⟨4891,5380,110⟩,⟨5380,5978,109⟩,⟨5978,6725,108⟩,⟨6725,7686,107⟩,⟨7686,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3568066518740023) (.leaf 0))) (.branch (.branch (.leaf 2442462759328964) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2864645301725625) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2631165821725710) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3164100819081455) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3831149102695663) (.leaf 0))) (.branch (.branch (.leaf 2532152699923665) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3004287518458175) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2741249256783983) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3349477604982673) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3693141497064489) (.leaf 0))) (.branch (.branch (.leaf 2486236118790232) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2932218047075461) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2684697123601007) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3253180914473793) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3984482577619040) (.leaf 0))) (.branch (.branch (.leaf 2580394481325837) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3081377404351105) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2801118935540416) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3454022669637550) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3660084789787547) (.leaf 0))) (.branch (.branch (.leaf 2476803110077238) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2918296622895248) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2673749813912251) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3233222302037104) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3939204562350911) (.leaf 0))) (.branch (.branch (.leaf 2570329328211889) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3064982919520777) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2788936756403402) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3428832926162032) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3792679406084608) (.leaf 0))) (.branch (.branch (.leaf 2522429839680158) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2989239826870526) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2729736668455975) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3327160226196901) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4102261953310500) (.leaf 0))) (.branch (.branch (.leaf 2620696356161300) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3146090043131207) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2851668614417117) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3539356425958735) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3882464254169605) (.leaf 0))) (.branch (.branch (.leaf 2503246018779000) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2988742884029776) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2716476627255015) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3354082084280850) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4253863926181417) (.leaf 0))) (.branch (.branch (.leaf 2603891569564031) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3156657776593132) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2843602676381411) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3590920110333786) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4056016511452104) (.leaf 0))) (.branch (.branch (.leaf 2552212803228656) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3069489539128996) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2778029301362843) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3466781642098897) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4482298340594617) (.leaf 0))) (.branch (.branch (.leaf 2658545864634581) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3251155660724859) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2913659973383778) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3728590347205245) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3995546861608220) (.leaf 0))) (.branch (.branch (.leaf 2540842043759069) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3049688661728168) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2763831176519726) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3435048833101450) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4391484202338639) (.leaf 0))) (.branch (.branch (.leaf 2645991405319169) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3226565243252283) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2897152632549823) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3685849768830348) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4180376810725513) (.leaf 0))) (.branch (.branch (.leaf 2591976669935690) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3134692045798107) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2828349707413913) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3554301209585391) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4635736155897336) (.leaf 0))) (.branch (.branch (.leaf 2703168663029159) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3326288372648852) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2970737976448986) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3831964347269101) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 26) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 48 26 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 26 (0 : Fin 4)) (endpointMeanCornerA 48 26 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 26 (0 : Fin 4) = endpointMeanCornerK 48 25 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 26 (0 : Fin 4) = endpointMeanCornerA 48 25 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_25.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_25.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_25.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_25.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 26 (1 : Fin 4)) (endpointMeanCornerA 48 26 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 26 (2 : Fin 4)) (endpointMeanCornerA 48 26 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 26 (2 : Fin 4) = endpointMeanCornerK 48 25 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 26 (2 : Fin 4) = endpointMeanCornerA 48 25 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_25.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_25.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_25.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_25.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 26 (3 : Fin 4)) (endpointMeanCornerA 48 26 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 26 h) (endpointMeanCornerA 48 26 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 48 26) (prefactors h) runs ≤
      endpointMeanCorner 48 26 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 48 26 h ≤ endpointMeanCorner 48 26 h :=
  endpointMeanNumericCorner_le_of_runs 48 26 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox48_26

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox48_27
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1076,1114,115⟩,⟨1114,1169,116⟩,⟨1169,1231,117⟩,⟨1231,1299,118⟩,⟨1299,1376,119⟩,⟨1376,1463,120⟩,⟨1463,1561,121⟩,⟨1561,1675,122⟩,⟨1675,1807,123⟩,⟨1807,1962,124⟩,⟨1962,2057,125⟩,⟨2057,2104,125⟩,⟨2104,2152,125⟩,⟨2152,2242,124⟩,⟨2242,2340,123⟩,⟨2340,2446,122⟩,⟨2446,2562,121⟩,⟨2562,2690,120⟩,⟨2690,2832,119⟩,⟨2832,2989,118⟩,⟨2989,3165,117⟩,⟨3165,3363,116⟩,⟨3363,3587,115⟩,⟨3587,3843,114⟩,⟨3843,4139,113⟩,⟨4139,4484,112⟩,⟨4484,4891,111⟩,⟨4891,5380,110⟩,⟨5380,5978,109⟩,⟨5978,6725,108⟩,⟨6725,7686,107⟩,⟨7686,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3660084789787547) (.leaf 0))) (.branch (.branch (.leaf 2476803110077238) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2918296622895248) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2673749813912251) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3233222302037104) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3939204562350911) (.leaf 0))) (.branch (.branch (.leaf 2570329328211889) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3064982919520777) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2788936756403402) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3428832926162032) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3792679406084608) (.leaf 0))) (.branch (.branch (.leaf 2522429839680158) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2989239826870526) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2729736668455975) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3327160226196901) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4102261953310500) (.leaf 0))) (.branch (.branch (.leaf 2620696356161300) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3146090043131207) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2851668614417117) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3539356425958735) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3754476156224996) (.leaf 0))) (.branch (.branch (.leaf 2511626276657609) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2972952768034352) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2717023004922968) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3303853780937634) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4050307666994204) (.leaf 0))) (.branch (.branch (.leaf 2609081535906322) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3126904545333008) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2837453840422819) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3510068321711831) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3894900070514991) (.leaf 0))) (.branch (.branch (.leaf 2559150455591015) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3047370488515034) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2775531814597549) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3402821872443327) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4223522830318141) (.leaf 0))) (.branch (.branch (.leaf 2661627685573181) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3212161725309226) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2903130525188768) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3626798405260592) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3995546861608220) (.leaf 0))) (.branch (.branch (.leaf 2540842043759069) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3049688661728168) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2763831176519726) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3435048833101450) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4391484202338639) (.leaf 0))) (.branch (.branch (.leaf 2645991405319169) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3226565243252283) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2897152632549823) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3685849768830348) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4180376810725513) (.leaf 0))) (.branch (.branch (.leaf 2591976669935690) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3134692045798107) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2828349707413913) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3554301209585391) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4635736155897336) (.leaf 0))) (.branch (.branch (.leaf 2703168663029159) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3326288372648852) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2970737976448986) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3831964347269101) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4111923169971802) (.leaf 0))) (.branch (.branch (.leaf 2579002720029381) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3111877232120139) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2812011226476608) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3517970100103132) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4533556746066763) (.leaf 0))) (.branch (.branch (.leaf 2688771913108170) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3298020883403959) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2951711027003038) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3783288990276066) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4308550083637385) (.leaf 0))) (.branch (.branch (.leaf 2632360063781478) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3201279592820580) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2879581602506477) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3644030225339409) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4794426446911375) (.leaf 0))) (.branch (.branch (.leaf 2748540440090257) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3403157366987507) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3028934125922385) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3938204359121350) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 27) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 48 27 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 27 (0 : Fin 4)) (endpointMeanCornerA 48 27 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 27 (0 : Fin 4) = endpointMeanCornerK 48 26 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 27 (0 : Fin 4) = endpointMeanCornerA 48 26 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_26.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_26.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_26.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_26.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 27 (1 : Fin 4)) (endpointMeanCornerA 48 27 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 27 (2 : Fin 4)) (endpointMeanCornerA 48 27 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 27 (2 : Fin 4) = endpointMeanCornerK 48 26 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 27 (2 : Fin 4) = endpointMeanCornerA 48 26 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_26.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_26.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_26.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_26.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 27 (3 : Fin 4)) (endpointMeanCornerA 48 27 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 27 h) (endpointMeanCornerA 48 27 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 48 27) (prefactors h) runs ≤
      endpointMeanCorner 48 27 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 48 27 h ≤ endpointMeanCorner 48 27 h :=
  endpointMeanNumericCorner_le_of_runs 48 27 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox48_27

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox48_28
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1086,1095,114⟩,⟨1095,1147,115⟩,⟨1147,1204,116⟩,⟨1204,1268,117⟩,⟨1268,1339,118⟩,⟨1339,1419,119⟩,⟨1419,1509,120⟩,⟨1509,1611,121⟩,⟨1611,1729,122⟩,⟨1729,1865,123⟩,⟨1865,2026,124⟩,⟨2026,2152,125⟩,⟨2152,2242,124⟩,⟨2242,2340,123⟩,⟨2340,2446,122⟩,⟨2446,2562,121⟩,⟨2562,2690,120⟩,⟨2690,2832,119⟩,⟨2832,2989,118⟩,⟨2989,3165,117⟩,⟨3165,3363,116⟩,⟨3363,3587,115⟩,⟨3587,3843,114⟩,⟨3843,4139,113⟩,⟨4139,4484,112⟩,⟨4484,4891,111⟩,⟨4891,5380,110⟩,⟨5380,5978,109⟩,⟨5978,6725,108⟩,⟨6725,7686,107⟩,⟨7686,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3754476156224996) (.leaf 0))) (.branch (.branch (.leaf 2511626276657609) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2972952768034352) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2717023004922968) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3303853780937634) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4050307666994204) (.leaf 0))) (.branch (.branch (.leaf 2609081535906322) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3126904545333008) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2837453840422819) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3510068321711831) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3894900070514991) (.leaf 0))) (.branch (.branch (.leaf 2559150455591015) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3047370488515034) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2775531814597549) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3402821872443327) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4223522830318141) (.leaf 0))) (.branch (.branch (.leaf 2661627685573181) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3212161725309226) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2903130525188768) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3626798405260592) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3851301818742902) (.leaf 0))) (.branch (.branch (.leaf 2546939047327122) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3028632556273355) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2760996549067136) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3376028242456006) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4164544373781280) (.leaf 0))) (.branch (.branch (.leaf 2648418000872657) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3190077169223837) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2886814940512644) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3593228334072143) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3999875796240519) (.leaf 0))) (.branch (.branch (.leaf 2596405636868838) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3106631596031712) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2822095238292909) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3480204110522890) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4348368120135109) (.leaf 0))) (.branch (.branch (.leaf 2703198300693801) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3279620992434270) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2955521130215733) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3716400692489660) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4111923169971802) (.leaf 0))) (.branch (.branch (.leaf 2579002720029381) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3111877232120139) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2812011226476608) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3517970100103132) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4533556746066763) (.leaf 0))) (.branch (.branch (.leaf 2688771913108170) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3298020883403959) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2951711027003038) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3783288990276066) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4308550083637385) (.leaf 0))) (.branch (.branch (.leaf 2632360063781478) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3201279592820580) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2879581602506477) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3644030225339409) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4794426446911375) (.leaf 0))) (.branch (.branch (.leaf 2748540440090257) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3403157366987507) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3028934125922385) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3938204359121350) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4231689113250812) (.leaf 0))) (.branch (.branch (.leaf 2617736528036465) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3175333937956871) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2861031167535943) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3602893066892865) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4680225596362635) (.leaf 0))) (.branch (.branch (.leaf 2732244098067023) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3371058982958922) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3007296850377971) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3883304117543081) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4440653238622769) (.leaf 0))) (.branch (.branch (.leaf 2673372637093825) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3269281601408562) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2931741497085061) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3736024467306234) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4958549016125738) (.leaf 0))) (.branch (.branch (.leaf 2794673767172935) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3481802768428814) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3088270326063454) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4047389842041572) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 28) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 48 28 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 28 (0 : Fin 4)) (endpointMeanCornerA 48 28 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 28 (0 : Fin 4) = endpointMeanCornerK 48 27 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 28 (0 : Fin 4) = endpointMeanCornerA 48 27 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_27.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_27.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_27.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_27.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 28 (1 : Fin 4)) (endpointMeanCornerA 48 28 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 28 (2 : Fin 4)) (endpointMeanCornerA 48 28 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 28 (2 : Fin 4) = endpointMeanCornerK 48 27 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 28 (2 : Fin 4) = endpointMeanCornerA 48 27 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_27.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_27.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_27.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_27.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 28 (3 : Fin 4)) (endpointMeanCornerA 48 28 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 28 h) (endpointMeanCornerA 48 28 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 48 28) (prefactors h) runs ≤
      endpointMeanCorner 48 28 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 48 28 h ≤ endpointMeanCorner 48 28 h :=
  endpointMeanNumericCorner_le_of_runs 48 28 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox48_28

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox48_29
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1094,1120,114⟩,⟨1120,1174,115⟩,⟨1174,1233,116⟩,⟨1233,1298,117⟩,⟨1298,1371,118⟩,⟨1371,1453,119⟩,⟨1453,1545,120⟩,⟨1545,1651,121⟩,⟨1651,1772,122⟩,⟨1772,1912,123⟩,⟨1912,2077,124⟩,⟨2077,2152,125⟩,⟨2152,2242,124⟩,⟨2242,2340,123⟩,⟨2340,2446,122⟩,⟨2446,2562,121⟩,⟨2562,2690,120⟩,⟨2690,2832,119⟩,⟨2832,2989,118⟩,⟨2989,3165,117⟩,⟨3165,3363,116⟩,⟨3363,3587,115⟩,⟨3587,3843,114⟩,⟨3843,4139,113⟩,⟨4139,4484,112⟩,⟨4484,4891,111⟩,⟨4891,5380,110⟩,⟨5380,5978,109⟩,⟨5978,6725,108⟩,⟨6725,7686,107⟩,⟨7686,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3851301818742902) (.leaf 0))) (.branch (.branch (.leaf 2546939047327122) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3028632556273355) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2760996549067136) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3376028242456006) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4164544373781280) (.leaf 0))) (.branch (.branch (.leaf 2648418000872657) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3190077169223837) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2886814940512644) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3593228334072143) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3999875796240519) (.leaf 0))) (.branch (.branch (.leaf 2596405636868838) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3106631596031712) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2822095238292909) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3480204110522890) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4348368120135109) (.leaf 0))) (.branch (.branch (.leaf 2703198300693801) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3279620992434270) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2955521130215733) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3716400692489660) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3910591727573896) (.leaf 0))) (.branch (.branch (.leaf 2568364579299599) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3062539738426895) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2787721552752276) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3420087542807413) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4234627190710405) (.leaf 0))) (.branch (.branch (.leaf 2672303982260472) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3228591715424321) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2916842825720737) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3644067081569333) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4064214468411150) (.leaf 0))) (.branch (.branch (.leaf 2619018569633377) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3142740001954453) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2850407418577337) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3527475577627890) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4425039759610012) (.leaf 0))) (.branch (.branch (.leaf 2728451674074012) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3320774690811041) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2987408225884638) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3771221160797586) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4231689113250812) (.leaf 0))) (.branch (.branch (.leaf 2617736528036465) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3175333937956871) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2861031167535943) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3602893066892865) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4680225596362635) (.leaf 0))) (.branch (.branch (.leaf 2732244098067023) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3371058982958922) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3007296850377971) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3883304117543081) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4440653238622769) (.leaf 0))) (.branch (.branch (.leaf 2673372637093825) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3269281601408562) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2931741497085061) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3736024467306234) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4958549016125738) (.leaf 0))) (.branch (.branch (.leaf 2794673767172935) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3481802768428814) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3088270326063454) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4047389842041572) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4305216656252985) (.leaf 0))) (.branch (.branch (.leaf 2641255491569254) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3214027402226554) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2890852360102388) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3654827716018514) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4770494794109494) (.leaf 0))) (.branch (.branch (.leaf 2758664058752163) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3415655969924116) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3041149544084847) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3944577882590507) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4521851447684389) (.leaf 0))) (.branch (.branch (.leaf 2698286258827662) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3310774220929876) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2963489853738918) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3792332050837170) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5059707147193174) (.leaf 0))) (.branch (.branch (.leaf 2822724616011582) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3529859723101978) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3124428543044915) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4114348835946050) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 29) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 48 29 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 29 (0 : Fin 4)) (endpointMeanCornerA 48 29 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 29 (0 : Fin 4) = endpointMeanCornerK 48 28 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 29 (0 : Fin 4) = endpointMeanCornerA 48 28 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_28.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_28.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_28.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_28.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 29 (1 : Fin 4)) (endpointMeanCornerA 48 29 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 29 (2 : Fin 4)) (endpointMeanCornerA 48 29 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 29 (2 : Fin 4) = endpointMeanCornerK 48 28 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 29 (2 : Fin 4) = endpointMeanCornerA 48 28 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_28.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_28.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_28.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_28.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 29 (3 : Fin 4)) (endpointMeanCornerA 48 29 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 29 h) (endpointMeanCornerA 48 29 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 48 29) (prefactors h) runs ≤
      endpointMeanCorner 48 29 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 48 29 h ≤ endpointMeanCorner 48 29 h :=
  endpointMeanNumericCorner_le_of_runs 48 29 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox48_29

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox48_30
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1098,1136,114⟩,⟨1136,1190,115⟩,⟨1190,1250,116⟩,⟨1250,1317,117⟩,⟨1317,1391,118⟩,⟨1391,1474,119⟩,⟨1474,1568,120⟩,⟨1568,1675,121⟩,⟨1675,1798,122⟩,⟨1798,1941,123⟩,⟨1941,2109,124⟩,⟨2109,2152,125⟩,⟨2152,2242,124⟩,⟨2242,2340,123⟩,⟨2340,2446,122⟩,⟨2446,2562,121⟩,⟨2562,2690,120⟩,⟨2690,2832,119⟩,⟨2832,2989,118⟩,⟨2989,3165,117⟩,⟨3165,3363,116⟩,⟨3363,3587,115⟩,⟨3587,3843,114⟩,⟨3843,4139,113⟩,⟨4139,4484,112⟩,⟨4484,4891,111⟩,⟨4891,5380,110⟩,⟨5380,5978,109⟩,⟨5978,6725,108⟩,⟨6725,7686,107⟩,⟨7686,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3910591727573896) (.leaf 0))) (.branch (.branch (.leaf 2568364579299599) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3062539738426895) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2787721552752276) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3420087542807413) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4234627190710405) (.leaf 0))) (.branch (.branch (.leaf 2672303982260472) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3228591715424321) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2916842825720737) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3644067081569333) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4064214468411150) (.leaf 0))) (.branch (.branch (.leaf 2619018569633377) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3142740001954453) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2850407418577337) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3527475577627890) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4425039759610012) (.leaf 0))) (.branch (.branch (.leaf 2728451674074012) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3320774690811041) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2987408225884638) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3771221160797586) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3950624556360488) (.leaf 0))) (.branch (.branch (.leaf 2582748305783828) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3085355159202064) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2805681781180488) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3449779393876797) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4282003064242312) (.leaf 0))) (.branch (.branch (.leaf 2688347531810583) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3254526065015959) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2937034739400443) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3678358560975860) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4107680837941312) (.leaf 0))) (.branch (.branch (.leaf 2634203165521737) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3167045132791023) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2869439828471334) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3559346067739878) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4476903776268451) (.leaf 0))) (.branch (.branch (.leaf 2745418186202940) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3348496985462371) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3008857188942169) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3808216659383147) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4305216656252985) (.leaf 0))) (.branch (.branch (.leaf 2641255491569254) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3214027402226554) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2890852360102388) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3654827716018514) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4770494794109494) (.leaf 0))) (.branch (.branch (.leaf 2758664058752163) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3415655969924116) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3041149544084847) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3944577882590507) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4521851447684389) (.leaf 0))) (.branch (.branch (.leaf 2698286258827662) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3310774220929876) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2963489853738918) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3792332050837170) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5059707147193174) (.leaf 0))) (.branch (.branch (.leaf 2822724616011582) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3529859723101978) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3124428543044915) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4114348835946050) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4354943419657389) (.leaf 0))) (.branch (.branch (.leaf 2657052075593913) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3240084638773247) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2910905640966567) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3689866054030458) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4831639452148027) (.leaf 0))) (.branch (.branch (.leaf 2776419143263252) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3445714587125038) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3063929450938068) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3985963247345440) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4576806768610944) (.leaf 0))) (.branch (.branch (.leaf 2715024192585255) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3338728117743499) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2984846200659537) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3830341121556096) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5128289821019338) (.leaf 0))) (.branch (.branch (.leaf 2841581426638240) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3562265628923845) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3148768910231647) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4159602458292981) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 30) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 48 30 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 30 (0 : Fin 4)) (endpointMeanCornerA 48 30 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 30 (0 : Fin 4) = endpointMeanCornerK 48 29 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 30 (0 : Fin 4) = endpointMeanCornerA 48 29 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_29.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_29.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_29.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_29.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 30 (1 : Fin 4)) (endpointMeanCornerA 48 30 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 30 (2 : Fin 4)) (endpointMeanCornerA 48 30 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 30 (2 : Fin 4) = endpointMeanCornerK 48 29 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 30 (2 : Fin 4) = endpointMeanCornerA 48 29 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_29.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_29.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_29.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_29.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 30 (3 : Fin 4)) (endpointMeanCornerA 48 30 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 30 h) (endpointMeanCornerA 48 30 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 48 30) (prefactors h) runs ≤
      endpointMeanCorner 48 30 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 48 30 h ≤ endpointMeanCorner 48 30 h :=
  endpointMeanNumericCorner_le_of_runs 48 30 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox48_30

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox48_31
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1105,1107,113⟩,⟨1107,1158,114⟩,⟨1158,1213,115⟩,⟨1213,1275,116⟩,⟨1275,1343,117⟩,⟨1343,1419,118⟩,⟨1419,1504,119⟩,⟨1504,1600,120⟩,⟨1600,1710,121⟩,⟨1710,1836,122⟩,⟨1836,1982,123⟩,⟨1982,2112,124⟩,⟨2112,2144,124⟩,⟨2144,2152,124⟩,⟨2152,2160,124⟩,⟨2160,2177,124⟩,⟨2177,2242,124⟩,⟨2242,2340,123⟩,⟨2340,2446,122⟩,⟨2446,2562,121⟩,⟨2562,2690,120⟩,⟨2690,2832,119⟩,⟨2832,2989,118⟩,⟨2989,3165,117⟩,⟨3165,3363,116⟩,⟨3363,3587,115⟩,⟨3587,3843,114⟩,⟨3843,4139,113⟩,⟨4139,4484,112⟩,⟨4484,4891,111⟩,⟨4891,5380,110⟩,⟨5380,5978,109⟩,⟨5978,6725,108⟩,⟨6725,7686,107⟩,⟨7686,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3950624556360488) (.leaf 0))) (.branch (.branch (.leaf 2582748305783828) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3085355159202064) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2805681781180488) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3449779393876797) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4282003064242312) (.leaf 0))) (.branch (.branch (.leaf 2688347531810583) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3254526065015959) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2937034739400443) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3678358560975860) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4107680837941312) (.leaf 0))) (.branch (.branch (.leaf 2634203165521737) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3167045132791023) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2869439828471334) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3559346067739878) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2745418186202940) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3348496985462371) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3008857188942169) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3808216659383147) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4052508767129786) (.leaf 0))) (.branch (.branch (.leaf 2619061032508675) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3143140107470874) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2851090219546925) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3525141678838322) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4402774612660071) (.leaf 0))) (.branch (.branch (.leaf 2728879070226326) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3320277017137282) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2988128175238408) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3765505680450510) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4218391451616878) (.leaf 0))) (.branch (.branch (.leaf 2672550936845505) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3228633509666055) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2917578690291885) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3640287761177284) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2788297482726043) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3418819457344751) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3063155763257276) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3902300996259891) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4354943419657389) (.leaf 0))) (.branch (.branch (.leaf 2657052075593913) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3240084638773247) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2910905640966567) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3689866054030458) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4831639452148027) (.leaf 0))) (.branch (.branch (.leaf 2776419143263252) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3445714587125038) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3063929450938068) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3985963247345440) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4576806768610944) (.leaf 0))) (.branch (.branch (.leaf 2715024192585255) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3338728117743499) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2984846200659537) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3830341121556096) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2841581426638240) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3562265628923845) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3148768910231647) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4159602458292981) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4481787693011252) (.leaf 0))) (.branch (.branch (.leaf 2696958099795277) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3306155721426029) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2961649543268928) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3778938548522612) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4987951823026708) (.leaf 0))) (.branch (.branch (.leaf 2821308412572722) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3522023517222733) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3121628541308042) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4091336276603722) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4717134860928612) (.leaf 0))) (.branch (.branch (.leaf 2757324685696079) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3409649826251843) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3038912827222293) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3927038817832503) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2889276415394844) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3644587949115366) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3210452649292356) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4274926134199473) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 31) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 48 31 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 31 (0 : Fin 4)) (endpointMeanCornerA 48 31 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 31 (0 : Fin 4) = endpointMeanCornerK 48 30 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 31 (0 : Fin 4) = endpointMeanCornerA 48 30 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_30.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_30.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_30.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_30.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 31 (1 : Fin 4)) (endpointMeanCornerA 48 31 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 31 (2 : Fin 4)) (endpointMeanCornerA 48 31 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 31 (2 : Fin 4) = endpointMeanCornerK 48 30 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 31 (2 : Fin 4) = endpointMeanCornerA 48 30 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_30.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_30.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_30.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_30.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 31 (3 : Fin 4)) (endpointMeanCornerA 48 31 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 31 h) (endpointMeanCornerA 48 31 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 48 31) (prefactors h) runs ≤
      endpointMeanCorner 48 31 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 48 31 h ≤ endpointMeanCorner 48 31 h :=
  endpointMeanNumericCorner_le_of_runs 48 31 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox48_31

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox48_32
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1115,1137,113⟩,⟨1137,1189,114⟩,⟨1189,1247,115⟩,⟨1247,1310,116⟩,⟨1310,1380,117⟩,⟨1380,1459,118⟩,⟨1459,1547,119⟩,⟨1547,1646,120⟩,⟨1646,1759,121⟩,⟨1759,1890,122⟩,⟨1890,2041,123⟩,⟨2041,2141,124⟩,⟨2141,2191,124⟩,⟨2191,2242,124⟩,⟨2242,2340,123⟩,⟨2340,2446,122⟩,⟨2446,2562,121⟩,⟨2562,2690,120⟩,⟨2690,2832,119⟩,⟨2832,2989,118⟩,⟨2989,3165,117⟩,⟨3165,3363,116⟩,⟨3363,3587,115⟩,⟨3587,3843,114⟩,⟨3843,4139,113⟩,⟨4139,4484,112⟩,⟨4484,4891,111⟩,⟨4891,5380,110⟩,⟨5380,5978,109⟩,⟨5978,6725,108⟩,⟨6725,7686,107⟩,⟨7686,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4052508767129786) (.leaf 0))) (.branch (.branch (.leaf 2619061032508675) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3143140107470874) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2851090219546925) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3525141678838322) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4402774612660071) (.leaf 0))) (.branch (.branch (.leaf 2728879070226326) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3320277017137282) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2988128175238408) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3765505680450510) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4218391451616878) (.leaf 0))) (.branch (.branch (.leaf 2672550936845505) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3228633509666055) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2917578690291885) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3640287761177284) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2788297482726043) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3418819457344751) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3063155763257276) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3902300996259891) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4157020509889527) (.leaf 0))) (.branch (.branch (.leaf 2655884306126240) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3202007297515469) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2897233568867524) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3602150293418696) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4526952456376636) (.leaf 0))) (.branch (.branch (.leaf 2770021692434966) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3387356330936616) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3040110446046801) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3854717476412464) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4332085948525821) (.leaf 0))) (.branch (.branch (.leaf 2711456961072745) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3291419573345996) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2966525148770985) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3723070117930870) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2831846489269843) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3490618785880461) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3118434222953278) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3998709744596711) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4481787693011252) (.leaf 0))) (.branch (.branch (.leaf 2696958099795277) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3306155721426029) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2961649543268928) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3778938548522612) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4987951823026708) (.leaf 0))) (.branch (.branch (.leaf 2821308412572722) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3522023517222733) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3121628541308042) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4091336276603722) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4717134860928612) (.leaf 0))) (.branch (.branch (.leaf 2757324685696079) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3409649826251843) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3038912827222293) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3927038817832503) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2889276415394844) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3644587949115366) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3210452649292356) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4274926134199473) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4612326496496106) (.leaf 0))) (.branch (.branch (.leaf 2737463468955744) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3373574110846878) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3013278030624347) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3870161231980667) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5149321184918836) (.leaf 0))) (.branch (.branch (.leaf 2866923453602941) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3600022387872795) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3180414205335419) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4199494950035328) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4861765510572604) (.leaf 0))) (.branch (.branch (.leaf 2800284226973873) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3482078063162728) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3093958800763541) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4026177665998117) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2937771948500152) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3728812700261702) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3273344760187574) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4393447122916009) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 32) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 48 32 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 32 (0 : Fin 4)) (endpointMeanCornerA 48 32 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 32 (0 : Fin 4) = endpointMeanCornerK 48 31 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 32 (0 : Fin 4) = endpointMeanCornerA 48 31 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_31.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_31.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_31.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_31.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 32 (1 : Fin 4)) (endpointMeanCornerA 48 32 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 32 (2 : Fin 4)) (endpointMeanCornerA 48 32 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 32 (2 : Fin 4) = endpointMeanCornerK 48 31 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 32 (2 : Fin 4) = endpointMeanCornerA 48 31 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_31.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_31.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_31.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_31.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 32 (3 : Fin 4)) (endpointMeanCornerA 48 32 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 32 h) (endpointMeanCornerA 48 32 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 48 32) (prefactors h) runs ≤
      endpointMeanCorner 48 32 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 48 32 h ≤ endpointMeanCorner 48 32 h :=
  endpointMeanNumericCorner_le_of_runs 48 32 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox48_32

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox48_33
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1125,1167,113⟩,⟨1167,1221,114⟩,⟨1221,1280,115⟩,⟨1280,1345,116⟩,⟨1345,1418,117⟩,⟨1418,1499,118⟩,⟨1499,1590,119⟩,⟨1590,1692,120⟩,⟨1692,1809,121⟩,⟨1809,1943,122⟩,⟨1943,2099,123⟩,⟨2099,2242,124⟩,⟨2242,2340,123⟩,⟨2340,2446,122⟩,⟨2446,2562,121⟩,⟨2562,2690,120⟩,⟨2690,2832,119⟩,⟨2832,2989,118⟩,⟨2989,3165,117⟩,⟨3165,3363,116⟩,⟨3363,3587,115⟩,⟨3587,3843,114⟩,⟨3843,4139,113⟩,⟨4139,4484,112⟩,⟨4484,4891,111⟩,⟨4891,5380,110⟩,⟨5380,5978,109⟩,⟨5978,6725,108⟩,⟨6725,7686,107⟩,⟨7686,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4157020509889527) (.leaf 0))) (.branch (.branch (.leaf 2655884306126240) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3202007297515469) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2897233568867524) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3602150293418696) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4526952456376636) (.leaf 0))) (.branch (.branch (.leaf 2770021692434966) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3387356330936616) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3040110446046801) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3854717476412464) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4332085948525821) (.leaf 0))) (.branch (.branch (.leaf 2711456961072745) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3291419573345996) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2966525148770985) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3723070117930870) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2831846489269843) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3490618785880461) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3118434222953278) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3998709744596711) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4264227547095830) (.leaf 0))) (.branch (.branch (.leaf 2693225304784605) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3261976998407578) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2944123723277600) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3680841202573269) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4654632668083106) (.leaf 0))) (.branch (.branch (.leaf 2811784611592876) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3455790843207818) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3092997014234667) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3946042864867480) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4448844750579437) (.leaf 0))) (.branch (.branch (.leaf 2750929365046130) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3355426614811311) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3016292752470820) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3807734995803472) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2876075665696060) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3563925986838949) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3174710251281933) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4097500330409622) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4612326496496106) (.leaf 0))) (.branch (.branch (.leaf 2737463468955744) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3373574110846878) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3013278030624347) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3870161231980667) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5149321184918836) (.leaf 0))) (.branch (.branch (.leaf 2866923453602941) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3600022387872795) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3180414205335419) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4199494950035328) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4861765510572604) (.leaf 0))) (.branch (.branch (.leaf 2800284226973873) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3482078063162728) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3093958800763541) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4026177665998117) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2937771948500152) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3728812700261702) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3273344760187574) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4393447122916009) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4746667438855550) (.leaf 0))) (.branch (.branch (.leaf 2778577184582898) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3442367281014631) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3065806523421897) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3963586009458105) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5315911140730346) (.leaf 0))) (.branch (.branch (.leaf 2913276000663665) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3679748624564833) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3240306905081298) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4310512909002909) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5010830636955802) (.leaf 0))) (.branch (.branch (.leaf 2843913084490115) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3556044830353652) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3150001860886530) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4127819293400583) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2987081462821884) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3814983846667166) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3337468914674447) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4515254068939261) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 33) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 48 33 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 33 (0 : Fin 4)) (endpointMeanCornerA 48 33 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 33 (0 : Fin 4) = endpointMeanCornerK 48 32 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 33 (0 : Fin 4) = endpointMeanCornerA 48 32 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_32.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_32.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_32.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_32.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 33 (1 : Fin 4)) (endpointMeanCornerA 48 33 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 33 (2 : Fin 4)) (endpointMeanCornerA 48 33 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 33 (2 : Fin 4) = endpointMeanCornerK 48 32 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 33 (2 : Fin 4) = endpointMeanCornerA 48 32 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_32.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_32.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_32.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_32.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 33 (3 : Fin 4)) (endpointMeanCornerA 48 33 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 33 h) (endpointMeanCornerA 48 33 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 48 33) (prefactors h) runs ≤
      endpointMeanCorner 48 33 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 48 33 h ≤ endpointMeanCorner 48 33 h :=
  endpointMeanNumericCorner_le_of_runs 48 33 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox48_33

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox48_34
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1132,1136,112⟩,⟨1136,1186,113⟩,⟨1186,1242,114⟩,⟨1242,1302,115⟩,⟨1302,1369,116⟩,⟨1369,1443,117⟩,⟨1443,1525,118⟩,⟨1525,1618,119⟩,⟨1618,1723,120⟩,⟨1723,1842,121⟩,⟨1842,1979,122⟩,⟨1979,2138,123⟩,⟨2138,2242,124⟩,⟨2242,2340,123⟩,⟨2340,2446,122⟩,⟨2446,2562,121⟩,⟨2562,2690,120⟩,⟨2690,2832,119⟩,⟨2832,2989,118⟩,⟨2989,3165,117⟩,⟨3165,3363,116⟩,⟨3363,3587,115⟩,⟨3587,3843,114⟩,⟨3843,4139,113⟩,⟨4139,4484,112⟩,⟨4484,4891,111⟩,⟨4891,5380,110⟩,⟨5380,5978,109⟩,⟨5978,6725,108⟩,⟨6725,7686,107⟩,⟨7686,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4264227547095830) (.leaf 0))) (.branch (.branch (.leaf 2693225304784605) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3261976998407578) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2944123723277600) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3680841202573269) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4654632668083106) (.leaf 0))) (.branch (.branch (.leaf 2811784611592876) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3455790843207818) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3092997014234667) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3946042864867480) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4448844750579437) (.leaf 0))) (.branch (.branch (.leaf 2750929365046130) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3355426614811311) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3016292752470820) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3807734995803472) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2876075665696060) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3563925986838949) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3174710251281933) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4097500330409622) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4300574143361250) (.leaf 0))) (.branch (.branch (.leaf 2705788609523091) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3282215458953086) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2959921814877443) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3707451677863882) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4697988036632624) (.leaf 0))) (.branch (.branch (.leaf 2825845040776182) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3478908218855223) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3110829536439366) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3976962969255546) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4488459519129614) (.leaf 0))) (.branch (.branch (.leaf 2764214116849793) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3377037714366828) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3033066804811837) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3836382331157212) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2890971704726366) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3588702257559999) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3193693711527568) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4130969952059194) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4746667438855550) (.leaf 0))) (.branch (.branch (.leaf 2778577184582898) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3442367281014631) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3065806523421897) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3963586009458105) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5315911140730346) (.leaf 0))) (.branch (.branch (.leaf 2913276000663665) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3679748624564833) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3240306905081298) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4310512909002909) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5010830636955802) (.leaf 0))) (.branch (.branch (.leaf 2843913084490115) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3556044830353652) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3150001860886530) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4127819293400583) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2987081462821884) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3814983846667166) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3337468914674447) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4515254068939261) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4792311721465779) (.leaf 0))) (.branch (.branch (.leaf 2792418519811836) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3465608673634105) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3083518726111304) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3995226107313669) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5372630294114267) (.leaf 0))) (.branch (.branch (.leaf 2928892795332614) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3706714483547024) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3260520738282346) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4348167299667920) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5061527832792757) (.leaf 0))) (.branch (.branch (.leaf 2858606571660264) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3581047943859968) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3168907567998605) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4162266884008698) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3003701207143988) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3844147839072792) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3359121578334498) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4556602270968842) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 34) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 48 34 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 34 (0 : Fin 4)) (endpointMeanCornerA 48 34 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 34 (0 : Fin 4) = endpointMeanCornerK 48 33 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 34 (0 : Fin 4) = endpointMeanCornerA 48 33 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_33.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_33.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_33.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_33.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 34 (1 : Fin 4)) (endpointMeanCornerA 48 34 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 34 (2 : Fin 4)) (endpointMeanCornerA 48 34 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 34 (2 : Fin 4) = endpointMeanCornerK 48 33 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 34 (2 : Fin 4) = endpointMeanCornerA 48 33 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_33.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_33.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_33.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_33.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 34 (3 : Fin 4)) (endpointMeanCornerA 48 34 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 34 h) (endpointMeanCornerA 48 34 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 48 34) (prefactors h) runs ≤
      endpointMeanCorner 48 34 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 48 34 h ≤ endpointMeanCorner 48 34 h :=
  endpointMeanNumericCorner_le_of_runs 48 34 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox48_34

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox48_35
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1136,1150,112⟩,⟨1150,1201,113⟩,⟨1201,1257,114⟩,⟨1257,1319,115⟩,⟨1319,1386,116⟩,⟨1386,1462,117⟩,⟨1462,1545,118⟩,⟨1545,1639,119⟩,⟨1639,1746,120⟩,⟨1746,1867,121⟩,⟨1867,2006,122⟩,⟨2006,2167,123⟩,⟨2167,2242,124⟩,⟨2242,2340,123⟩,⟨2340,2446,122⟩,⟨2446,2562,121⟩,⟨2562,2690,120⟩,⟨2690,2832,119⟩,⟨2832,2989,118⟩,⟨2989,3165,117⟩,⟨3165,3363,116⟩,⟨3363,3587,115⟩,⟨3587,3843,114⟩,⟨3843,4139,113⟩,⟨4139,4484,112⟩,⟨4484,4891,111⟩,⟨4891,5380,110⟩,⟨5380,5978,109⟩,⟨5978,6725,108⟩,⟨6725,7686,107⟩,⟨7686,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4300574143361250) (.leaf 0))) (.branch (.branch (.leaf 2705788609523091) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3282215458953086) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2959921814877443) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3707451677863882) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4697988036632624) (.leaf 0))) (.branch (.branch (.leaf 2825845040776182) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3478908218855223) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3110829536439366) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3976962969255546) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4488459519129614) (.leaf 0))) (.branch (.branch (.leaf 2764214116849793) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3377037714366828) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3033066804811837) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3836382331157212) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2890971704726366) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3588702257559999) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3193693711527568) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4130969952059194) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4374199388757441) (.leaf 0))) (.branch (.branch (.leaf 2731091307554632) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3323069858833983) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2991772769412604) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3761251156931164) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4785914030148117) (.leaf 0))) (.branch (.branch (.leaf 2854177179760887) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3525607932926518) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3146803611199221) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4039531920731974) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4568750447228159) (.leaf 0))) (.branch (.branch (.leaf 2790976393915950) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3420678377973710) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3066895277249631) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3894325204469775) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2920995635233678) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3638772727358195) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3232001850611304) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4198731598459707) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4792311721465779) (.leaf 0))) (.branch (.branch (.leaf 2792418519811836) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3465608673634105) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3083518726111304) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3995226107313669) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5372630294114267) (.leaf 0))) (.branch (.branch (.leaf 2928892795332614) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3706714483547024) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3260520738282346) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4348167299667920) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5061527832792757) (.leaf 0))) (.branch (.branch (.leaf 2858606571660264) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3581047943859968) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3168907567998605) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4162266884008698) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3003701207143988) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3844147839072792) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3359121578334498) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4556602270968842) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4884921263099593) (.leaf 0))) (.branch (.branch (.leaf 2820308383377164) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3512563266151391) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3119250710864125) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4059266038984111) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5487890586220337) (.leaf 0))) (.branch (.branch (.leaf 2960377977785491) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3761240481614809) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3301327487942793) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4424465741654102) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5164466204232398) (.leaf 0))) (.branch (.branch (.leaf 2888221686294397) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3631582809490270) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3207060068524462) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4232026883181777) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3037218620761044) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3903146368630952) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3402849248234990) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4640438074406826) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 35) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 48 35 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 35 (0 : Fin 4)) (endpointMeanCornerA 48 35 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 35 (0 : Fin 4) = endpointMeanCornerK 48 34 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 35 (0 : Fin 4) = endpointMeanCornerA 48 34 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_34.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_34.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_34.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_34.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 35 (1 : Fin 4)) (endpointMeanCornerA 48 35 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 35 (2 : Fin 4)) (endpointMeanCornerA 48 35 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 35 (2 : Fin 4) = endpointMeanCornerK 48 34 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 35 (2 : Fin 4) = endpointMeanCornerA 48 34 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_34.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_34.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_34.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_34.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 35 (3 : Fin 4)) (endpointMeanCornerA 48 35 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 35 h) (endpointMeanCornerA 48 35 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 48 35) (prefactors h) runs ≤
      endpointMeanCorner 48 35 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 48 35 h ≤ endpointMeanCorner 48 35 h :=
  endpointMeanNumericCorner_le_of_runs 48 35 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox48_35

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox48_36
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1145,1174,112⟩,⟨1174,1226,113⟩,⟨1226,1283,114⟩,⟨1283,1346,115⟩,⟨1346,1416,116⟩,⟨1416,1493,117⟩,⟨1493,1579,118⟩,⟨1579,1675,119⟩,⟨1675,1784,120⟩,⟨1784,1908,121⟩,⟨1908,2050,122⟩,⟨2050,2216,123⟩,⟨2216,2242,124⟩,⟨2242,2340,123⟩,⟨2340,2446,122⟩,⟨2446,2562,121⟩,⟨2562,2690,120⟩,⟨2690,2832,119⟩,⟨2832,2989,118⟩,⟨2989,3165,117⟩,⟨3165,3363,116⟩,⟨3363,3587,115⟩,⟨3587,3843,114⟩,⟨3843,4139,113⟩,⟨4139,4484,112⟩,⟨4484,4891,111⟩,⟨4891,5380,110⟩,⟨5380,5978,109⟩,⟨5978,6725,108⟩,⟨6725,7686,107⟩,⟨7686,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4374199388757441) (.leaf 0))) (.branch (.branch (.leaf 2731091307554632) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3323069858833983) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2991772769412604) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3761251156931164) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4785914030148117) (.leaf 0))) (.branch (.branch (.leaf 2854177179760887) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3525607932926518) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3146803611199221) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4039531920731974) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4568750447228159) (.leaf 0))) (.branch (.branch (.leaf 2790976393915950) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3420678377973710) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3066895277249631) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3894325204469775) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2920995635233678) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3638772727358195) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3232001850611304) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4198731598459707) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4487007337504074) (.leaf 0))) (.branch (.branch (.leaf 2769489695848893) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3385306914206246) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3040192989523631) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3843417709958772) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4920898111042870) (.leaf 0))) (.branch (.branch (.leaf 2897208889998482) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3596835532203795) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3201546242005258) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4135235905289780) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4691887853881359) (.leaf 0))) (.branch (.branch (.leaf 2831606412862390) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3487199068484121) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3118346730074929) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3982884527122520) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2966617187030526) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3715191339624221) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3290327348184574) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4302463847304100) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4884921263099593) (.leaf 0))) (.branch (.branch (.leaf 2820308383377164) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3512563266151391) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3119250710864125) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4059266038984111) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5487890586220337) (.leaf 0))) (.branch (.branch (.leaf 2960377977785491) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3761240481614809) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3301327487942793) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4424465741654102) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5164466204232398) (.leaf 0))) (.branch (.branch (.leaf 2888221686294397) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3631582809490270) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3207060068524462) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4232026883181777) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3037218620761044) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3903146368630952) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3402849248234990) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4640438074406826) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5027201937794896) (.leaf 0))) (.branch (.branch (.leaf 2862666339262246) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3584190672146837) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3173626555653136) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4157255761810134) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5665433881234525) (.leaf 0))) (.branch (.branch (.leaf 3008241501787288) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3844537060520273) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3363497193909542) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4541431034386814) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5322812345312526) (.leaf 0))) (.branch (.branch (.leaf 2933220622906925) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3708725376466541) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3265151811760990) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4338865213554104) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3088197314037454) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3993346285926251) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3469510369160379) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4769092767234530) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 36) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 48 36 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 36 (0 : Fin 4)) (endpointMeanCornerA 48 36 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 36 (0 : Fin 4) = endpointMeanCornerK 48 35 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 36 (0 : Fin 4) = endpointMeanCornerA 48 35 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_35.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_35.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_35.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_35.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 36 (1 : Fin 4)) (endpointMeanCornerA 48 36 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 36 (2 : Fin 4)) (endpointMeanCornerA 48 36 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 48 36 (2 : Fin 4) = endpointMeanCornerK 48 35 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 48 36 (2 : Fin 4) = endpointMeanCornerA 48 35 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_35.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox48_35.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox48_35.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox48_35.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 36 (3 : Fin 4)) (endpointMeanCornerA 48 36 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 48 36 h) (endpointMeanCornerA 48 36 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 48 36) (prefactors h) runs ≤
      endpointMeanCorner 48 36 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 48 36 h ≤ endpointMeanCorner 48 36 h :=
  endpointMeanNumericCorner_le_of_runs 48 36 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox48_36

namespace SingularValueBounds.KL.Certificates
theorem endpointMeanEntropyRow48 (ai : Fin 42)
    (hactive : endpointMeanActive 48 ai) (h : Fin 4) :
    endpointMeanNumericCorner 48 ai h ≤ endpointMeanCorner 48 ai h := by
  fin_cases ai
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 0) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 1) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 2) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 3) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 4) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 5) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 6) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 7) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 8) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 9) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 10) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 11) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 12) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 13) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 14) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 15) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 16) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 17) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 18) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 19) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 20) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 21) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 22) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 23) hactive)
  · exact EndpointEntropyBox48_24.numerical h
  · exact EndpointEntropyBox48_25.numerical h
  · exact EndpointEntropyBox48_26.numerical h
  · exact EndpointEntropyBox48_27.numerical h
  · exact EndpointEntropyBox48_28.numerical h
  · exact EndpointEntropyBox48_29.numerical h
  · exact EndpointEntropyBox48_30.numerical h
  · exact EndpointEntropyBox48_31.numerical h
  · exact EndpointEntropyBox48_32.numerical h
  · exact EndpointEntropyBox48_33.numerical h
  · exact EndpointEntropyBox48_34.numerical h
  · exact EndpointEntropyBox48_35.numerical h
  · exact EndpointEntropyBox48_36.numerical h
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 37) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 38) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 39) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 40) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 48 41) hactive)
end SingularValueBounds.KL.Certificates
