import SingularValueBounds.KL.Certificates.EndpointMeanEntropyAssembly
import SingularValueBounds.KL.Certificates.EndpointPrefactorEvaluation

-- Elaborate the finite corner checks sequentially.
set_option Elab.async false

/-! Exact integer entropy certificates, independently checked by Lean's kernel.
Each corner is checked separately. Adjacent boxes reuse their shared vertices after
checking that the previous rate table contains the same prefactor values. -/
namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox54_32
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1264,1317,99⟩,⟨1317,1407,100⟩,⟨1407,1510,101⟩,⟨1510,1630,102⟩,⟨1630,1772,103⟩,⟨1772,1941,104⟩,⟨1941,2146,105⟩,⟨2146,2401,106⟩,⟨2401,2725,107⟩,⟨2725,3153,108⟩,⟨3153,3741,109⟩,⟨3741,4345,110⟩,⟨4345,4496,110⟩,⟨4496,4571,110⟩,⟨4571,4647,110⟩,⟨4647,4950,110⟩,⟨4950,5500,109⟩,⟨5500,6187,108⟩,⟨6187,7071,107⟩,⟨7071,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3539180030977805) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4464274346850291) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3017362025809212) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3923433385184634) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2828815573695475) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3247972978595677) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3716764219773001) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2746559472503890) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3126470671931459) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4168146215029872) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2918665164591752) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3384423243024934) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3567340564265769) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4510119519826731) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3036791921513530) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3958628091035085) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2845355477259705) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3271135453263791) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3748116581994119) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2761887337216923) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3147640462880806) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4208057594549151) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2936563310390473) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3409889784374961) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3939706380289130) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5590329568309173) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3217830331008272) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4551349020934404) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2979702501363690) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3524165450013111) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4212178244939700) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2878857503919458) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3360531984049760) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4990189955365854) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3091913374116385) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3714477110610409) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3975654046550942) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5661473781709259) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3240801513278415) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4599544347897244) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2998807006114997) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3552427038835780) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4253453157431195) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2896394777961561) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3385925364945093) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5047775221768516) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3112811702408004) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3746189809066154) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 54 32) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 54 32 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 32 (0 : Fin 4)) (endpointMeanCornerA 54 32 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 32 (1 : Fin 4)) (endpointMeanCornerA 54 32 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 32 (2 : Fin 4)) (endpointMeanCornerA 54 32 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 32 (3 : Fin 4)) (endpointMeanCornerA 54 32 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 32 h) (endpointMeanCornerA 54 32 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 54 32) (prefactors h) runs ≤
      endpointMeanCorner 54 32 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 54 32 h ≤ endpointMeanCorner 54 32 h :=
  endpointMeanNumericCorner_le_of_runs 54 32 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox54_32

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox54_33
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1271,1340,99⟩,⟨1340,1432,100⟩,⟨1432,1538,101⟩,⟨1538,1661,102⟩,⟨1661,1805,103⟩,⟨1805,1978,104⟩,⟨1978,2187,105⟩,⟨2187,2447,106⟩,⟨2447,2779,107⟩,⟨2779,3215,108⟩,⟨3215,3815,109⟩,⟨3815,4382,110⟩,⟨4382,4666,110⟩,⟨4666,4950,110⟩,⟨4950,5500,109⟩,⟨5500,6187,108⟩,⟨6187,7071,107⟩,⟨7071,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3567340564265769) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4510119519826731) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3036791921513530) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3958628091035085) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2845355477259705) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3271135453263791) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3748116581994119) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2761887337216923) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3147640462880806) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4208057594549151) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2936563310390473) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3409889784374961) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3651004243741189) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4646939209856816) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3094346452241250) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4063396991518382) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2894292684668963) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3339839307287718) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3841350086830793) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2807214848227597) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3210389510203052) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4327007517464472) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2989548743696661) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3485485927591260) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3975654046550942) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5661473781709259) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3240801513278415) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4599544347897244) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2998807006114997) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3552427038835780) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4253453157431195) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2896394777961561) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3385925364945093) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5047775221768516) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3112811702408004) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3746189809066154) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4082696550782940) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5874813861620388) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3308938940109459) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4743467496706822) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3055394599678272) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3636401205913761) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4376520531268224) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2948307776209916) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3461309004445970) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5220057715532965) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3174754645005820) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3840513665856609) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 54 33) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 54 33 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 33 (0 : Fin 4)) (endpointMeanCornerA 54 33 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 54 33 (0 : Fin 4) = endpointMeanCornerK 54 32 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 54 33 (0 : Fin 4) = endpointMeanCornerA 54 32 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_32.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_32.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox54_32.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox54_32.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 33 (1 : Fin 4)) (endpointMeanCornerA 54 33 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 33 (2 : Fin 4)) (endpointMeanCornerA 54 33 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 54 33 (2 : Fin 4) = endpointMeanCornerK 54 32 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 54 33 (2 : Fin 4) = endpointMeanCornerA 54 32 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_32.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_32.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox54_32.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox54_32.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 33 (3 : Fin 4)) (endpointMeanCornerA 54 33 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 33 h) (endpointMeanCornerA 54 33 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 54 33) (prefactors h) runs ≤
      endpointMeanCorner 54 33 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 54 33 h ≤ endpointMeanCorner 54 33 h :=
  endpointMeanNumericCorner_le_of_runs 54 33 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox54_33

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox54_34
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1278,1281,98⟩,⟨1281,1364,99⟩,⟨1364,1457,100⟩,⟨1457,1565,101⟩,⟨1565,1690,102⟩,⟨1690,1838,103⟩,⟨1838,2014,104⟩,⟨2014,2228,105⟩,⟨2228,2493,106⟩,⟨2493,2831,107⟩,⟨2831,3277,108⟩,⟨3277,3889,109⟩,⟨3889,4419,110⟩,⟨4419,4684,110⟩,⟨4684,4950,110⟩,⟨4950,5500,109⟩,⟨5500,6187,108⟩,⟨6187,7071,107⟩,⟨7071,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3651004243741189) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2727209479555906) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4646939209856816) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3094346452241250) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4063396991518382) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2894292684668963) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3339839307287718) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3841350086830793) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2807214848227597) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3210389510203052) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4327007517464472) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2989548743696661) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3485485927591260) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3679325916836073) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2741385784461134) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4693461984517836) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3113772682267065) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4098932553740836) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2910791415129467) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3363059772965075) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3872940471246344) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2822488732086149) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3231582619932946) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4367400047968568) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3007422161421314) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3511055255443065) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4082696550782940) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2851518513281580) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5874813861620388) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3308938940109459) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4743467496706822) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3055394599678272) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3636401205913761) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4376520531268224) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2948307776209916) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3461309004445970) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5220057715532965) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3174754645005820) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3840513665856609) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4119014055030671) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2867631791426648) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5947698991280416) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3331968292421549) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4792435779351227) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3074493434653404) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3664831417221211) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4418329244681323) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2965818058852515) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3486808017724202) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5278782122920852) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3195675007763355) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3872479794317669) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 54 34) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 54 34 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 34 (0 : Fin 4)) (endpointMeanCornerA 54 34 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 34 (1 : Fin 4)) (endpointMeanCornerA 54 34 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 34 (2 : Fin 4)) (endpointMeanCornerA 54 34 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 34 (3 : Fin 4)) (endpointMeanCornerA 54 34 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 34 h) (endpointMeanCornerA 54 34 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 54 34) (prefactors h) runs ≤
      endpointMeanCorner 54 34 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 54 34 h ≤ endpointMeanCorner 54 34 h :=
  endpointMeanNumericCorner_le_of_runs 54 34 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox54_34

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox54_35
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1284,1298,98⟩,⟨1298,1381,99⟩,⟨1381,1476,100⟩,⟨1476,1586,101⟩,⟨1586,1713,102⟩,⟨1713,1863,103⟩,⟨1863,2041,104⟩,⟨2041,2259,105⟩,⟨2259,2528,106⟩,⟨2528,2871,107⟩,⟨2871,3323,108⟩,⟨3323,3945,109⟩,⟨3945,4447,110⟩,⟨4447,4698,110⟩,⟨4698,4950,110⟩,⟨4950,5500,109⟩,⟨5500,6187,108⟩,⟨6187,7071,107⟩,⟨7071,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3679325916836073) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2741385784461134) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4693461984517836) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3113772682267065) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4098932553740836) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2910791415129467) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3363059772965075) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3872940471246344) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2822488732086149) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3231582619932946) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4367400047968568) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3007422161421314) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3511055255443065) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3736630060314895) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2769959846828284) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4787909483368698) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3152991780130218) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4170938701736776) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2944071562051680) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3409986152476392) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3936902752833869) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2853286264765028) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3274389476423525) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4449319819302532) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3043490211607221) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3562758012621082) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4119014055030671) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2867631791426648) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5947698991280416) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3331968292421549) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4792435779351227) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3074493434653404) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3664831417221211) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4418329244681323) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2965818058852515) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3486808017724202) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5278782122920852) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3195675007763355) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3872479794317669) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4192621121104717) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2900132019568283) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 6096193189164102) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3378508947404364) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4891894107424055) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3113050003120192) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3722360399189140) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4503148677480680) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3001151227519313) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3538370971875525) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5398220276525786) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3237930212158059) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3937212466366750) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 54 35) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 54 35 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 35 (0 : Fin 4)) (endpointMeanCornerA 54 35 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 54 35 (0 : Fin 4) = endpointMeanCornerK 54 34 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 54 35 (0 : Fin 4) = endpointMeanCornerA 54 34 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_34.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_34.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox54_34.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox54_34.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 35 (1 : Fin 4)) (endpointMeanCornerA 54 35 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 35 (2 : Fin 4)) (endpointMeanCornerA 54 35 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 54 35 (2 : Fin 4) = endpointMeanCornerK 54 34 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 54 35 (2 : Fin 4) = endpointMeanCornerA 54 34 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_34.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_34.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox54_34.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox54_34.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 35 (3 : Fin 4)) (endpointMeanCornerA 54 35 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 35 h) (endpointMeanCornerA 54 35 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 54 35) (prefactors h) runs ≤
      endpointMeanCorner 54 35 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 54 35 h ≤ endpointMeanCorner 54 35 h :=
  endpointMeanNumericCorner_le_of_runs 54 35 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox54_35

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox54_36
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1292,1325,98⟩,⟨1325,1410,99⟩,⟨1410,1508,100⟩,⟨1508,1620,101⟩,⟨1620,1750,102⟩,⟨1750,1904,103⟩,⟨1904,2087,104⟩,⟨2087,2309,105⟩,⟨2309,2586,106⟩,⟨2586,2937,107⟩,⟨2937,3400,108⟩,⟨3400,4038,109⟩,⟨4038,4950,110⟩,⟨4950,5500,109⟩,⟨5500,6187,108⟩,⟨6187,7071,107⟩,⟨7071,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3736630060314895) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2769959846828284) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4787909483368698) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3152991780130218) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4170938701736776) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2944071562051680) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3409986152476392) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3936902752833869) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2853286264765028) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3274389476423525) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4449319819302532) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3043490211607221) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3562758012621082) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3824264031350891) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2813380347405647) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4933156253111010) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3212748578417312) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4281326606767255) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2994706585271552) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3481606296059750) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4034832268583498) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2900113795649427) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3339665298942181) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4575089545034710) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3098404964187070) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3641743194547273) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4192621121104717) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2900132019568283) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 6096193189164102) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3378508947404364) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4891894107424055) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3113050003120192) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3722360399189140) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4503148677480680) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3001151227519313) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3538370971875525) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5398220276525786) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3237930212158059) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3937212466366750) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4305505355709679) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2949574302867126) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 6325914705552949) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3449541654979510) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5044965096707029) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3171793366050681) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3810351541771031) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4633440621748838) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3054941808693790) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3617148633227955) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5582463593684393) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3302362932297317) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 4036346008381195) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 54 36) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 54 36 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 36 (0 : Fin 4)) (endpointMeanCornerA 54 36 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 54 36 (0 : Fin 4) = endpointMeanCornerK 54 35 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 54 36 (0 : Fin 4) = endpointMeanCornerA 54 35 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_35.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_35.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox54_35.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox54_35.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 36 (1 : Fin 4)) (endpointMeanCornerA 54 36 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 36 (2 : Fin 4)) (endpointMeanCornerA 54 36 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 54 36 (2 : Fin 4) = endpointMeanCornerK 54 35 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 54 36 (2 : Fin 4) = endpointMeanCornerA 54 35 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_35.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_35.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox54_35.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox54_35.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 36 (3 : Fin 4)) (endpointMeanCornerA 54 36 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 36 h) (endpointMeanCornerA 54 36 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 54 36) (prefactors h) runs ≤
      endpointMeanCorner 54 36 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 54 36 h ≤ endpointMeanCorner 54 36 h :=
  endpointMeanNumericCorner_le_of_runs 54 36 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox54_36

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox54_37
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1303,1357,98⟩,⟨1357,1445,99⟩,⟨1445,1546,100⟩,⟨1546,1661,101⟩,⟨1661,1795,102⟩,⟨1795,1953,103⟩,⟨1953,2142,104⟩,⟨2142,2371,105⟩,⟨2371,2655,106⟩,⟨2655,3016,107⟩,⟨3016,3493,108⟩,⟨3493,4149,109⟩,⟨4149,4950,110⟩,⟨4950,5500,109⟩,⟨5500,6187,108⟩,⟨6187,7071,107⟩,⟨7071,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3824264031350891) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2813380347405647) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4933156253111010) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3212748578417312) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4281326606767255) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2994706585271552) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3481606296059750) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4034832268583498) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2900113795649427) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3339665298942181) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4575089545034710) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3098404964187070) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3641743194547273) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3913953253443476) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2857481485961409) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5082809251541208) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3273637912147100) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4394636033893459) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3046212479162345) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3554730681812296) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4135197757649478) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2947709850069579) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3406242412292664) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4704414426285747) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3154310562750062) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3722479452168696) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4305505355709679) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2949574302867126) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 6325914705552949) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3449541654979510) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5044965096707029) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3171793366050681) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3810351541771031) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4633440621748838) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3054941808693790) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3617148633227955) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5582463593684393) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3302362932297317) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 4036346008381195) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4421428942083917) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2999859492406548) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 6564292767667054) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3522067815916486) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5202825790600435) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3231645218303517) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3900422665962055) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4767502370648603) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3109696495441004) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3697680186407291) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5772995205536207) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3368077821956149) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 4137975595309723) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 54 37) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 54 37 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 37 (0 : Fin 4)) (endpointMeanCornerA 54 37 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 54 37 (0 : Fin 4) = endpointMeanCornerK 54 36 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 54 37 (0 : Fin 4) = endpointMeanCornerA 54 36 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_36.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_36.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox54_36.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox54_36.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 37 (1 : Fin 4)) (endpointMeanCornerA 54 37 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 37 (2 : Fin 4)) (endpointMeanCornerA 54 37 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 54 37 (2 : Fin 4) = endpointMeanCornerK 54 36 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 54 37 (2 : Fin 4) = endpointMeanCornerA 54 36 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_36.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_36.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox54_36.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox54_36.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 37 (3 : Fin 4)) (endpointMeanCornerA 54 37 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 37 h) (endpointMeanCornerA 54 37 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 54 37) (prefactors h) runs ≤
      endpointMeanCorner 54 37 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 54 37 h ≤ endpointMeanCorner 54 37 h :=
  endpointMeanNumericCorner_le_of_runs 54 37 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox54_37

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox54_38
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1314,1390,98⟩,⟨1390,1481,99⟩,⟨1481,1584,100⟩,⟨1584,1702,101⟩,⟨1702,1840,102⟩,⟨1840,2003,103⟩,⟨2003,2196,104⟩,⟨2196,2432,105⟩,⟨2432,2724,106⟩,⟨2724,3096,107⟩,⟨3096,3586,108⟩,⟨3586,4260,109⟩,⟨4260,4950,110⟩,⟨4950,5500,109⟩,⟨5500,6187,108⟩,⟨6187,7071,107⟩,⟨7071,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3913953253443476) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2857481485961409) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5082809251541208) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3273637912147100) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4394636033893459) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3046212479162345) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3554730681812296) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4135197757649478) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2947709850069579) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3406242412292664) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4704414426285747) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3154310562750062) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3722479452168696) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4005745927728071) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2902273931834973) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5237002146700805) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3335681245597546) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4510944304008037) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3098604221809916) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3629390903422480) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4238059814286276) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2996087040871271) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3474146758052778) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4837394957277832) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3211224885474943) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3805005606261809) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4421428942083917) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2999859492406548) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 6564292767667054) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3522067815916486) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5202825790600435) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3231645218303517) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3900422665962055) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4767502370648603) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3109696495441004) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3697680186407291) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5772995205536207) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3368077821956149) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 4137975595309723) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4540473713259389) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3051001958294142) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 6811653578228174) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3596118829876369) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5365626062508517) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3292626477111156) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3992622939478043) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4905442997899306) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3165432567729590) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3780004679748919) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5970029733977735) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3435100395479963) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 4242164074096830) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 54 38) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 54 38 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 38 (0 : Fin 4)) (endpointMeanCornerA 54 38 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 54 38 (0 : Fin 4) = endpointMeanCornerK 54 37 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 54 38 (0 : Fin 4) = endpointMeanCornerA 54 37 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_37.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_37.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox54_37.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox54_37.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 38 (1 : Fin 4)) (endpointMeanCornerA 54 38 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 38 (2 : Fin 4)) (endpointMeanCornerA 54 38 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 54 38 (2 : Fin 4) = endpointMeanCornerK 54 37 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 54 38 (2 : Fin 4) = endpointMeanCornerA 54 37 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_37.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox54_37.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox54_37.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox54_37.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 38 (3 : Fin 4)) (endpointMeanCornerA 54 38 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 38 h) (endpointMeanCornerA 54 38 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 54 38) (prefactors h) runs ≤
      endpointMeanCorner 54 38 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 54 38 h ≤ endpointMeanCorner 54 38 h :=
  endpointMeanNumericCorner_le_of_runs 54 38 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox54_38

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox54_39
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1324,1340,97⟩,⟨1340,1423,98⟩,⟨1423,1516,99⟩,⟨1516,1622,100⟩,⟨1622,1743,101⟩,⟨1743,1885,102⟩,⟨1885,2052,103⟩,⟨2052,2251,104⟩,⟨2251,2493,105⟩,⟨2493,2793,106⟩,⟨2793,3175,107⟩,⟨3175,3678,108⟩,⟨3678,4371,109⟩,⟨4371,4950,110⟩,⟨4950,5500,109⟩,⟨5500,6187,108⟩,⟨6187,7071,107⟩,⟨7071,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4005745927728071) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2902273931834973) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5237002146700805) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3335681245597546) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4510944304008037) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3098604221809916) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3629390903422480) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4238059814286276) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2996087040871271) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3474146758052778) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4837394957277832) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3211224885474943) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 2816020661685622) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3805005606261809) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4099691385785671) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2947768521612944) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5395872661605925) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3398900449846463) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4630330784375465) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3151897048907913) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3705619218142900) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4343480540015981) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3045258187899624) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3543404794952567) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4974134472921469) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3269166133122654) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 2858218184015207) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3889361338246999) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4540473713259389) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3051001958294142) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 6811653578228174) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3596118829876369) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5365626062508517) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3292626477111156) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3992622939478043) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4905442997899306) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3165432567729590) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3780004679748919) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5970029733977735) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3435100395479963) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 2947359569460244) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 4242164074096830) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4662723705581654) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3103016315623211) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 7068335632183995) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3671726756694012) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5533520475485328) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3354758454414962) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 4087002692287544) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5047374733106969) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3222167615242517) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3864162030953393) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 6173789126032682) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3503456674933151) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 2995213085570170) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 4348975874085807) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 54 39) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 54 39 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 39 (0 : Fin 4)) (endpointMeanCornerA 54 39 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 39 (1 : Fin 4)) (endpointMeanCornerA 54 39 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 39 (2 : Fin 4)) (endpointMeanCornerA 54 39 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 39 (3 : Fin 4)) (endpointMeanCornerA 54 39 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 54 39 h) (endpointMeanCornerA 54 39 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 54 39) (prefactors h) runs ≤
      endpointMeanCorner 54 39 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 54 39 h ≤ endpointMeanCorner 54 39 h :=
  endpointMeanNumericCorner_le_of_runs 54 39 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox54_39

namespace SingularValueBounds.KL.Certificates
theorem endpointMeanEntropyRow54 (ai : Fin 42)
    (hactive : endpointMeanActive 54 ai) (h : Fin 4) :
    endpointMeanNumericCorner 54 ai h ≤ endpointMeanCorner 54 ai h := by
  fin_cases ai
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 0) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 1) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 2) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 3) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 4) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 5) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 6) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 7) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 8) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 9) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 10) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 11) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 12) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 13) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 14) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 15) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 16) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 17) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 18) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 19) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 20) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 21) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 22) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 23) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 24) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 25) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 26) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 27) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 28) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 29) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 30) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 31) hactive)
  · exact EndpointEntropyBox54_32.numerical h
  · exact EndpointEntropyBox54_33.numerical h
  · exact EndpointEntropyBox54_34.numerical h
  · exact EndpointEntropyBox54_35.numerical h
  · exact EndpointEntropyBox54_36.numerical h
  · exact EndpointEntropyBox54_37.numerical h
  · exact EndpointEntropyBox54_38.numerical h
  · exact EndpointEntropyBox54_39.numerical h
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 40) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 54 41) hactive)
end SingularValueBounds.KL.Certificates
