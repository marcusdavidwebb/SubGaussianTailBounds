import SingularValueBounds.KL.Certificates.EndpointMeanEntropyAssembly
import SingularValueBounds.KL.Certificates.EndpointPrefactorEvaluation

-- Elaborate the finite corner checks sequentially.
set_option Elab.async false

/-! Exact integer entropy certificates, independently checked by Lean's kernel.
Each corner is checked separately. Adjacent boxes reuse their shared vertices after
checking that the previous rate table contains the same prefactor values. -/
namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox53_31
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1228,1235,101⟩,⟨1235,1313,102⟩,⟨1313,1401,103⟩,⟨1401,1503,104⟩,⟨1503,1621,105⟩,⟨1621,1759,106⟩,⟨1759,1924,107⟩,⟨1924,2123,108⟩,⟨2123,2370,109⟩,⟨2370,2683,110⟩,⟨2683,3093,111⟩,⟨3093,3652,112⟩,⟨3652,3859,113⟩,⟨3859,4181,112⟩,⟨4181,4561,111⟩,⟨4561,5017,110⟩,⟨5017,5574,109⟩,⟨5574,6271,108⟩,⟨6271,7167,107⟩,⟨7167,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3189432252612540) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3781207824661343) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2805574988587769) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3448761650922540) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4229493326769028) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2979741595142172) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3311719298211866) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3986939464730854) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2888871300041793) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3603808234657645) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2728849485019857) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4521413270013756) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3079417777913031) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3229877106219621) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3840680991623671) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2835006533360692) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3497261739662039) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4304796561930037) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3014027503665694) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3355904592812664) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4053537775538627) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2920593713511032) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3657339575817531) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2756222545238354) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4607602060522490) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3116590007372966) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3436806913667137) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4298503718682695) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2946477842337045) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3795789585264416) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5078943961767955) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3163607661851036) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3602914425050716) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4639588649987049) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3049298665867869) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4023599086383035) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2853322371036881) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5675890329060605) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3291750608655970) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3485594059024088) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4377328207775045) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2980307899230292) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3856560507339545) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5188334336183077) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3203844906624871) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3657145949904697) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4731417885251032) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3086117884473735) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4092377618382118) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2884516967356204) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5810461469898264) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3335933233739988) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 53 31) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 53 31 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 31 (0 : Fin 4)) (endpointMeanCornerA 53 31 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 31 (1 : Fin 4)) (endpointMeanCornerA 53 31 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 31 (2 : Fin 4)) (endpointMeanCornerA 53 31 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 31 (3 : Fin 4)) (endpointMeanCornerA 53 31 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 31 h) (endpointMeanCornerA 53 31 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 53 31) (prefactors h) runs ≤
      endpointMeanCorner 53 31 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 53 31 h ≤ endpointMeanCorner 53 31 h :=
  endpointMeanNumericCorner_le_of_runs 53 31 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox53_31

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox53_32
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1236,1262,101⟩,⟨1262,1342,102⟩,⟨1342,1433,103⟩,⟨1433,1537,104⟩,⟨1537,1658,105⟩,⟨1658,1800,106⟩,⟨1800,1969,107⟩,⟨1969,2174,108⟩,⟨2174,2427,109⟩,⟨2427,2748,110⟩,⟨2748,3168,111⟩,⟨3168,3742,112⟩,⟨3742,3859,113⟩,⟨3859,4181,112⟩,⟨4181,4561,111⟩,⟨4561,5017,110⟩,⟨5017,5574,109⟩,⟨5574,6271,108⟩,⟨6271,7167,107⟩,⟨7167,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3229877106219621) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3840680991623671) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2835006533360692) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3497261739662039) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4304796561930037) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3014027503665694) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3355904592812664) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4053537775538627) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2920593713511032) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3657339575817531) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2756222545238354) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4607602060522490) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3116590007372966) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3297511495629809) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3940532283642763) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2884082886674430) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3578513206555006) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4431567793030056) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3071274493264563) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3429857868506071) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4165493950506139) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2973524027312743) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3747112484902228) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2801838961097804) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4752936530100898) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3178702163054365) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3485594059024088) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4377328207775045) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2980307899230292) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3856560507339545) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5188334336183077) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3203844906624871) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3657145949904697) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4731417885251032) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3086117884473735) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4092377618382118) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2884516967356204) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5810461469898264) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3335933233739988) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3567340564265769) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4510119519826731) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3036791921513530) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3958628091035085) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5373386160696838) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3271135453263791) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3748116581994119) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4886410495324181) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3147640462880806) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4208057594549151) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2936563310390473) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 6038752275611159) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3409889784374961) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 53 32) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 53 32 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 32 (0 : Fin 4)) (endpointMeanCornerA 53 32 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 53 32 (0 : Fin 4) = endpointMeanCornerK 53 31 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 53 32 (0 : Fin 4) = endpointMeanCornerA 53 31 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_31.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_31.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox53_31.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox53_31.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 32 (1 : Fin 4)) (endpointMeanCornerA 53 32 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 32 (2 : Fin 4)) (endpointMeanCornerA 53 32 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 53 32 (2 : Fin 4) = endpointMeanCornerK 53 31 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 53 32 (2 : Fin 4) = endpointMeanCornerA 53 31 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_31.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_31.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox53_31.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox53_31.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 32 (3 : Fin 4)) (endpointMeanCornerA 53 32 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 32 h) (endpointMeanCornerA 53 32 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 53 32) (prefactors h) runs ≤
      endpointMeanCorner 53 32 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 53 32 h ≤ endpointMeanCorner 53 32 h :=
  endpointMeanNumericCorner_le_of_runs 53 32 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox53_32

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox53_33
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1247,1296,101⟩,⟨1296,1378,102⟩,⟨1378,1472,103⟩,⟨1472,1579,104⟩,⟨1579,1704,105⟩,⟨1704,1851,106⟩,⟨1851,2025,107⟩,⟨2025,2236,108⟩,⟨2236,2498,109⟩,⟨2498,2829,110⟩,⟨2829,3263,111⟩,⟨3263,3855,112⟩,⟨3855,3859,113⟩,⟨3859,4181,112⟩,⟨4181,4561,111⟩,⟨4561,5017,110⟩,⟨5017,5574,109⟩,⟨5574,6271,108⟩,⟨6271,7167,107⟩,⟨7167,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3297511495629809) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3940532283642763) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2884082886674430) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3578513206555006) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4431567793030056) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3071274493264563) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3429857868506071) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4165493950506139) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2973524027312743) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3747112484902228) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2801838961097804) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4752936530100898) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3178702163054365) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3366562165127588) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4042979542507230) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2934008793040772) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3661652379134225) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4562072288827580) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3129608804665949) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3505440835042745) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4280542284917430) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3027413604330756) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3839088956176999) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2848210344076821) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4902855186371251) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3242052184439713) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3567340564265769) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4510119519826731) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3036791921513530) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3958628091035085) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5373386160696838) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3271135453263791) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3748116581994119) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4886410495324181) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3147640462880806) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4208057594549151) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2936563310390473) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 6038752275611159) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3409889784374961) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3651004243741189) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4646939209856816) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3094346452241250) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4063396991518382) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5565038210935655) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3339839307287718) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3841350086830793) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5046480380277694) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3210389510203052) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4327007517464472) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2989548743696661) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 6276012539643857) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3485485927591260) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 53 33) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 53 33 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 33 (0 : Fin 4)) (endpointMeanCornerA 53 33 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 53 33 (0 : Fin 4) = endpointMeanCornerK 53 32 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 53 33 (0 : Fin 4) = endpointMeanCornerA 53 32 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_32.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_32.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox53_32.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox53_32.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 33 (1 : Fin 4)) (endpointMeanCornerA 53 33 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 33 (2 : Fin 4)) (endpointMeanCornerA 53 33 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 53 33 (2 : Fin 4) = endpointMeanCornerK 53 32 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 53 33 (2 : Fin 4) = endpointMeanCornerA 53 32 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_32.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_32.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox53_32.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox53_32.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 33 (3 : Fin 4)) (endpointMeanCornerA 53 33 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 33 h) (endpointMeanCornerA 53 33 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 53 33) (prefactors h) runs ≤
      endpointMeanCorner 53 33 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 53 33 h ≤ endpointMeanCorner 53 33 h :=
  endpointMeanNumericCorner_le_of_runs 53 33 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox53_33

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox53_34
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1254,1318,101⟩,⟨1318,1402,102⟩,⟨1402,1498,103⟩,⟨1498,1608,104⟩,⟨1608,1735,105⟩,⟨1735,1884,106⟩,⟨1884,2063,107⟩,⟨2063,2278,108⟩,⟨2278,2545,109⟩,⟨2545,2883,110⟩,⟨2883,3325,111⟩,⟨3325,3753,112⟩,⟨3753,3860,112⟩,⟨3860,3967,112⟩,⟨3967,4181,112⟩,⟨4181,4561,111⟩,⟨4561,5017,110⟩,⟨5017,5574,109⟩,⟨5574,6271,108⟩,⟨6271,7167,107⟩,⟨7167,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3366562165127588) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4042979542507230) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2934008793040772) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3661652379134225) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4562072288827580) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3129608804665949) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3505440835042745) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4280542284917430) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3027413604330756) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3839088956176999) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2848210344076821) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3242052184439713) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3389898892045148) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4077717125281229) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2950842085965845) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3689792477881432) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4606422311467722) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3149298760464881) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3531003495314900) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4319593570033585) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3045592962042113) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3870246771124248) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2863837395905996) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3263448189395981) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3651004243741189) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4646939209856816) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3094346452241250) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4063396991518382) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5565038210935655) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3339839307287718) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3841350086830793) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5046480380277694) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3210389510203052) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4327007517464472) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2989548743696661) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3485485927591260) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3679325916836073) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4693461984517836) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3113772682267065) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4098932553740836) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5630429393553300) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3363059772965075) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3872940471246344) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5100993883697568) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3231582619932946) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4367400047968568) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3007422161421314) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3511055255443065) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 53 34) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 53 34 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 34 (0 : Fin 4)) (endpointMeanCornerA 53 34 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 53 34 (0 : Fin 4) = endpointMeanCornerK 53 33 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 53 34 (0 : Fin 4) = endpointMeanCornerA 53 33 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_33.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_33.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox53_33.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox53_33.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 34 (1 : Fin 4)) (endpointMeanCornerA 53 34 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 34 (2 : Fin 4)) (endpointMeanCornerA 53 34 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 53 34 (2 : Fin 4) = endpointMeanCornerK 53 33 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 53 34 (2 : Fin 4) = endpointMeanCornerA 53 33 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_33.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_33.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox53_33.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox53_33.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 34 (3 : Fin 4)) (endpointMeanCornerA 53 34 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 34 h) (endpointMeanCornerA 53 34 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 53 34) (prefactors h) runs ≤
      endpointMeanCorner 53 34 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 53 34 h ≤ endpointMeanCorner 53 34 h :=
  endpointMeanNumericCorner_le_of_runs 53 34 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox53_34

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox53_35
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1259,1260,100⟩,⟨1260,1335,101⟩,⟨1335,1420,102⟩,⟨1420,1517,103⟩,⟨1517,1629,104⟩,⟨1629,1758,105⟩,⟨1758,1910,106⟩,⟨1910,2091,107⟩,⟨2091,2310,108⟩,⟨2310,2580,109⟩,⟨2580,2923,110⟩,⟨2923,3373,111⟩,⟨3373,3777,112⟩,⟨3777,3979,112⟩,⟨3979,4181,112⟩,⟨4181,4561,111⟩,⟨4561,5017,110⟩,⟨5017,5574,109⟩,⟨5574,6271,108⟩,⟨6271,7167,107⟩,⟨7167,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3389898892045148) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4077717125281229) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2950842085965845) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3689792477881432) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2783586018944527) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4606422311467722) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3149298760464881) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3531003495314900) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4319593570033585) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3045592962042113) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3870246771124248) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2863837395905996) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3263448189395981) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3437058771952470) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4148090259019892) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2984798958939332) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3746723114241839) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2812896771664037) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4696419989607815) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3189051089937512) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3582689405534308) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4398768182279975) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3082279829421734) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3933323078190105) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2895349189136725) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3306664741603392) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3679325916836073) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4693461984517836) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3113772682267065) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4098932553740836) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2910791415129467) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5630429393553300) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3363059772965075) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3872940471246344) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5100993883697568) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3231582619932946) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4367400047968568) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3007422161421314) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3511055255443065) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3736630060314895) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4787909483368698) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3152991780130218) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4170938701736776) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2944071562051680) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5763525896519158) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3409986152476392) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3936902752833869) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5211793862365257) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3274389476423525) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4449319819302532) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3043490211607221) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3562758012621082) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 53 35) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 53 35 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 35 (0 : Fin 4)) (endpointMeanCornerA 53 35 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 35 (1 : Fin 4)) (endpointMeanCornerA 53 35 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 35 (2 : Fin 4)) (endpointMeanCornerA 53 35 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 35 (3 : Fin 4)) (endpointMeanCornerA 53 35 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 35 h) (endpointMeanCornerA 53 35 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 53 35) (prefactors h) runs ≤
      endpointMeanCorner 53 35 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 53 35 h ≤ endpointMeanCorner 53 35 h :=
  endpointMeanNumericCorner_le_of_runs 53 35 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox53_35

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox53_36
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1268,1286,100⟩,⟨1286,1363,101⟩,⟨1363,1451,102⟩,⟨1451,1550,103⟩,⟨1550,1664,104⟩,⟨1664,1797,105⟩,⟨1797,1952,106⟩,⟨1952,2137,107⟩,⟨2137,2362,108⟩,⟨2362,2639,109⟩,⟨2639,2991,110⟩,⟨2991,3451,111⟩,⟨3451,3816,112⟩,⟨3816,3998,112⟩,⟨3998,4181,112⟩,⟨4181,4561,111⟩,⟨4561,5017,110⟩,⟨5017,5574,109⟩,⟨5574,6271,108⟩,⟨6271,7167,107⟩,⟨7167,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3437058771952470) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4148090259019892) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2984798958939332) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3746723114241839) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2812896771664037) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4696419989607815) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3189051089937512) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3582689405534308) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4398768182279975) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3082279829421734) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3933323078190105) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2895349189136725) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3306664741603392) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3509031594373577) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4255933678631750) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3036468345431271) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3833770287640810) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2857442611125783) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4834724073268940) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3249622393402349) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3661640284501126) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4520259404892652) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3138140402510430) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4029870267145115) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2943268198034666) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3372564996282635) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3736630060314895) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4787909483368698) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3152991780130218) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4170938701736776) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2944071562051680) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5763525896519158) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3409986152476392) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3936902752833869) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5211793862365257) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3274389476423525) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4449319819302532) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3043490211607221) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3562758012621082) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3824264031350891) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4933156253111010) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3212748578417312) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4281326606767255) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2994706585271552) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5969093023399394) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3481606296059750) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4034832268583498) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5382522712253849) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3339665298942181) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4575089545034710) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3098404964187070) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3641743194547273) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 53 36) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 53 36 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 36 (0 : Fin 4)) (endpointMeanCornerA 53 36 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 53 36 (0 : Fin 4) = endpointMeanCornerK 53 35 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 53 36 (0 : Fin 4) = endpointMeanCornerA 53 35 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_35.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_35.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox53_35.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox53_35.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 36 (1 : Fin 4)) (endpointMeanCornerA 53 36 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 36 (2 : Fin 4)) (endpointMeanCornerA 53 36 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 53 36 (2 : Fin 4) = endpointMeanCornerK 53 35 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 53 36 (2 : Fin 4) = endpointMeanCornerA 53 35 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_35.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_35.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox53_35.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox53_35.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 36 (3 : Fin 4)) (endpointMeanCornerA 53 36 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 36 h) (endpointMeanCornerA 53 36 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 53 36) (prefactors h) runs ≤
      endpointMeanCorner 53 36 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 53 36 h ≤ endpointMeanCorner 53 36 h :=
  endpointMeanNumericCorner_le_of_runs 53 36 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox53_36

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox53_37
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1278,1317,100⟩,⟨1317,1397,101⟩,⟨1397,1487,102⟩,⟨1487,1589,103⟩,⟨1589,1707,104⟩,⟨1707,1843,105⟩,⟨1843,2003,106⟩,⟨2003,2194,107⟩,⟨2194,2424,108⟩,⟨2424,2710,109⟩,⟨2710,3072,110⟩,⟨3072,3545,111⟩,⟨3545,4181,112⟩,⟨4181,4561,111⟩,⟨4561,5017,110⟩,⟨5017,5574,109⟩,⟨5574,6271,108⟩,⟨6271,7167,107⟩,⟨7167,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3509031594373577) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4255933678631750) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3036468345431271) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3833770287640810) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2857442611125783) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4834724073268940) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3249622393402349) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3661640284501126) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4520259404892652) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3138140402510430) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4029870267145115) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2943268198034666) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3372564996282635) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3582511544694141) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4366580847059897) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3089032172566343) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3922839817687362) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2902693891268233) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4977101050666082) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3311344159089324) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3742330985312390) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4645106138994062) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3195013344299726) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4128787299489501) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2991980282746185) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3439778611676123) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3824264031350891) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4933156253111010) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3212748578417312) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4281326606767255) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2994706585271552) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5969093023399394) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3481606296059750) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4034832268583498) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5382522712253849) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3339665298942181) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4575089545034710) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3098404964187070) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3641743194547273) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3913953253443476) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5082809251541208) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3273637912147100) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4394636033893459) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3046212479162345) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 6181992093331928) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3554730681812296) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4135197757649478) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5558844327503858) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3406242412292664) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4704414426285747) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3154310562750062) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3722479452168696) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 53 37) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 53 37 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 37 (0 : Fin 4)) (endpointMeanCornerA 53 37 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 53 37 (0 : Fin 4) = endpointMeanCornerK 53 36 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 53 37 (0 : Fin 4) = endpointMeanCornerA 53 36 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_36.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_36.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox53_36.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox53_36.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 37 (1 : Fin 4)) (endpointMeanCornerA 53 37 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 37 (2 : Fin 4)) (endpointMeanCornerA 53 37 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 53 37 (2 : Fin 4) = endpointMeanCornerK 53 36 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 53 37 (2 : Fin 4) = endpointMeanCornerA 53 36 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_36.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_36.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox53_36.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox53_36.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 37 (3 : Fin 4)) (endpointMeanCornerA 53 37 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 37 h) (endpointMeanCornerA 53 37 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 53 37) (prefactors h) runs ≤
      endpointMeanCorner 53 37 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 53 37 h ≤ endpointMeanCorner 53 37 h :=
  endpointMeanNumericCorner_le_of_runs 53 37 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox53_37

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox53_38
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1288,1349,100⟩,⟨1349,1431,101⟩,⟨1431,1523,102⟩,⟨1523,1628,103⟩,⟨1628,1749,104⟩,⟨1749,1889,105⟩,⟨1889,2054,106⟩,⟨2054,2250,107⟩,⟨2250,2487,108⟩,⟨2487,2780,109⟩,⟨2780,3153,110⟩,⟨3153,3640,111⟩,⟨3640,4181,112⟩,⟨4181,4561,111⟩,⟨4561,5017,110⟩,⟨5017,5574,109⟩,⟨5574,6271,108⟩,⟨6271,7167,107⟩,⟨7167,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3582511544694141) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4366580847059897) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3089032172566343) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3922839817687362) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2902693891268233) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4977101050666082) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3311344159089324) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3742330985312390) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4645106138994062) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3195013344299726) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4128787299489501) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2991980282746185) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3439778611676123) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3657530182528301) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4480104657091420) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3142505923866188) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4013978689553455) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2948661783652181) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5123670863762948) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3374238238324859) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3824799848010547) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4773401061710253) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3252917002084136) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4230132345303107) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3041498568944380) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3508331762437865) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3913953253443476) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5082809251541208) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3273637912147100) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4394636033893459) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3046212479162345) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 6181992093331928) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3554730681812296) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4135197757649478) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5558844327503858) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3406242412292664) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4704414426285747) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3154310562750062) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3722479452168696) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4005745927728071) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5237002146700805) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3335681245597546) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4510944304008037) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3098604221809916) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 6402484614028335) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3629390903422480) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4238059814286276) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5740941916895804) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3474146758052778) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4837394957277832) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3211224885474943) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3805005606261809) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 53 38) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 53 38 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 38 (0 : Fin 4)) (endpointMeanCornerA 53 38 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 53 38 (0 : Fin 4) = endpointMeanCornerK 53 37 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 53 38 (0 : Fin 4) = endpointMeanCornerA 53 37 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_37.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_37.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox53_37.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox53_37.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 38 (1 : Fin 4)) (endpointMeanCornerA 53 38 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 38 (2 : Fin 4)) (endpointMeanCornerA 53 38 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 53 38 (2 : Fin 4) = endpointMeanCornerK 53 37 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 53 38 (2 : Fin 4) = endpointMeanCornerA 53 37 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_37.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox53_37.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox53_37.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox53_37.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 38 (3 : Fin 4)) (endpointMeanCornerA 53 38 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 38 h) (endpointMeanCornerA 53 38 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 53 38) (prefactors h) runs ≤
      endpointMeanCorner 53 38 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 53 38 h ≤ endpointMeanCorner 53 38 h :=
  endpointMeanNumericCorner_le_of_runs 53 38 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox53_38

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox53_39
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1299,1305,99⟩,⟨1305,1380,100⟩,⟨1380,1464,101⟩,⟨1464,1559,102⟩,⟨1559,1667,103⟩,⟨1667,1791,104⟩,⟨1791,1935,105⟩,⟨1935,2104,106⟩,⟨2104,2306,107⟩,⟨2306,2550,108⟩,⟨2550,2851,109⟩,⟨2851,3233,110⟩,⟨3233,3734,111⟩,⟨3734,4181,112⟩,⟨4181,4561,111⟩,⟨4561,5017,110⟩,⟨5017,5574,109⟩,⟨5574,6271,108⟩,⟨6271,7167,107⟩,⟨7167,8000,106⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3657530182528301) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4480104657091420) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3142505923866188) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4013978689553455) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2948661783652181) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5123670863762948) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3374238238324859) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3824799848010547) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2862975408933493) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4773401061710253) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3252917002084136) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4230132345303107) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3041498568944380) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3508331762437865) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3734119728356004) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4596579896604150) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3196905350885272) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4107234980011955) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2995357636754477) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5274556986674021) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3438326897468997) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3909086057528492) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2906389955475784) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4905239409851443) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3311870055668652) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4333965002506191) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3091836399536684) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3578251144870277) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4005745927728071) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5237002146700805) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3335681245597546) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4510944304008037) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3098604221809916) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 6402484614028335) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3629390903422480) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4238059814286276) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 2996087040871271) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5740941916895804) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3474146758052778) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4837394957277832) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3211224885474943) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3805005606261809) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4099691385785671) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5395872661605925) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3398900449846463) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4630330784375465) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3151897048907913) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 6630841420370707) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3705619218142900) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4343480540015981) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3045258187899624) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 5929004690795317) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3543404794952567) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 4974134472921469) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3269166133122654) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 3889361338246999) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 53 39) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 53 39 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 39 (0 : Fin 4)) (endpointMeanCornerA 53 39 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 39 (1 : Fin 4)) (endpointMeanCornerA 53 39 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 39 (2 : Fin 4)) (endpointMeanCornerA 53 39 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 39 (3 : Fin 4)) (endpointMeanCornerA 53 39 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 53 39 h) (endpointMeanCornerA 53 39 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 53 39) (prefactors h) runs ≤
      endpointMeanCorner 53 39 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 53 39 h ≤ endpointMeanCorner 53 39 h :=
  endpointMeanNumericCorner_le_of_runs 53 39 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox53_39

namespace SingularValueBounds.KL.Certificates
theorem endpointMeanEntropyRow53 (ai : Fin 42)
    (hactive : endpointMeanActive 53 ai) (h : Fin 4) :
    endpointMeanNumericCorner 53 ai h ≤ endpointMeanCorner 53 ai h := by
  fin_cases ai
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 0) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 1) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 2) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 3) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 4) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 5) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 6) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 7) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 8) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 9) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 10) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 11) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 12) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 13) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 14) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 15) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 16) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 17) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 18) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 19) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 20) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 21) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 22) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 23) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 24) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 25) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 26) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 27) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 28) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 29) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 30) hactive)
  · exact EndpointEntropyBox53_31.numerical h
  · exact EndpointEntropyBox53_32.numerical h
  · exact EndpointEntropyBox53_33.numerical h
  · exact EndpointEntropyBox53_34.numerical h
  · exact EndpointEntropyBox53_35.numerical h
  · exact EndpointEntropyBox53_36.numerical h
  · exact EndpointEntropyBox53_37.numerical h
  · exact EndpointEntropyBox53_38.numerical h
  · exact EndpointEntropyBox53_39.numerical h
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 40) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 53 41) hactive)
end SingularValueBounds.KL.Certificates
