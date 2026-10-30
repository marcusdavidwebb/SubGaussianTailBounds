import SingularValueBounds.KL.Upper.GeneralMeanJointTail
import SingularValueBounds.KL.Upper.GeneralMeanTailEntropy
import SingularValueBounds.KL.Upper.GeneralMeanCells

open MeasureTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
open Certificates
noncomputable section
set_option maxHeartbeats 1800000

theorem upperJointCost_mono_third {v k a a' : ℝ} (hk : 0<k)
    (hvk : v*k^2<1) (ha : a≤a') : upperJointCost v k a≤upperJointCost v k a' := by
  have hl := Real.log_le_sub_one_of_pos (show 0<1-v*k^2 by linarith)
  have hr : 0≤-Real.log (1-v*k^2)-v*k^2 := by linarith
  unfold upperJointCost
  exact add_le_add_right (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right ha (by positivity : 0≤k^3)) hr) _

theorem upperRateF_nonpos_of_le_two {v theta : ℝ} (hv : 1<v) (hv2 : v≤2)
    (ht : 1≤theta) : upperRateF v theta≤0 := by
  let x := (theta-1)/(v-1)
  have hx : 0≤x := div_nonneg (by linarith) (by linarith)
  have hm : x*(v-1)≤theta-1 := by dsimp [x];rw [div_mul_cancel₀ _ (by linarith : v-1≠0)]
  have hp := upper_margin_rescaling (by linarith : 0<v) hv2 ht hx hm
  have hl := Real.log_le_log (Real.exp_pos _) hp.2.2
  have hd : 0<1+x := by positivity
  rw [Real.log_exp,Real.log_div hp.1.ne' hd.ne'] at hl
  rw [← upperFactorF_rate_identity hv ht]
  dsimp [upperFactorF]
  change _≤0
  dsimp [x] at hl
  linarith

theorem generalMeanRow_rate_bound {r : GeneralMeanRow} (hr : r.rateCompatible)
    (hcert : RateCertificateConditions) (hq : (1:ℝ)<r.q) :
    ∀theta∈Icc (1:ℝ) r.q,upperRateF r.q theta≤(r.C:ℝ) := by
  intro theta ht
  rcases hr with ⟨h2,h0⟩|⟨j,hqj,hCj⟩
  · have hh := upperRateF_nonpos_of_le_two hq (by exact_mod_cast h2) ht.1
    simpa [h0] using hh
  · rw [hqj] at ht ⊢
    rw [hCj]
    exact upper_rate_of_certificates hcert j ht

theorem upperShift_tail_general_mean_row
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω→ι→ℝ} {r : GeneralMeanRow} (hnum : GeneralMeanNumericalConditions r)
    {K L b eta : ℝ} (hsg : SubGaussianMGF μ X K) (hm : Measurable X) (hK : 0<K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hL : 1≤L)
    (hcap : K^2*Matrix.trace R+(47/20)*K^2*L*eta≤b) (hb : b<1)
    (heta : 0<eta) (hnorm : eta^2=∑i,hR.isHermitian.eigenvalues i^2)
    (hmax : ∀i,hR.isHermitian.eigenvalues i≤(r.khi:ℝ)*eta)
    (ha : (∑i,(hR.isHermitian.eigenvalues i/eta)^3)≤(r.ahi:ℝ))
    (hcompatible : r.rateCompatible) (hrate : RateCertificateConditions) :
    GeneralMeanTailProfile
      (fun u=>μ.real {ω|u<(1-b)*upperShift R hR (X ω)})
      r.prefactor r.q r.c r.cutoff K L := by
  have hk : (0:ℝ)<r.khi := by exact_mod_cast hnum.shape
  have hq : (0:ℝ)<r.q := by exact_mod_cast hnum.rate
  have hvk : (r.q:ℝ)*(r.khi:ℝ)^2<1 := by exact_mod_cast hnum.gap
  have hC : (0:ℝ)≤r.C := by exact_mod_cast hnum.correction
  have hpref : extendedJointPrefactor r.q r.khi r.C
      (∑i,(hR.isHermitian.eigenvalues i/eta)^3)≤(r.prefactor:ℝ) := by
    apply le_trans _ hnum.prefactor_sound
    unfold extendedJointPrefactor
    apply Real.exp_le_exp.mpr
    linarith [upperJointCost_mono_third hk hvk ha]
  have hcut : (r.cutoff:ℝ)=extendedTailCutoff (47/20) r.khi r.q := by
    simp [GeneralMeanRow.cutoff,extendedTailCutoff]
  unfold GeneralMeanTailProfile
  split_ifs with hq1
  · have hh := upperShift_tail_extended_joint_two_pieces hsg hm hK hR
      (by norm_num : (0:ℝ)<47/20) (by linarith : 0<L) hcap hb hq1 hk hvk hC
      (generalMeanRow_rate_bound hcompatible hrate hq1) heta hnorm hmax
    constructor
    · intro u hu hc
      rw [hcut] at hc
      exact (hh.1 u hu hc).trans (mul_le_mul_of_nonneg_right hpref (Real.exp_nonneg _))
    · intro u hc
      rw [hcut] at hc ⊢
      exact (hh.2 u hc).trans (mul_le_mul_of_nonneg_right hpref (Real.exp_nonneg _))
  · intro u hu
    have hcost : 0≤(47/20:ℝ)*K^2*L*eta := by positivity
    have hcap0 : K^2*Matrix.trace R≤b := by linarith
    have ht := upperShift_tail_joint_of_spectrum hsg hm hK hR hcap0 hb hq
      (by linarith : (r.q:ℝ)≤2) hk hvk heta hnorm hmax hu
      (fun i=>by
        have hn := mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg hu (hR.eigenvalues_pos i).le) (by linarith : (r.q:ℝ)-1≤0)
        linarith)
    apply ht.trans
    have hc : upperJointCost r.q r.khi (∑i,(hR.isHermitian.eigenvalues i/eta)^3)/2≤
        ((r.C:ℝ)/(r.khi:ℝ)^2+upperJointCost r.q r.khi r.ahi)/2 := by
      have hdiv : 0≤(r.C:ℝ)/(r.khi:ℝ)^2 := div_nonneg hC (sq_nonneg _)
      linarith [upperJointCost_mono_third hk hvk ha]
    have he := Real.exp_le_exp.mpr (sub_le_sub_right hc ((r.q:ℝ)*u/(2*K^2)))
    have hexp : Real.exp (((r.C:ℝ)/(r.khi:ℝ)^2+upperJointCost r.q r.khi r.ahi)/2-
        (r.q:ℝ)*u/(2*K^2))=
        Real.exp (((r.C:ℝ)/(r.khi:ℝ)^2+upperJointCost r.q r.khi r.ahi)/2)*
          Real.exp (-(r.q:ℝ)*u/(2*K^2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp] at he
    exact he.trans (mul_le_mul_of_nonneg_right hnum.prefactor_sound (Real.exp_nonneg _))

end
end SingularValueBounds.KL
