import SingularValueBounds.KL.Upper.EndpointMeanEnvelope

open MeasureTheory Set
open scoped BigOperators
namespace SingularValueBounds.KL
open Certificates
noncomputable section
set_option maxHeartbeats 1800000

theorem endpointAnalyticTailQ_sound {j0 : ℕ} (hj0 : 0<j0) :
    (31623/10000:ℝ)*entropyExpPrimitive ((j0:ℝ)/200) (9/10) (endpointRunPoint j0 8000)≤
      (endpointAnalyticTailQ j0:ℝ) := by
  have hp := primitiveUpperQ_sound (show (0:ℚ)<(j0:ℚ)/200 by positivity)
    (endpointRunPointQ_above j0 8000) (by norm_num : (0:ℚ)<9/10)
  norm_num only [Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat,endpointRunPointQ_cast] at hp
  have hh := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤31623/10000)
  have hr : (((31623/10000)*primitiveUpperQ ((j0:ℚ)/200) (9/10)
      (endpointRunPointQ j0 8000):ℚ):ℝ)≤(endpointAnalyticTailQ j0:ℝ) := by
    exact_mod_cast le_roundUpQ ((31623/10000)*primitiveUpperQ ((j0:ℚ)/200) (9/10)
      (endpointRunPointQ j0 8000))
  push_cast at hr
  exact hh.trans hr

/-- Replace the exact, nonnegative interval weights by rational ceilings. -/
theorem endpoint_entropy_runs_bound {j0 : ℕ} {rs : List EndpointRateRun}
    {T : ℝ → ℝ} {A : EndpointRateRun → ℝ}
    (hj0 : 0<j0) (hcover : EndpointRunsCover j0 8000 rs)
    (hT : Antitone T) (hT0 : ∀u,0≤T u)
    (hTail : ∀u,0≤u → T u≤(31623/10000:ℝ)*Real.exp (-((9/20:ℝ)*u)))
    (hr : ∀r∈rs,r.start≤r.stop ∧ 0<r.rate)
    (hA : ∀r∈rs,0≤A r)
    (hBound : ∀r∈rs,∀u∈Ioc (endpointRunPoint j0 r.start) (endpointRunPoint j0 r.stop),
      T u≤A r*Real.exp (-((r.rate:ℝ)/100)*u/2)) :
    Real.log ((j0:ℝ)/200)+
      (∫u in Ioi ((j0:ℝ)/200),entropyKernel ((j0:ℝ)/200) u*T u)≤
      ((logRoundedQ ((j0:ℚ)/200)).2:ℝ)+(endpointAnalyticTailQ j0:ℝ)+
        (rs.map (fun r => (endpointRunWeightQ j0 r:ℝ)*A r)).sum := by
  have hmain := entropy_analytic_runs_bound hj0 hcover hT hT0 hTail
    (q := fun r => (r.rate:ℝ)/100) (A := A)
    (fun r hmem => by have := (hr r hmem).2; positivity) hBound
  have hs := weighted_list_le rs (fun r hmem => by
    have hw := entropyExpWeightUpperQ_sound (show (0:ℚ)<(j0:ℚ)/200 by positivity)
      (endpointRunPointQ_above j0 r.start)
      (endpointRunPointQ_mono j0 (hr r hmem).1)
      (show (0:ℚ)<(r.rate:ℚ)/100 by have := (hr r hmem).2; positivity)
    norm_num only [Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat,endpointRunPointQ_cast] at hw
    have hh := mul_le_mul_of_nonneg_right hw (hA r hmem)
    change A r*(entropyExpPrimitive ((j0:ℝ)/200) ((r.rate:ℝ)/100) (endpointRunPoint j0 r.start)-
      entropyExpPrimitive ((j0:ℝ)/200) ((r.rate:ℝ)/100) (endpointRunPoint j0 r.stop))≤
        (endpointRunWeightQ j0 r:ℝ)*A r
    convert! hh using 1 <;> ring)
  have hl := (roundedLogConditions (show (0:ℚ)<(j0:ℚ)/200 by positivity)).sound.2
  norm_num only [Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat] at hl
  have ht := endpointAnalyticTailQ_sound hj0
  linarith

private theorem endpoint_run_margin {j0 : ℕ} {r : EndpointRateRun} {k : ℚ} {u : ℝ}
    (hk : 0≤(k:ℝ)) (hu : 0≤u) (hup : u≤endpointRunPoint j0 r.stop)
    (hcap : endpointRunPointQ j0 r.stop*k*((r.rate:ℚ)/100-1)≤58/25) :
    u*(k:ℝ)*((r.rate:ℝ)/100-1)≤58/25 := by
  have hcapR : endpointRunPoint j0 r.stop*(k:ℝ)*((r.rate:ℝ)/100-1)≤58/25 := by
    have hh : ((endpointRunPointQ j0 r.stop*k*((r.rate:ℚ)/100-1):ℚ):ℝ)≤((58/25:ℚ):ℝ) := by
      exact_mod_cast hcap
    push_cast at hh
    rw [endpointRunPointQ_cast] at hh
    exact hh
  by_cases hq : 1≤(r.rate:ℝ)/100
  · exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hup hk) (sub_nonneg.mpr hq)).trans hcapR
  · have hh : u*(k:ℝ)*((r.rate:ℝ)/100-1)≤0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hu hk) (by linarith)
    linarith

theorem endpoint_mean_joint_survival (h : EndpointMeanCertificateConditions)
    (ki : Fin 60) (ai : Fin 42) (hact : endpointMeanActive ki ai) {a k : ℝ}
    (hbox : (endpointMeanBox ki ai).contains a k) {T : ℝ → ℝ}
    (hT : Antitone T) (hT0 : ∀u,0≤T u)
    (hTail : ∀u,0≤u → T u≤(31623/10000:ℝ)*Real.exp (-((9/20:ℝ)*u)))
    (hJoint : ∀u q:ℝ,0≤u → 0<q → q≤2 → q*k^2<1 → u*k*(q-1)≤58/25 →
      T u≤upperJointPrefactor q a k*Real.exp (-q*u/2)) :
    Real.log ((endpointMeanCutoff ki ai:ℝ)/200)+
      (∫u in Ioi ((endpointMeanCutoff ki ai:ℝ)/200),
        entropyKernel ((endpointMeanCutoff ki ai:ℝ)/200) u*T u)≤
      realEval₂ (endpointMeanBilinearQ ki ai) a k := by
  have hc := (h.jointCutoff ki ai hact).1
  have hn := h.jointNumerical ki ai hact
  have hb := h.jointBoxes ki ai hact
  have hk : 0<k := (by exact_mod_cast hb.2.1 : (0:ℝ)<(endpointMeanBox ki ai).bottom).trans_le hbox.2.1
  have hktop : (0:ℝ)≤(endpointMeanBox ki ai).top := hk.le.trans hbox.2.2
  have hm := endpoint_entropy_runs_bound hc hn.1 hT hT0 hTail
    (A := fun r => upperJointPrefactor ((r.rate:ℝ)/100) a k)
    (fun r hr => by
      obtain ⟨_,hs,_,hl,_,_,_⟩ := hn.2.1 r hr
      exact ⟨hs.le,by omega⟩)
    (fun r hr => Real.exp_nonneg _)
    (by
      intro r hr u hu
      obtain ⟨_,_,_,hlo,hhi,hgap,hcap⟩ := hn.2.1 r hr
      have hqp : 0<(r.rate:ℝ)/100 := by
        have hrp : 0<r.rate := by omega
        positivity
      have hq2 : (r.rate:ℝ)/100≤2 := by
        have hh : (r.rate:ℝ)≤200 := by exact_mod_cast hhi
        linarith
      have hcg : ((r.rate:ℝ)/100)*((endpointMeanBox ki ai).top:ℝ)^2<1 := by
        have hh : ((((r.rate:ℚ)/100)*(endpointMeanBox ki ai).top^2:ℚ):ℝ)<(1:ℝ) := by
          exact_mod_cast hgap
        push_cast at hh
        exact hh
      have hkg : ((r.rate:ℝ)/100)*k^2<1 :=
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk.le hbox.2.2 2) hqp.le).trans_lt hcg
      have hup : (endpointMeanCutoff ki ai:ℝ)/200≤endpointRunPoint (endpointMeanCutoff ki ai) r.start := by
        have hh : (((endpointMeanCutoff ki ai:ℚ)/200):ℝ)≤
            (endpointRunPointQ (endpointMeanCutoff ki ai) r.start:ℝ) := by
          exact_mod_cast endpointRunPointQ_above (endpointMeanCutoff ki ai) r.start
        norm_num only [Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat,endpointRunPointQ_cast] at hh
        exact hh
      have hu0 : 0≤u := (by positivity : (0:ℝ)≤(endpointMeanCutoff ki ai:ℝ)/200).trans (hup.trans hu.1.le)
      have hmt := endpoint_run_margin hktop hu0 hu.2 hcap
      have hmargin : u*k*((r.rate:ℝ)/100-1)≤58/25 := by
        by_cases hq1 : 1≤(r.rate:ℝ)/100
        · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbox.2.2 hu0)
            (sub_nonneg.mpr hq1)).trans hmt
        · have hh : u*k*((r.rate:ℝ)/100-1)≤0 :=
            mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hu0 hk.le) (by linarith)
          linarith
      exact hJoint u _ hu0 hqp hq2 hkg hmargin)
  change _≤endpointMeanEnvelope ki ai a k at hm
  exact hm.trans (endpointMeanEnvelope_bilinear h ki ai hact hbox)

theorem endpoint_mean_small_survival (h : EndpointMeanCertificateConditions)
    (i : Fin 50) {T : ℝ → ℝ} (hT : Antitone T) (hT0 : ∀u,0≤T u)
    (hTail : ∀u,0≤u → T u≤(31623/10000:ℝ)*Real.exp (-((9/20:ℝ)*u)))
    (hMargin : ∀u q:ℝ,0≤u → 0<q → q≤2 → q*(endpointSmallK i:ℝ)^2<1 →
      u*(endpointSmallK i:ℝ)*(q-1)≤58/25 →
      T u≤Real.exp (-Real.log (1-q*(endpointSmallK i:ℝ)^2)/(2*(endpointSmallK i:ℝ)^2)-q*u/2)) :
    Real.log ((endpointSmallCutoff i:ℝ)/200)+
      (∫u in Ioi ((endpointSmallCutoff i:ℝ)/200),
        entropyKernel ((endpointSmallCutoff i:ℝ)/200) u*T u)≤(endpointSmallTarget i:ℝ) := by
  have hc := (h.smallCutoff i).1
  have hn := h.smallNumerical i
  have hk : (0:ℚ)<endpointSmallK i := by unfold endpointSmallK; positivity
  have hkr : (0:ℝ)<endpointSmallK i := by exact_mod_cast hk
  let A : EndpointRateRun → ℝ := fun r =>
    Real.exp (-Real.log (1-((r.rate:ℝ)/100)*(endpointSmallK i:ℝ)^2)/(2*(endpointSmallK i:ℝ)^2))
  have hm := endpoint_entropy_runs_bound hc hn.1 hT hT0 hTail (A := A)
    (fun r hr => by
      obtain ⟨_,hs,_,hl,_,_,_⟩ := hn.2.1 r hr
      exact ⟨hs.le,by omega⟩)
    (fun r hr => Real.exp_nonneg _)
    (by
      intro r hr u hu
      obtain ⟨_,_,_,hlo,hhi,hgap,hcap⟩ := hn.2.1 r hr
      have hqp : 0<(r.rate:ℝ)/100 := by
        have hrp : 0<r.rate := by omega
        positivity
      have hq2 : (r.rate:ℝ)/100≤2 := by
        have hh : (r.rate:ℝ)≤200 := by exact_mod_cast hhi
        linarith
      have hkg : ((r.rate:ℝ)/100)*(endpointSmallK i:ℝ)^2<1 := by
        have hh : ((((r.rate:ℚ)/100)*(endpointSmallK i)^2:ℚ):ℝ)<(1:ℝ) := by
          exact_mod_cast hgap
        push_cast at hh
        exact hh
      have hup : (endpointSmallCutoff i:ℝ)/200≤endpointRunPoint (endpointSmallCutoff i) r.start := by
        have hh : (((endpointSmallCutoff i:ℚ)/200):ℝ)≤
            (endpointRunPointQ (endpointSmallCutoff i) r.start:ℝ) := by
          exact_mod_cast endpointRunPointQ_above (endpointSmallCutoff i) r.start
        norm_num only [Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat,endpointRunPointQ_cast] at hh
        exact hh
      have hu0 : 0≤u := (by positivity : (0:ℝ)≤(endpointSmallCutoff i:ℝ)/200).trans (hup.trans hu.1.le)
      have hmargin := endpoint_run_margin hkr.le hu0 hu.2 hcap
      have hh := hMargin u _ hu0 hqp hq2 hkg hmargin
      dsimp only [A]
      convert! hh using 1
      rw [←Real.exp_add]
      congr 1
      ring)
  have hs : ((logRoundedQ ((endpointSmallCutoff i:ℚ)/200)).2:ℝ)+
      (endpointAnalyticTailQ (endpointSmallCutoff i):ℝ)+
      ((endpointSmallRuns i).map (fun r => (endpointRunWeightQ (endpointSmallCutoff i) r:ℝ)*A r)).sum≤
        (endpointSmallNumeric i:ℝ) := by
    unfold endpointSmallNumeric
    push_cast
    apply add_le_add le_rfl
    simp only [List.map_map,Function.comp_def,Rat.cast_mul]
    apply weighted_list_le
    intro r hr
    obtain ⟨_,hstep,_,hlo,_,hgap,_⟩ := hn.2.1 r hr
    have hw : (0:ℝ)≤endpointRunWeightQ (endpointSmallCutoff i) r := by
      exact_mod_cast endpointRunWeightQ_nonneg hc hstep.le (by omega)
    have hp := endpointSmall24_sound hk hgap (hn.2.2.1 r hr)
    norm_num only [Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat] at hp
    exact mul_le_mul_of_nonneg_left hp hw
  exact (hm.trans hs).trans (by exact_mod_cast hn.2.2.2)

end
end SingularValueBounds.KL
