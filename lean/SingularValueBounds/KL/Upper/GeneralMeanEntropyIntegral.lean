import SingularValueBounds.KL.Upper.GeneralMeanError
import SingularValueBounds.KL.Upper.EntropyQuadrature

open MeasureTheory Set Filter
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1600000

theorem generalMean_integral_translate (f : ℝ → ℝ) (c : ℝ) :
    (∫ u in Ioi 0,f (c+u))=∫u in Ioi c,f u := by
  rw [← integral_indicator measurableSet_Ioi,← integral_indicator measurableSet_Ioi]
  have h := integral_add_left_eq_self (μ := volume) ((Ioi c).indicator f) c
  convert h using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    by_cases hu : 0<u
    · simp [Set.indicator_of_mem,hu,show c<c+u by linarith]
    · simp [Set.indicator_of_not_mem,hu,show ¬c<c+u by linarith]

theorem generalMean_resolvent_cutoff {β v : ℝ} (hβ : 0<β) (hv : 0<v) :
    (∫u in Ioi v,Real.exp (-(β*u))/u)=
      Real.exp (-(β*v))*exponentialResolvent (β*v) := by
  rw [← exponentialResolvent_scaled hβ hv,← integral_const_mul,
    ← generalMean_integral_translate _ v]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [show -(β*(v+u))=-(β*v)+-(β*u) by ring,Real.exp_add]
  ring

theorem generalMean_entropy_exponential_integral {a v β : ℝ}
    (ha : 0<a) (hav : a≤v) (hβ : 0<β) :
    (∫u in Ioi v,entropyKernel a u*Real.exp (-(β*u)))=
      Real.exp (-(β*v))/β*(1+Real.log (v/a)+exponentialResolvent (β*v)) := by
  have hv : 0<v := ha.trans_le hav
  let F : ℝ → ℝ := fun u => entropyKernel a u*Real.exp (-(β*u))
  let g : ℝ → ℝ := fun u => Real.exp (-(β*u))/u-β*F u
  have hFint : IntegrableOn F (Ioi v) := by
    have hi := entropy_tail_integrable (r := β) (T := fun u => Real.exp (-(β*u)))
      ha (by norm_num : (0:ℝ)≤1) hβ
      (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg))
      (fun u => Real.exp_nonneg _) (fun u hu => by simp)
    exact hi.mono_set (Ioi_subset_Ioi hav)
  have hRint : IntegrableOn (fun u => Real.exp (-(β*u))/u) (Ioi v) := by
    have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (0:ℝ)) (p := (1:ℝ)) (b := β) (by norm_num) (by norm_num) hβ
    have he : IntegrableOn (fun u : ℝ => Real.exp (-(β*u))) (Ioi v) := by
      have hh : IntegrableOn (fun u : ℝ => Real.exp (-(β*u))) (Ioi 0) := by
        simpa only [Real.rpow_zero,Real.rpow_one,one_mul,neg_mul] using hi
      exact hh.mono_set (Ioi_subset_Ioi hv.le)
    apply (he.const_mul (1/v)).mono'
    · exact ((Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)).div
        measurable_id).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0<u := hv.trans hu
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤Real.exp (-(β*u))/u)]
      simpa [div_eq_mul_inv,mul_comm] using
        div_le_div_of_nonneg_left (Real.exp_nonneg (-(β*u))) hv (le_of_lt hu)
  have hd : ∀u∈Ici v,HasDerivAt F (g u) u := by
    intro u hu
    have hu0 : 0<u := hv.trans_le hu
    have hlog := ((hasDerivAt_id u).div_const a).log (ne_of_gt (div_pos hu0 ha))
    have he := ((hasDerivAt_id u).const_mul (-β)).exp
    convert ((hasDerivAt_const u 1).add hlog).mul he using 1 <;>
      dsimp [F,g,entropyKernel] <;> (try simp only [id_eq,zero_add]) <;> field_simp <;> ring
  have hlim : Tendsto F atTop (nhds 0) := by
    have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) β hβ
    have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) β hβ
    have hu : Tendsto (fun u : ℝ => (1+u/a)*Real.exp (-(β*u))) atTop (nhds 0) := by
      have hh := h0.add (h1.div_const a)
      convert hh using 1 <;> simp only [Real.rpow_zero,Real.rpow_one,one_mul,zero_div,add_zero]
      ext u
      ring
    apply squeeze_zero' _ _ hu
    · filter_upwards [eventually_ge_atTop v] with u hu
      exact mul_nonneg (entropyKernel_nonneg ha (hav.trans hu)) (Real.exp_nonneg _)
    · filter_upwards [eventually_ge_atTop v] with u hu
      have hl := Real.log_le_sub_one_of_pos (div_pos (hv.trans_le hu) ha)
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      dsimp [F,entropyKernel]
      linarith
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    (hRint.sub (hFint.const_mul β)) hlim
  change (∫u in Ioi v,Real.exp (-(β*u))/u-β*F u)=0-F v at hi
  rw [integral_sub hRint (hFint.const_mul β),integral_const_mul,
    generalMean_resolvent_cutoff hβ hv] at hi
  dsimp [F,entropyKernel] at hi ⊢
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hβ.ne').mpr
  nlinarith

end
end SingularValueBounds.KL
