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
  convert! h using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    by_cases hu : 0<u
    · simp [Set.indicator_of_mem,hu,show c<c+u by linarith]
    · simp [Set.indicator_of_notMem,hu,show ¬c<c+u by linarith]

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
    have hi := entropy_tail_integrable (C := 1) (r := β) (T := fun u => Real.exp (-(β*u)))
      ha hβ
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
    convert! ((hasDerivAt_const u 1).add hlog).mul he using 1 <;>
      (try funext z) <;> dsimp [F,g,entropyKernel] <;>
      (try simp only [zero_add]) <;> field_simp <;> ring
  have hlim : Tendsto F atTop (nhds 0) := by
    have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) β hβ
    have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) β hβ
    have hu : Tendsto (fun u : ℝ => (1+u/a)*Real.exp (-(β*u))) atTop (nhds 0) := by
      have hh := h0.add (h1.div_const a)
      convert! hh using 1 <;> simp only [Real.rpow_zero,Real.rpow_one,one_mul,zero_div,add_zero]
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


open MeasureTheory Set
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1600000

def generalMeanExponentialPrimitive (a v β : ℝ) : ℝ :=
  Real.exp (-(β*v))/β*(1+Real.log (v/a)+exponentialResolvent (β*v))

theorem generalMean_exponential_primitive_integral {a v β : ℝ}
    (ha : 0<a) (hav : a≤v) (hβ : 0<β) :
    (∫u in Ioi v,entropyKernel a u*Real.exp (-(β*u)))=
      generalMeanExponentialPrimitive a v β :=
  generalMean_entropy_exponential_integral ha hav hβ

theorem generalMean_exp_scale {K L : ℝ} (hK : 0<K) (hKL : L=1+Real.log K) :
    Real.exp (2*L-2)=K^2 := by
  rw [hKL,show 2*(1+Real.log K)-2=Real.log K+Real.log K by ring,Real.exp_add,
    Real.exp_log hK]
  ring

theorem generalMean_log_cutoff {K L c : ℝ} (hK : 0<K) (hL : 1≤L) (hc : 0<c)
    (hKL : L=1+Real.log K) :
    Real.log (c*K^2*L)=2*L-2+Real.log (c*L) := by
  have hK2 : K^2≠0 := pow_ne_zero 2 hK.ne'
  rw [show c*K^2*L=K^2*(c*L) by ring,Real.log_mul hK2 (by positivity),Real.log_pow,hKL]
  ring

theorem generalMean_exp_scale_factor {K L z : ℝ} (hK : 0<K) (hKL : L=1+Real.log K) :
    K^2*Real.exp (-z*L/2)=Real.exp (-2-(z/2-2)*L) := by
  rw [← generalMean_exp_scale hK hKL,← Real.exp_add]
  congr 1
  ring

theorem generalMean_base_integral_scale {A K L q c : ℝ}
    (hK : 0<K) (hL : 1≤L) (hq : 0<q) (hc : 0<c) (hKL : L=1+Real.log K) :
    A*generalMeanExponentialPrimitive (c*K^2*L) (c*K^2*L) (q/(2*K^2))=
      generalMeanRemainder A q c L := by
  have ha : c*K^2*L≠0 := by positivity
  have harg : q/(2*K^2)*(c*K^2*L)=q*c*L/2 := by field_simp
  unfold generalMeanExponentialPrimitive generalMeanRemainder
  rw [harg,div_self ha,Real.log_one,add_zero]
  have hdiv : Real.exp (-(q*c*L/2))/(q/(2*K^2))=
      (2/q)*(K^2*Real.exp (-(q*c)*L/2)) := by simp only [div_eq_mul_inv,inv_inv,mul_inv_rev];ring
  rw [hdiv,generalMean_exp_scale_factor hK hKL]
  ring

theorem generalMean_continuation_integral_scale {A K L q c s : ℝ}
    (hK : 0<K) (hL : 1≤L) (hq : 1<q) (hc : 0<c) (hcs : c≤s)
    (hKL : L=1+Real.log K) :
    A*Real.exp (-(q-1)*s*L/2)*
        generalMeanExponentialPrimitive (c*K^2*L) (s*K^2*L) (1/(2*K^2))-
      A*generalMeanExponentialPrimitive (c*K^2*L) (s*K^2*L) (q/(2*K^2))=
      generalMeanContinuation A q c s L := by
  have hs : 0<s := hc.trans_le hcs
  have hq0 : 0<q := by linarith
  have hratio : s*K^2*L/(c*K^2*L)=s/c := by field_simp
  have harg1 : 1/(2*K^2)*(s*K^2*L)=s*L/2 := by field_simp
  have hargq : q/(2*K^2)*(s*K^2*L)=q*s*L/2 := by field_simp
  unfold generalMeanExponentialPrimitive generalMeanContinuation
  rw [hratio,harg1,hargq]
  have hd1 : Real.exp (-(s*L/2))/(1/(2*K^2))=2*K^2*Real.exp (-s*L/2) := by simp only [div_eq_mul_inv,inv_inv,mul_inv_rev];ring
  have hdq : Real.exp (-(q*s*L/2))/(q/(2*K^2))=(2/q)*K^2*Real.exp (-(q*s)*L/2) := by simp only [div_eq_mul_inv,inv_inv,mul_inv_rev];ring
  rw [hd1,hdq]
  have he : Real.exp (-(q-1)*s*L/2)*Real.exp (-s*L/2)=Real.exp (-(q*s)*L/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfactor := generalMean_exp_scale_factor (z := q*s) hK hKL
  have hcommon : Real.exp (-(q-1)*s*L/2)*(K^2*Real.exp (-s*L/2))=
      Real.exp (-2-(q*s/2-2)*L) := by
    rw [← mul_assoc,mul_comm _ (K^2),mul_assoc,he,hfactor]
  calc
    _ = 2*A*(Real.exp (-(q-1)*s*L/2)*(K^2*Real.exp (-s*L/2)))*
        (1+Real.log (s/c)+exponentialResolvent (s*L/2))-
        (2*A/q)*(K^2*Real.exp (-(q*s)*L/2))*
          (1+Real.log (s/c)+exponentialResolvent (q*s*L/2)) := by ring
    _ = _ := by rw [hcommon,hfactor];ring

end
end SingularValueBounds.KL
