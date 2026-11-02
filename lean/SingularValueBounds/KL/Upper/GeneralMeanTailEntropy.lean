import SingularValueBounds.KL.Upper.GeneralMeanScaling
import SingularValueBounds.KL.Upper.GeneralMeanNumerics

open MeasureTheory Set
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1800000

theorem generalMean_exponential_entropy_integrable {a A r : ℝ}
    (ha : 0<a) (hA : 0≤A) (hr : 0<r) :
    IntegrableOn (fun u => entropyKernel a u*(A*Real.exp (-(r*u)))) (Ioi a) :=
  entropy_tail_integrable (C := A) (T := fun u => A*Real.exp (-(r*u))) ha hr
    (by fun_prop) (fun u => mul_nonneg hA (Real.exp_nonneg _)) (fun u hu => le_rfl)

theorem generalMean_two_piece_integral {a v A B r t : ℝ} {T : ℝ → ℝ}
    (ha : 0<a) (hav : a≤v) (hA : 0≤A) (hB : 0≤B) (hr : 0<r) (ht : 0<t)
    (hTi : IntegrableOn (fun u => entropyKernel a u*T u) (Ioi a))
    (hlow : ∀u∈Icc a v,T u≤A*Real.exp (-(r*u)))
    (hhigh : ∀u,v<u → T u≤B*Real.exp (-(t*u))) :
    (∫u in Ioi a,entropyKernel a u*T u)≤
      A*generalMeanExponentialPrimitive a a r-
        A*generalMeanExponentialPrimitive a v r+B*generalMeanExponentialPrimitive a v t := by
  have hiA := generalMean_exponential_entropy_integrable ha hA hr
  have hiB := generalMean_exponential_entropy_integrable ha hB ht
  have hAi (x : ℝ) : (fun u => entropyKernel a u*(A*Real.exp (-(r*u)))) x=
      A*(entropyKernel a x*Real.exp (-(r*x))) := by ring
  have hBi (x : ℝ) : (fun u => entropyKernel a u*(B*Real.exp (-(t*u)))) x=
      B*(entropyKernel a x*Real.exp (-(t*x))) := by ring
  have hsplit := entropy_integral_split hav hTi
  have hsplitA := entropy_integral_split hav hiA
  have hTinterval : IntervalIntegrable (fun u => entropyKernel a u*T u) volume a v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hav).mpr
      (hTi.mono_set (fun u hu => hu.1))
  have hAinterval : IntervalIntegrable (fun u => entropyKernel a u*(A*Real.exp (-(r*u)))) volume a v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hav).mpr
      (hiA.mono_set (fun u hu => hu.1))
  have hlowint := intervalIntegral.integral_mono_on hav hTinterval hAinterval
    (fun u hu => mul_le_mul_of_nonneg_left (hlow u hu) (entropyKernel_nonneg ha hu.1))
  have hhighint := setIntegral_mono_on
    (hTi.mono_set (Ioi_subset_Ioi hav)) (hiB.mono_set (Ioi_subset_Ioi hav)) measurableSet_Ioi
    (fun u hu => mul_le_mul_of_nonneg_left (hhigh u hu)
      (entropyKernel_nonneg ha (hav.trans hu.le)))
  have hAbase : (∫u in Ioi a,entropyKernel a u*(A*Real.exp (-(r*u))))=
      A*generalMeanExponentialPrimitive a a r := by
    simp_rw [hAi]
    rw [integral_const_mul,generalMean_exponential_primitive_integral ha le_rfl hr]
  have hAtail : (∫u in Ioi v,entropyKernel a u*(A*Real.exp (-(r*u))))=
      A*generalMeanExponentialPrimitive a v r := by
    simp_rw [hAi]
    rw [integral_const_mul,generalMean_exponential_primitive_integral ha hav hr]
  have hBtail : (∫u in Ioi v,entropyKernel a u*(B*Real.exp (-(t*u))))=
      B*generalMeanExponentialPrimitive a v t := by
    simp_rw [hBi]
    rw [integral_const_mul,generalMean_exponential_primitive_integral ha hav ht]
  rw [hAbase,hAtail] at hsplitA
  rw [hBtail] at hhighint
  linarith

theorem generalMean_one_piece_integral {a A r : ℝ} {T : ℝ → ℝ}
    (ha : 0<a) (hA : 0≤A) (hr : 0<r)
    (hTi : IntegrableOn (fun u => entropyKernel a u*T u) (Ioi a))
    (hTail : ∀u,a<u → T u≤A*Real.exp (-(r*u))) :
    (∫u in Ioi a,entropyKernel a u*T u)≤A*generalMeanExponentialPrimitive a a r := by
  have hiA := generalMean_exponential_entropy_integrable ha hA hr
  have hh := setIntegral_mono_on hTi hiA measurableSet_Ioi
    (fun u hu => mul_le_mul_of_nonneg_left (hTail u hu) (entropyKernel_nonneg ha hu.le))
  have hid : (fun u => entropyKernel a u*(A*Real.exp (-(r*u))))=
      (fun u => A*(entropyKernel a u*Real.exp (-(r*u)))) := by funext u;ring
  rw [hid,integral_const_mul,generalMean_exponential_primitive_integral ha le_rfl hr] at hh
  exact hh

def GeneralMeanTailProfile (T : ℝ → ℝ) (A q s K L : ℝ) : Prop :=
  if 1<q then
    (∀u,0≤u → u≤s*K^2*L → T u≤A*Real.exp (-q*u/(2*K^2))) ∧
    (∀u,s*K^2*L<u → T u≤A*Real.exp (-u/(2*K^2)-s*(q-1)*L/2))
  else ∀u,0≤u → T u≤A*Real.exp (-q*u/(2*K^2))

theorem generalMean_tail_integral_bound {T : ℝ → ℝ} {A q c s K L : ℝ}
    (hK : 0<K) (hL : 1≤L) (hKL : L=1+Real.log K)
    (hA : 0≤A) (hq : 0<q) (hc : 0<c) (hcont : 1<q → c≤s)
    (hTi : IntegrableOn (fun u => entropyKernel (c*K^2*L) u*T u) (Ioi (c*K^2*L)))
    (hTail : GeneralMeanTailProfile T A q s K L) :
    (∫u in Ioi (c*K^2*L),entropyKernel (c*K^2*L) u*T u)≤
      generalMeanError A q c s L := by
  have hLp : 0<L := by linarith
  have ha : 0<c*K^2*L := by positivity
  unfold GeneralMeanTailProfile at hTail
  by_cases hq1 : 1<q
  · have hcs := hcont hq1
    have hs : 0<s := hc.trans_le hcs
    have hp := if_pos hq1 ▸ hTail
    have hcut : c*K^2*L≤s*K^2*L := by gcongr
    have hlow : ∀u∈Icc (c*K^2*L) (s*K^2*L),T u≤A*Real.exp (-((q/(2*K^2))*u)) := by
      intro u hu
      have hh := hp.1 u (ha.le.trans hu.1) hu.2
      convert! hh using 1 <;> congr 2 <;> ring
    have hhigh : ∀u,s*K^2*L<u →
        T u≤(A*Real.exp (-(q-1)*s*L/2))*Real.exp (-((1/(2*K^2))*u)) := by
      intro u hu
      have hh := hp.2 u hu
      rw [mul_assoc,← Real.exp_add]
      convert! hh using 1 <;> congr 2 <;> ring
    have hi := generalMean_two_piece_integral ha hcut hA (by positivity)
      (by positivity : 0<q/(2*K^2)) (by positivity : 0<1/(2*K^2)) hTi hlow hhigh
    have hbase := generalMean_base_integral_scale (A := A) hK hL hq hc hKL
    have hcorrection := generalMean_continuation_integral_scale (A := A) hK hL hq1 hc hcs hKL
    unfold generalMeanError
    rw [if_pos hq1]
    linarith
  · have hp := if_neg hq1 ▸ hTail
    have hi := generalMean_one_piece_integral ha hA (by positivity : 0<q/(2*K^2)) hTi
      (fun u hu => by
        have hh := hp u (ha.le.trans hu.le)
        convert! hh using 1 <;> congr 2 <;> ring)
    rw [generalMean_base_integral_scale hK hL hq hc hKL] at hi
    simpa only [generalMeanError,if_neg hq1,add_zero] using hi

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Full scalar entropy consequence of one finite numerical row. -/
theorem generalMean_entropy_cost_of_row {r : Certificates.GeneralMeanRow}
    (h : Certificates.GeneralMeanNumericalConditions r) {K L : ℝ}
    (hK : 0<K) (hL : 1≤L) (hKL : L=1+Real.log K)
    {W : Ω → ℝ} (hW : Measurable W) (hWi : Integrable W μ)
    (hW0 : ∀ω,0≤W ω) (hMean : (∫ω,W ω ∂μ)=1)
    (hWE : Integrable (fun ω => W ω*Real.log (W ω)) μ)
    {C t : ℝ} (ht : 0<t)
    (hGlobal : ∀u,0≤u → μ.real {ω | u<W ω}≤C*Real.exp (-(t*u)))
    (hTail : GeneralMeanTailProfile (fun u => μ.real {ω | u<W ω})
      r.prefactor r.q r.cutoff K L) :
    (∫ω,W ω*Real.log (W ω) ∂μ)+(r.J:ℝ)/2≤(47/20)*L := by
  have hc : (0:ℝ)<r.c := by exact_mod_cast h.cutoff
  have hq : (0:ℝ)<r.q := by exact_mod_cast h.rate
  have ha : 0<(r.c:ℝ)*K^2*L := by positivity
  have hTm : Measurable (fun u => μ.real {ω | u<W ω}) := by
    apply Antitone.measurable
    intro u v huv
    exact measureReal_mono (fun ω hω => lt_of_le_of_lt huv hω) (measure_ne_top μ _)
  have hTi := entropy_tail_integrable ha ht hTm (fun u => measureReal_nonneg)
    (fun u hu => hGlobal u (ha.le.trans hu.le))
  have he := generalMean_tail_integral_bound hK hL hKL h.prefactor_pos.le hq hc
    (fun hq1 => by
      have hqq : (1:ℚ)<r.q := by exact_mod_cast hq1
      exact_mod_cast (h.continuation hqq).1) hTi hTail
  have hEntropy := entropy_tail_integral hW hW0 hWi hMean hWE ha
  change (∫ω,W ω*Real.log (W ω) ∂μ)≤Real.log ((r.c:ℝ)*K^2*L)+
    (∫u in Ioi ((r.c:ℝ)*K^2*L),entropyKernel ((r.c:ℝ)*K^2*L) u*
      μ.real {ω | u<W ω}) at hEntropy
  rw [generalMean_log_cutoff hK hL hc hKL] at hEntropy
  have hAll := h.allL_sound hL
  linarith

end
end SingularValueBounds.KL
