import SingularValueBounds.KL.Upper.GeneralMeanScaling
import SingularValueBounds.KL.Certificates.EndpointEntropyRuns

/-! Exact integration of each exponential survival bound. A finite list chooses
where to change rates; no mesh quadrature or prefix-moment calculation is used. -/
open MeasureTheory Set
namespace SingularValueBounds.KL
open Certificates
noncomputable section

/-- The exact integral from `u` to infinity of the entropy kernel times an
exponential with rate `q / 2`. -/
def entropyExpPrimitive (c q u : ℝ) : ℝ :=
  (2/q)*Real.exp (-q*u/2)*(1+Real.log (u/c)+exponentialResolvent (q*u/2))

theorem entropyExpPrimitive_eq_general (c q u : ℝ) :
    entropyExpPrimitive c q u = generalMeanExponentialPrimitive c u (q/2) := by
  unfold entropyExpPrimitive generalMeanExponentialPrimitive
  rw [show -(q/2*u) = -q*u/2 by ring, show q/2*u = q*u/2 by ring]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

private theorem entropy_exp_integrable {c q : ℝ} (hc : 0<c) (hq : 0<q) :
    IntegrableOn (fun u => entropyKernel c u*Real.exp (-q*u/2)) (Ioi c) := by
  apply entropy_tail_integrable (C := 1) (r := q/2) hc (by positivity)
    (by fun_prop) (fun u => Real.exp_nonneg _)
  intro u hu
  rw [one_mul]
  apply le_of_eq
  congr 1
  ring

theorem entropy_exp_Ioi_integral {c q l : ℝ}
    (hc : 0<c) (hcl : c≤l) (hq : 0<q) :
    (∫u in Ioi l,entropyKernel c u*Real.exp (-q*u/2)) = entropyExpPrimitive c q l := by
  rw [entropyExpPrimitive_eq_general]
  convert generalMean_exponential_primitive_integral hc hcl (by positivity : 0<q/2) using 1
  congr 1
  funext u
  congr 1
  congr 1
  ring

/-- Integration on a run is subtraction of two exact tail primitives. -/
theorem entropy_exp_Ioc_integral {c q l r : ℝ}
    (hc : 0<c) (hcl : c≤l) (hlr : l≤r) (hq : 0<q) :
    (∫u in Ioc l r,entropyKernel c u*Real.exp (-q*u/2)) =
      entropyExpPrimitive c q l-entropyExpPrimitive c q r := by
  have hi := entropy_exp_integrable hc hq
  have hs := entropy_integral_split hlr (hi.mono_set (Ioi_subset_Ioi hcl))
  rw [entropy_exp_Ioi_integral hc hcl hq,
    entropy_exp_Ioi_integral hc (hcl.trans hlr) hq,
    intervalIntegral.integral_of_le hlr] at hs
  linarith

theorem entropy_exp_weight_nonneg {c q l r : ℝ}
    (hc : 0<c) (hcl : c≤l) (hlr : l≤r) (hq : 0<q) :
    0≤entropyExpPrimitive c q l-entropyExpPrimitive c q r := by
  rw [← entropy_exp_Ioc_integral hc hcl hlr hq]
  exact setIntegral_nonneg measurableSet_Ioc (fun u hu =>
    mul_nonneg (entropyKernel_nonneg hc (hcl.trans hu.1.le)) (Real.exp_nonneg _))

theorem entropy_exponential_cell_bound {c l r A q : ℝ} {T : ℝ → ℝ}
    (hc : 0<c) (hcl : c≤l) (hlr : l≤r) (hq : 0<q)
    (hTi : IntegrableOn (fun u => entropyKernel c u*T u) (Ioi c))
    (hBound : ∀u∈Ioc l r,T u≤A*Real.exp (-q*u/2)) :
    (∫u in Ioc l r,entropyKernel c u*T u)≤
      A*(entropyExpPrimitive c q l-entropyExpPrimitive c q r) := by
  have hs : Ioc l r ⊆ Ioi c := fun u hu => hcl.trans_lt hu.1
  have hEi := ((entropy_exp_integrable hc hq).mono_set hs).const_mul A
  have hh := setIntegral_mono_on (hTi.mono_set hs) hEi measurableSet_Ioc (fun u hu => by
    have h := mul_le_mul_of_nonneg_left (hBound u hu)
      (entropyKernel_nonneg hc (hcl.trans hu.1.le))
    convert h using 1 <;> ring)
  rw [integral_const_mul,entropy_exp_Ioc_integral hc hcl hlr hq] at hh
  exact hh

theorem entropy_exponential_tail_bound {c l A q : ℝ} {T : ℝ → ℝ}
    (hc : 0<c) (hcl : c≤l) (hq : 0<q)
    (hTi : IntegrableOn (fun u => entropyKernel c u*T u) (Ioi c))
    (hBound : ∀u∈Ioi l,T u≤A*Real.exp (-q*u/2)) :
    (∫u in Ioi l,entropyKernel c u*T u)≤A*entropyExpPrimitive c q l := by
  have hs : Ioi l ⊆ Ioi c := Ioi_subset_Ioi hcl
  have hEi := ((entropy_exp_integrable hc hq).mono_set hs).const_mul A
  have hh := setIntegral_mono_on (hTi.mono_set hs) hEi measurableSet_Ioi (fun u hu => by
    have h := mul_le_mul_of_nonneg_left (hBound u hu)
      (entropyKernel_nonneg hc (hcl.trans hu.le))
    convert h using 1 <;> ring)
  rw [integral_const_mul,entropy_exp_Ioi_integral hc hcl hq] at hh
  exact hh

/-- A list of contiguous runs gives an exact partition, including zero-length
runs. Only the chosen rates and their pointwise survival bounds enter. -/
theorem entropy_exponential_runs_bound {c : ℝ} {x : ℕ → ℝ} {T : ℝ → ℝ}
    {start stop : ℕ} {rs : List EndpointRateRun} {A q : EndpointRateRun → ℝ}
    (hc : 0<c) (hx : Monotone x) (hcx : c≤x start)
    (hcover : EndpointRunsCover start stop rs)
    (hTi : IntegrableOn (fun u => entropyKernel c u*T u) (Ioi c))
    (hq : ∀r∈rs,0<q r)
    (hBound : ∀r∈rs,∀u∈Ioc (x r.start) (x r.stop),T u≤A r*Real.exp (-q r*u/2)) :
    (∫u in Ioi (x start),entropyKernel c u*T u)≤
      (rs.map (fun r => A r*(entropyExpPrimitive c (q r) (x r.start)-
        entropyExpPrimitive c (q r) (x r.stop)))).sum+
        ∫u in Ioi (x stop),entropyKernel c u*T u := by
  induction rs generalizing start with
  | nil =>
    have he : start=stop := hcover
    simp [he]
  | cons r rest ih =>
    obtain ⟨hs,hr,hrest⟩ := hcover
    subst start
    have hcr : c≤x r.stop := hcx.trans (hx hr)
    have hsplit := entropy_integral_split (hx hr) (hTi.mono_set (Ioi_subset_Ioi hcx))
    rw [intervalIntegral.integral_of_le (hx hr)] at hsplit
    have hcell := entropy_exponential_cell_bound hc hcx (hx hr) (hq r (by simp)) hTi
      (hBound r (by simp))
    have hrem := ih hcr hrest (fun t ht => hq t (by simp [ht]))
      (fun t ht => hBound t (by simp [ht]))
    simp only [List.map_cons,List.sum_cons]
    linarith

/-- Integer labels locate the original rate-switch boundaries; integration on
these intervals is analytic and makes no mesh-approximation assumption. -/
def endpointRunPoint (j0 j : ℕ) : ℝ := (max j0 (j-1) : ℕ)/200

theorem endpointRunPoint_mono (j0 : ℕ) : Monotone (endpointRunPoint j0) := by
  intro j k hjk
  unfold endpointRunPoint
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact_mod_cast max_le_max_left j0 (Nat.sub_le_sub_right hjk 1)

theorem endpointRunPoint_start (j0 : ℕ) : endpointRunPoint j0 j0 = (j0 : ℝ)/200 := by
  simp [endpointRunPoint,Nat.sub_le]

/-- Complete infinite entropy bound using the finite analytic runs and one
exponential tail. No numerical premise is hidden in the partition argument. -/
theorem entropy_analytic_runs_bound {j0 stop : ℕ} {rs : List EndpointRateRun}
    {T : ℝ → ℝ} {U : ℝ} {A q : EndpointRateRun → ℝ}
    (hj0 : 0<j0) (hcover : EndpointRunsCover j0 stop rs)
    (hT : Antitone T) (hT0 : ∀u,0≤T u)
    (hTail : ∀u,0≤u → T u≤U*Real.exp (-((9/20 : ℝ)*u)))
    (hq : ∀r∈rs,0<q r)
    (hBound : ∀r∈rs,∀u∈Ioc (endpointRunPoint j0 r.start) (endpointRunPoint j0 r.stop),
      T u≤A r*Real.exp (-q r*u/2)) :
    Real.log ((j0 : ℝ)/200)+
      (∫u in Ioi ((j0 : ℝ)/200),entropyKernel ((j0 : ℝ)/200) u*T u)≤
      Real.log ((j0 : ℝ)/200)+
        (rs.map (fun r => A r*(entropyExpPrimitive ((j0 : ℝ)/200) (q r) (endpointRunPoint j0 r.start)-
          entropyExpPrimitive ((j0 : ℝ)/200) (q r) (endpointRunPoint j0 r.stop)))).sum+
        U*entropyExpPrimitive ((j0 : ℝ)/200) (9/10) (endpointRunPoint j0 stop) := by
  have hc : 0<(j0 : ℝ)/200 := by positivity
  have hcx : (j0 : ℝ)/200≤endpointRunPoint j0 j0 := (endpointRunPoint_start j0).ge
  have hTi := entropy_tail_integrable hc (by norm_num : (0:ℝ)<9/20) hT.measurable hT0
    (fun u hu => hTail u (hc.le.trans hu.le))
  have hmain := entropy_exponential_runs_bound hc (endpointRunPoint_mono j0) hcx hcover hTi hq hBound
  rw [endpointRunPoint_start] at hmain
  have hstop : (j0 : ℝ)/200≤endpointRunPoint j0 stop :=
    hcx.trans (endpointRunPoint_mono j0 hcover.le)
  have hrem := entropy_exponential_tail_bound hc hstop (by norm_num : (0:ℝ)<9/10) hTi (A := U) (by
    intro u hu
    convert hTail u (hc.le.trans (hstop.trans hu.le)) using 1 <;> congr 2 <;> ring)
  linarith

end
end SingularValueBounds.KL
