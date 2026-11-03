import SingularValueBounds.KL.Upper.EndpointMeanPolynomial

open MeasureTheory Set
open scoped BigOperators
namespace SingularValueBounds.KL
open Certificates
noncomputable section
set_option maxHeartbeats 1800000

theorem weighted_list_le {α : Type*} (rs : List α) {a b : α → ℝ}
    (h : ∀ r ∈ rs,a r≤b r) : (rs.map a).sum≤(rs.map b).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simpa only [List.map_cons,List.sum_cons] using
      add_le_add (h r List.mem_cons_self)
        (ih (fun s hs => h s (List.mem_cons_of_mem _ hs)))

theorem weighted_list_convex {α : Type*} (rs : List α) {d : α → ℝ} {f : α → ℝ → ℝ}
    {l r c : ℝ} (hd : ∀j∈rs,0≤d j) (hf : ∀j∈rs,ConvexOn ℝ (Icc l r) (f j)) :
    ConvexOn ℝ (Icc l r) (fun x => c+(rs.map (fun j => d j*f j x)).sum) := by
  induction rs with
  | nil =>
    refine ⟨convex_Icc _ _,?_⟩
    intro x hx y hy u v hu hv huv
    simp only [List.map_nil,List.sum_nil,add_zero,smul_eq_mul]
    have he := congrArg (fun t : ℝ => t*c) huv
    nlinarith
  | cons j rs ih =>
    have hh := ConvexOn.smul (hd j List.mem_cons_self) (hf j List.mem_cons_self)
    have ht := ih (fun s hs => hd s (List.mem_cons_of_mem _ hs))
      (fun s hs => hf s (List.mem_cons_of_mem _ hs))
    apply (hh.add ht).congr
    intro x hx
    simp only [Pi.add_apply,smul_eq_mul,List.map_cons,List.sum_cons]
    ring

def endpointMeanEnvelope (ki : Fin 60) (ai : Fin 42) (a k : ℝ) : ℝ :=
  ((logRoundedQ ((endpointMeanCutoff ki ai : ℚ)/200)).2 : ℝ)+
    (endpointAnalyticTailQ (endpointMeanCutoff ki ai) : ℝ)+
    ((endpointMeanRuns ki ai).map (fun r =>
      (endpointRunWeightQ (endpointMeanCutoff ki ai) r : ℝ)*
        upperJointPrefactor ((r.rate : ℝ)/100) a k)).sum

theorem endpointMeanEnvelope_convex (h : EndpointMeanCertificateConditions)
    (ki : Fin 60) (ai : Fin 42) (hact : endpointMeanActive ki ai) :
    (∀k∈Icc ((endpointMeanBox ki ai).bottom : ℝ) (endpointMeanBox ki ai).top,
      ConvexOn ℝ (Icc ((endpointMeanBox ki ai).left : ℝ) (endpointMeanBox ki ai).right)
        (fun a => endpointMeanEnvelope ki ai a k)) ∧
    (∀a∈Icc ((endpointMeanBox ki ai).left : ℝ) (endpointMeanBox ki ai).right,
      ConvexOn ℝ (Icc ((endpointMeanBox ki ai).bottom : ℝ) (endpointMeanBox ki ai).top)
        (fun k => endpointMeanEnvelope ki ai a k)) := by
  have hb := h.jointBoxes ki ai hact
  have hn := h.jointNumerical ki ai hact
  have hc := (h.jointCutoff ki ai hact).1
  have hw (r : EndpointRateRun) (hr : r∈endpointMeanRuns ki ai) :
      (0:ℝ)≤endpointRunWeightQ (endpointMeanCutoff ki ai) r := by
    obtain ⟨_,hs,_,hq,_,_,_⟩ := hn.2.1 r hr
    exact_mod_cast endpointRunWeightQ_nonneg hc hs.le (by omega)
  constructor
  · intro k hk
    exact weighted_list_convex _ hw (fun r hr => upperJointPrefactor_convex_third _ _ _ _)
  · intro a ha
    apply weighted_list_convex _ hw
    intro r hr
    obtain ⟨_,_,_,hq,_,hg,_⟩ := hn.2.1 r hr
    have hq0 : (0:ℝ)≤(r.rate:ℝ)/100 := by positivity
    have ha0 : 0≤a := (by exact_mod_cast hb.1 : (0:ℝ)≤(endpointMeanBox ki ai).left).trans ha.1
    have hkl : (0:ℝ)<(endpointMeanBox ki ai).bottom := by exact_mod_cast hb.2.1
    have hgap0 : ((((r.rate:ℚ)/100)*(endpointMeanBox ki ai).top^2:ℚ):ℝ)<1 := by exact_mod_cast hg
    push_cast at hgap0
    have hgap : ((r.rate:ℝ)/100)*((endpointMeanBox ki ai).top:ℝ)^2<1 := hgap0
    exact upperJointPrefactor_convex_shape hq0 ha0 hkl hgap

theorem endpointMean_corner_contains (ki : Fin 60) (ai : Fin 42)
    (hact : endpointMeanActive ki ai) (v : Fin 4) :
    (endpointMeanBox ki ai).contains (endpointMeanCornerA ki ai v) (endpointMeanCornerK ki ai v) := by
  have hk : (endpointMeanBox ki ai).bottom<(endpointMeanBox ki ai).top := by
    dsimp [endpointMeanBox]
    push_cast
    linarith
  have haR : ((endpointMeanBox ki ai).left:ℝ)≤(endpointMeanBox ki ai).right := by exact_mod_cast hact.1.le
  have hkR : ((endpointMeanBox ki ai).bottom:ℝ)≤(endpointMeanBox ki ai).top := by exact_mod_cast hk.le
  unfold endpointMeanCornerA endpointMeanCornerK RationalBox.contains
  split_ifs <;> constructor <;> constructor <;>
    first | exact le_rfl | exact haR | exact hkR

theorem endpointMeanEnvelope_corner (h : EndpointMeanCertificateConditions)
    (ki : Fin 60) (ai : Fin 42) (hact : endpointMeanActive ki ai) (v : Fin 4) :
    endpointMeanEnvelope ki ai (endpointMeanCornerA ki ai v) (endpointMeanCornerK ki ai v)≤
      (endpointMeanCorner ki ai v : ℝ) := by
  have hn := h.jointNumerical ki ai hact
  have hc := (h.jointCutoff ki ai hact).1
  have hb := h.jointBoxes ki ai hact
  have hv := endpointMean_corner_contains ki ai hact v
  have hk : (0:ℚ)<endpointMeanCornerK ki ai v := by
    exact_mod_cast (show (0:ℝ)<endpointMeanCornerK ki ai v from
      (by exact_mod_cast hb.2.1 : (0:ℝ)<(endpointMeanBox ki ai).bottom).trans_le hv.2.1)
  have ha : (0:ℚ)≤endpointMeanCornerA ki ai v := by
    exact_mod_cast (show (0:ℝ)≤endpointMeanCornerA ki ai v from
      (by exact_mod_cast hb.1 : (0:ℝ)≤(endpointMeanBox ki ai).left).trans hv.1.1)
  have hkt : endpointMeanCornerK ki ai v≤(endpointMeanBox ki ai).top := by exact_mod_cast hv.2.2
  have hs : endpointMeanEnvelope ki ai (endpointMeanCornerA ki ai v) (endpointMeanCornerK ki ai v)≤
      (endpointMeanNumericCorner ki ai v:ℝ) := by
    unfold endpointMeanEnvelope endpointMeanNumericCorner
    push_cast
    apply add_le_add le_rfl
    simp only [List.map_map,Function.comp_def,Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat]
    apply weighted_list_le
    intro r hr
    obtain ⟨_,hstep,_,hq,_,hgap,_⟩ := hn.2.1 r hr
    have hw : (0:ℝ)≤endpointRunWeightQ (endpointMeanCutoff ki ai) r := by
      exact_mod_cast endpointRunWeightQ_nonneg hc hstep.le (by omega)
    have hq0 : (0:ℚ)≤(r.rate:ℚ)/100 := by positivity
    have hgc : (r.rate:ℚ)/100*(endpointMeanCornerK ki ai v)^2<1 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk.le hkt 2) hq0).trans_lt hgap
    have hp := endpointJoint24_sound hk ha hgc (hn.2.2.1 v r hr)
    norm_num only [Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat] at hp
    exact mul_le_mul_of_nonneg_left hp hw
  exact hs.trans (by exact_mod_cast hn.2.2.2 v)

theorem endpointMeanEnvelope_bilinear (h : EndpointMeanCertificateConditions)
    (ki : Fin 60) (ai : Fin 42) (hact : endpointMeanActive ki ai) {a k : ℝ}
    (hbox : (endpointMeanBox ki ai).contains a k) :
    endpointMeanEnvelope ki ai a k≤realEval₂ (endpointMeanBilinearQ ki ai) a k := by
  have hc := endpointMeanEnvelope_convex h ki ai hact
  have ha : ((endpointMeanBox ki ai).left : ℝ)<(endpointMeanBox ki ai).right := by exact_mod_cast hact.1
  have hk : ((endpointMeanBox ki ai).bottom : ℝ)<(endpointMeanBox ki ai).top := by exact_mod_cast (h.jointBoxes ki ai hact).2.2.1
  have hh := separately_convex_corner_bound hbox.1 hbox.2 hc.1 hc.2 ha hk
  have h0 := endpointMeanEnvelope_corner h ki ai hact 0
  have h1 := endpointMeanEnvelope_corner h ki ai hact 1
  have h2 := endpointMeanEnvelope_corner h ki ai hact 2
  have h3 := endpointMeanEnvelope_corner h ki ai hact 3
  norm_num only [endpointMeanCornerA,endpointMeanCornerK,Fin.reduceEq,or_true,or_false,if_true,if_false] at h0 h1 h2 h3
  have hw (u v : ℝ) (hu : 0≤u) (hv : 0≤v) {x y : ℝ} (hxy : x≤y) : u*v*x≤u*v*y :=
    mul_le_mul_of_nonneg_left hxy (mul_nonneg hu hv)
  rw [endpointMeanBilinear_eq_corners ki ai hact]
  dsimp only
  apply hh.trans
  have hAl : 0≤((endpointMeanBox ki ai).right : ℝ)-a := sub_nonneg.mpr hbox.1.2
  have hAr : 0≤a-((endpointMeanBox ki ai).left : ℝ) := sub_nonneg.mpr hbox.1.1
  have hKl : 0≤((endpointMeanBox ki ai).top : ℝ)-k := sub_nonneg.mpr hbox.2.2
  have hKr : 0≤k-((endpointMeanBox ki ai).bottom : ℝ) := sub_nonneg.mpr hbox.2.1
  have wa := div_nonneg hAl (sub_pos.mpr ha).le
  have wb := div_nonneg hAr (sub_pos.mpr ha).le
  have wc := div_nonneg hKl (sub_pos.mpr hk).le
  have wd := div_nonneg hKr (sub_pos.mpr hk).le
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left h0 (mul_nonneg wa wc))
    (mul_le_mul_of_nonneg_left h1 (mul_nonneg wb wc)))
    (mul_le_mul_of_nonneg_left h2 (mul_nonneg wa wd)))
    (mul_le_mul_of_nonneg_left h3 (mul_nonneg wb wd))

end
end SingularValueBounds.KL
