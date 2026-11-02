import SingularValueBounds.KL.Upper.EndpointMeanPolynomial

open MeasureTheory Set
open scoped BigOperators
namespace SingularValueBounds.KL
open Certificates
noncomputable section
set_option maxHeartbeats 1800000

theorem finite_weighted_sum_convex {s : Finset ℕ} {d : ℕ → ℝ} {f : ℕ → ℝ → ℝ}
    {l r c : ℝ} (hd : ∀j∈s,0≤d j) (hf : ∀j∈s,ConvexOn ℝ (Icc l r) (f j)) :
    ConvexOn ℝ (Icc l r) (fun x => c+∑j∈s,d j*f j x) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy u v hu hv huv
  have hsum := Finset.sum_le_sum (s := s) (fun j hj =>
    mul_le_mul_of_nonneg_left ((hf j hj).2 hx hy hu hv huv) (hd j hj))
  simp only [smul_eq_mul] at hsum ⊢
  have he : (∑j∈s,d j*(u*f j x+v*f j y))=
      u*(∑j∈s,d j*f j x)+v*(∑j∈s,d j*f j y) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    congr 1 <;> rw [Finset.mul_sum] <;> apply Finset.sum_congr rfl <;> intros <;> ring
  rw [he] at hsum
  have hc : u*c+v*c=c := by calc
    _=(u+v)*c := by ring
    _=c := by rw [huv,one_mul]
  linarith

def endpointMeanEnvelopeCoeff (ki : Fin 60) (ai : Fin 42) (j : ℕ) : ℝ :=
  (entropyGridKernelQ (endpointMeanCutoff ki ai) j : ℝ)*
    (endpointDecayQ (endpointMeanRate ki ai j) j : ℝ)/200

def endpointMeanEnvelope (ki : Fin 60) (ai : Fin 42) (a k : ℝ) : ℝ :=
  ((logRoundedQ ((endpointMeanCutoff ki ai : ℚ)/200)).2 : ℝ)+
    (entropyGridTailQ (endpointMeanCutoff ki ai) (endpointDecayQ 90 8000) : ℝ)+
    ∑j∈Finset.Ico (endpointMeanCutoff ki ai) 8000,
      endpointMeanEnvelopeCoeff ki ai j*upperJointPrefactor ((endpointMeanRate ki ai j : ℝ)/100) a k

theorem endpointMeanEnvelope_eq_grid (ki : Fin 60) (ai : Fin 42) (a k : ℝ) :
    endpointMeanEnvelope ki ai a k=entropyGridBoundReal (endpointMeanCutoff ki ai)
      (fun j => upperJointPrefactor ((endpointMeanRate ki ai j : ℝ)/100) a k*
        (endpointDecayQ (endpointMeanRate ki ai j) j : ℝ)) (endpointDecayQ 90 8000) := by
  unfold endpointMeanEnvelope entropyGridBoundReal
  have hs : (∑j∈Finset.Ico (endpointMeanCutoff ki ai) 8000,
      endpointMeanEnvelopeCoeff ki ai j*upperJointPrefactor ((endpointMeanRate ki ai j : ℝ)/100) a k)=
      ∑j∈Finset.Ico (endpointMeanCutoff ki ai) 8000,
        (entropyGridKernelQ (endpointMeanCutoff ki ai) j : ℝ)*
          (upperJointPrefactor ((endpointMeanRate ki ai j : ℝ)/100) a k*
            (endpointDecayQ (endpointMeanRate ki ai j) j : ℝ))/200 := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [endpointMeanEnvelopeCoeff]
    ring
  rw [hs]
  ring

theorem endpointMeanEnvelopeCoeff_nonneg (h : EndpointMeanCertificateConditions)
    (ki : Fin 60) (ai : Fin 42) (hact : endpointMeanActive ki ai)
    {j : ℕ} (hj : j∈Finset.Ico (endpointMeanCutoff ki ai) 8000) :
    0≤endpointMeanEnvelopeCoeff ki ai j := by
  have hc := h.jointCutoff ki ai hact
  have h0 := h.gridLogs (endpointMeanCutoff ki ai) (by simp only [Finset.mem_Icc]; omega)
  have hj' := h.gridLogs (j+1) (by simp only [Finset.mem_Icc]; have := Finset.mem_Ico.mp hj; omega)
  have hK : (0 : ℝ)≤entropyGridKernelQ (endpointMeanCutoff ki ai) j := by
    exact_mod_cast entropyGridKernel_nonneg hc.1 (Finset.mem_Ico.mp hj).1 h0
      (by simpa only [Nat.cast_add,Nat.cast_one] using hj')
  have hr := h.jointRates ki ai hact j hj
  have hd := (h.decays _ (Finset.mem_Icc.mpr ⟨hr.1,hr.2.1⟩)).sound
    (j := j) (by have := Finset.mem_Ico.mp hj; omega)
  have hD : (0 : ℝ)≤endpointDecayQ (endpointMeanRate ki ai j) j := (Real.exp_nonneg _).trans hd
  unfold endpointMeanEnvelopeCoeff
  positivity

theorem endpointMeanEnvelope_convex (h : EndpointMeanCertificateConditions)
    (ki : Fin 60) (ai : Fin 42) (hact : endpointMeanActive ki ai) :
    (∀k∈Icc ((endpointMeanBox ki ai).bottom : ℝ) (endpointMeanBox ki ai).top,
      ConvexOn ℝ (Icc ((endpointMeanBox ki ai).left : ℝ) (endpointMeanBox ki ai).right)
        (fun a => endpointMeanEnvelope ki ai a k)) ∧
    (∀a∈Icc ((endpointMeanBox ki ai).left : ℝ) (endpointMeanBox ki ai).right,
      ConvexOn ℝ (Icc ((endpointMeanBox ki ai).bottom : ℝ) (endpointMeanBox ki ai).top)
        (fun k => endpointMeanEnvelope ki ai a k)) := by
  have hb := h.jointBoxes ki ai hact
  constructor
  · intro k hk
    exact finite_weighted_sum_convex (fun j hj => endpointMeanEnvelopeCoeff_nonneg h ki ai hact hj)
      (fun j hj => upperJointPrefactor_convex_third _ _ _ _)
  · intro a ha
    apply finite_weighted_sum_convex (fun j hj => endpointMeanEnvelopeCoeff_nonneg h ki ai hact hj)
    intro j hj
    have hr := h.jointRates ki ai hact j hj
    have hq : (0 : ℝ)≤(endpointMeanRate ki ai j : ℝ)/100 := by positivity
    have ha0 : 0≤a := (by exact_mod_cast hb.1 : (0 : ℝ)≤(endpointMeanBox ki ai).left).trans ha.1
    have hkl : (0 : ℝ)<(endpointMeanBox ki ai).bottom := by exact_mod_cast hb.2.1
    have hg : ((endpointMeanRate ki ai j : ℝ)/100)*((endpointMeanBox ki ai).top : ℝ)^2<1 := by
      have hh : ((((endpointMeanRate ki ai j : ℚ)/100)*(endpointMeanBox ki ai).top^2 : ℚ) : ℝ)<(1 : ℝ) := by
        exact_mod_cast hr.2.2.1
      simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_pow] using hh
    exact upperJointPrefactor_convex_shape hq ha0 hkl hg

theorem endpointMeanEnvelope_corner (h : EndpointMeanCertificateConditions)
    (ki : Fin 60) (ai : Fin 42) (hact : endpointMeanActive ki ai) (v : Fin 4) :
    endpointMeanEnvelope ki ai (endpointMeanCornerA ki ai v) (endpointMeanCornerK ki ai v)≤
      (endpointMeanCorner ki ai v : ℝ) := by
  have hs : endpointMeanEnvelope ki ai (endpointMeanCornerA ki ai v) (endpointMeanCornerK ki ai v)≤
      (endpointMeanNumericCorner ki ai v : ℝ) := by
    unfold endpointMeanEnvelope endpointMeanNumericCorner entropyGridBoundQ
    push_cast
    have hh : (∑j∈Finset.Ico (endpointMeanCutoff ki ai) 8000,
      endpointMeanEnvelopeCoeff ki ai j*upperJointPrefactor ((endpointMeanRate ki ai j : ℝ)/100)
        (endpointMeanCornerA ki ai v) (endpointMeanCornerK ki ai v))≤
      ∑j∈Finset.Ico (endpointMeanCutoff ki ai) 8000,
        (entropyGridKernelQ (endpointMeanCutoff ki ai) j : ℝ)*
          ((endpointJointPrefactorQ (endpointMeanCornerK ki ai v) (endpointMeanCornerA ki ai v)
            ((endpointMeanRate ki ai j : ℚ)/100) : ℝ)*(endpointDecayQ (endpointMeanRate ki ai j) j : ℝ))/200 := by
      apply Finset.sum_le_sum
      intro j hj
      have hp := (h.jointPrefactors ki ai hact v j hj).sound
      norm_num only [Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat] at hp
      have ht := mul_le_mul_of_nonneg_left hp (endpointMeanEnvelopeCoeff_nonneg h ki ai hact hj)
      convert! ht using 1 <;> unfold endpointMeanEnvelopeCoeff <;> ring
    linarith
  have hn : (endpointMeanNumericCorner ki ai v : ℝ)≤(endpointMeanCorner ki ai v : ℝ) := by
    exact_mod_cast h.jointCorners ki ai hact v
  exact hs.trans hn

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
