import SingularValueBounds.KL.Upper.JointTail
import SingularValueBounds.KL.Certificates.Enclosures

/-! # Capped determinant weights for the endpoint MGF (S1.6.4)

The cap is the printed `225/256`. A top weight at least `31/256`
uses the finite product bound directly. If every weight is smaller,
the logarithmic chord estimate gives the stronger alternative `e⁻²`.
-/
open scoped BigOperators
open MeasureTheory Set
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem one_sub_sum_le_product (s : Finset ι) {p : ι → ℝ}
    (hp : ∀ i∈s, 0≤p i) (hp1 : ∀ i∈s, p i≤1) :
    1-∑ i∈s,p i ≤ ∏ i∈s,(1-p i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hi0 := hp i (Finset.mem_insert_self _ _)
    have hi1 := hp1 i (Finset.mem_insert_self _ _)
    have hps : ∀ j∈s,0≤p j := fun j hj => hp j (Finset.mem_insert_of_mem hj)
    have hp1s : ∀ j∈s,p j≤1 := fun j hj => hp1 j (Finset.mem_insert_of_mem hj)
    have hh := mul_le_mul_of_nonneg_left (ih hps hp1s) (sub_nonneg.mpr hi1)
    rw [Finset.sum_insert hi,Finset.prod_insert hi]
    have hsum : 0≤∑j∈s,p j := Finset.sum_nonneg hps
    nlinarith [mul_nonneg hi0 hsum]

/-- A normalized vector with one sufficiently large coordinate obeys the
two-weight determinant estimate without any iteration or limiting argument. -/
theorem capped_weight_product_of_large {p : ι → ℝ} {v : ℝ}
    (hp : ∀ i,0≤p i) (hv : 1/2≤v) (hv1 : v<1)
    (hsum : ∑ i,p i=1) (hcap : ∀ i,p i≤v)
    {j : ι} (hj : 1-v≤p j) : v*(1-v)≤∏i,(1-p i) := by
  have hp1 : ∀ i,p i≤1 := fun i => (hcap i).trans hv1.le
  have hs := one_sub_sum_le_product (Finset.univ.erase j)
    (fun i hi => hp i) (fun i hi => hp1 i)
  have hsumErase : ∑ i∈Finset.univ.erase j,p i=1-p j := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j),hsum]
  rw [hsumErase] at hs
  have hprod : (∏i,(1-p i))=(1-p j)*∏i∈Finset.univ.erase j,(1-p i) := by
    exact (Finset.mul_prod_erase Finset.univ (fun i => 1-p i) (Finset.mem_univ j)).symm
  rw [hprod]
  have hh := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr (hp1 j))
  have hjcap := hcap j
  have hsq : 0≤(v-p j)*(p j-(1-v)) := mul_nonneg (sub_nonneg.mpr hjcap) (sub_nonneg.mpr hj)
  nlinarith

/-- The exact endpoint capped-weight prefactor needed by Lemma S1.12. -/
theorem endpoint_capped_weight_log_bound {p : ι → ℝ}
    (hp : ∀ i,0≤p i) (hsum : ∑i,p i=1)
    (hcap : ∀ i,p i≤(225/256 : ℝ)) :
    -(∑i,Real.log (1-p i))≤2*Real.log (46/15 : ℝ) := by
  have hpos : ∀ i,0<1-p i := fun i => by linarith [hcap i]
  by_cases hj : ∃j,(31/256 : ℝ)≤p j
  · obtain ⟨j,hj⟩ := hj
    have hd := capped_weight_product_of_large hp (by norm_num : (1/2 : ℝ)≤225/256)
      (by norm_num : (225/256 : ℝ)<1) hsum hcap (j := j) (by norm_num; exact hj)
    have hh := Real.log_le_log (by norm_num : (0 : ℝ)<(225/256)*(1-225/256)) hd
    rw [Real.log_prod Finset.univ _ (fun i hi => (hpos i).ne')] at hh
    have hn : -(Real.log ((225/256 : ℝ)*(1-225/256)))≤2*Real.log (46/15 : ℝ) := by
      have hnum : 1/((46/15 : ℝ)^2)≤(225/256 : ℝ)*(1-225/256) := by norm_num
      have hlog := Real.log_le_log (by norm_num : (0 : ℝ)<1/((46/15 : ℝ)^2)) hnum
      rw [Real.log_div (by norm_num) (by norm_num),Real.log_one,Real.log_pow] at hlog
      linarith
    linarith
  · have hsmall : ∀ i,p i≤1/2 := by
      intro i
      have hi : ¬(31/256 : ℝ)≤p i := fun h => hj ⟨i,h⟩
      linarith
    have hlog : ∀i,-Real.log (1-p i)≤2*p i := by
      intro i
      have hh := Real.log_le_sub_one_of_pos (one_div_pos.mpr (hpos i))
      rw [Real.log_div (by norm_num) (hpos i).ne',Real.log_one] at hh
      have hdiv : 1/(1-p i)-1≤2*p i := by
        apply (mul_le_mul_right (hpos i)).mp
        field_simp [(hpos i).ne']
        nlinarith [hp i,hsmall i,sq_nonneg (p i)]
      linarith
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i hi => hlog i)
    rw [Finset.sum_neg_distrib,← Finset.mul_sum,hsum,mul_one] at hs
    have he : Real.exp (1 : ℝ)≤(46/15 : ℝ) := by
      have hh := Certificates.exp_le_expTaylorUpper 8 (x := (1 : ℝ)) (by norm_num) (by norm_num)
      norm_num [Certificates.expTaylorUpper,Certificates.expTaylor,Finset.sum_range_succ] at hh ⊢
      linarith
    have hl := Real.log_le_log (Real.exp_pos 1) he
    rw [Real.log_exp] at hl
    linarith

variable [Nonempty ι]

theorem endpoint_capped_spectral_cost {r : ι → ℝ} (hr : ∀i,0<r i)
    {h η : ℝ} (hh : 0≤h) (hη : 0<η) (hnorm : η^2=∑i,r i^2)
    (hmax : ∀i,r i≤(15/16 : ℝ)*η) :
    (∀i,0<1-upperTailEigenvalue r h i) ∧
      -(∑i,Real.log (1-upperTailEigenvalue r h i))≤
        h*(∑i,r i)+2*Real.log (46/15 : ℝ) := by
  have hp := upperTailWeight_properties hr hh
  have hcap : ∀i,upperTailWeight r h i≤(225/256 : ℝ) := by
    intro i
    have hb := upperTailWeight_le_normalized hr hh hη hnorm hmax i
    norm_num at hb ⊢
    exact hb
  have hlog := endpoint_capped_weight_log_bound (fun i => (hp.1 i).le) hp.2.1 hcap
  have hF : (∑i,upperFactorF 1 (h*r i))≤(0 : ℝ) := by
    apply Finset.sum_nonpos
    intro i hi
    have harg : 0<1+h*r i := by have hi := hr i; positivity
    have hl := Real.log_le_sub_one_of_pos harg
    simpa [upperFactorF] using (show Real.log (1+h*r i)-h*r i≤0 by linarith)
  have hcost := upper_tail_logdet_of_costs hr hh
    (q := 1) (C := 0) (A := 2*Real.log (46/15 : ℝ))
    (by intro i; norm_num)
    (by intro i; simp only [upperTailSecondArgument,sub_self,zero_mul,sub_zero,one_div,one_mul];
        linarith [hcap i]) hF
    (by simpa [upperTailSecondArgument] using hlog)
  simpa using hcost

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The low-shape tail for the actual exact upper shift. -/
theorem upperShift_endpoint_low_tail {X : Ω → ι → ℝ} {R : Matrix ι ι ℝ}
    (hsg : SubGaussianMGF μ X 1) (hm : Measurable X) (hR : R.PosDef)
    {b η u : ℝ} (hcap : Matrix.trace R≤b) (hb : b<1)
    (hη : 0<η) (hnorm : η^2=∑i,hR.isHermitian.eigenvalues i^2)
    (hmax : ∀i,hR.isHermitian.eigenvalues i≤(15/16 : ℝ)*η) (hu : 0≤u) :
    μ.real {ω | u<(1-b)*upperShift R hR (X ω)}≤
      (46/15 : ℝ)*Real.exp (-((1/2 : ℝ)*u)) := by
  have hb0 : 0<1-b := by linarith
  by_cases hu0 : u=0
  · subst u
    norm_num
    exact (measureReal_le_one (μ := μ)).trans (by norm_num)
  have huPos : 0<u := lt_of_le_of_ne hu (Ne.symm hu0)
  let h := u/(1-b)
  have hh : 0<h := div_pos huPos hb0
  obtain ⟨hgap,hlog⟩ := endpoint_capped_spectral_cost hR.eigenvalues_pos hh.le hη hnorm hmax
  rw [← real_spectral_trace hR.isHermitian] at hlog
  have ht := upperShift_tail_of_spectral_logdet hsg hm (by norm_num : (0 : ℝ)<1)
    hR hh (q := 1) (by norm_num) (by simpa using hgap) (by simpa using hlog)
  have hevent : {ω | u<(1-b)*upperShift R hR (X ω)}={ω | h<upperShift R hR (X ω)} := by
    ext ω
    change u<(1-b)*upperShift R hR (X ω) ↔ u/(1-b)<upperShift R hR (X ω)
    rw [div_lt_iff₀ hb0,mul_comm]
  rw [hevent]
  norm_num only [one_pow,one_mul,mul_one] at ht
  have hscaled : u≤h*(1-Matrix.trace R) := by
    have he : h*(1-b)=u := by dsimp [h]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hcap hh.le]
  calc
    _ ≤ Real.exp (2*Real.log (46/15 : ℝ)/2-h*(1-Matrix.trace R)/2) := ht
    _ ≤ Real.exp (Real.log (46/15 : ℝ)-u/2) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_sub,Real.exp_log (by norm_num : (0 : ℝ)<46/15),
        div_eq_mul_inv,← Real.exp_neg]; congr 2; ring

end
end SingularValueBounds.KL
