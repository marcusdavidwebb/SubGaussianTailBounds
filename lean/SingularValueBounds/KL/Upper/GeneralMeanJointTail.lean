import SingularValueBounds.KL.Upper.ExtendedTailPieces
import SingularValueBounds.KL.Upper.JointTail

/-! Shaped determinant prefactors for the extended rates used in the general
upper mean. The rate correction and the third spectral moment are both retained. -/
open MeasureTheory ProbabilityTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1400000
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem upper_tail_second_cost_joint {r : ι → ℝ} (hr : ∀ i,0 < r i)
    {h q v k eta : ℝ} (hh : 0 ≤ h) (hq : 0 < q) (hv : 0 < v)
    (hk : 0 < k) (hvk : v*k^2 < 1) (heta : 0 < eta)
    (hnorm : eta^2 = ∑ i,r i^2) (hmax : ∀ i,r i ≤ k*eta)
    (hden : ∀ i,0 < 1-(q-1)*h*r i)
    (hrate : ∀ i,q/(1-(q-1)*h*r i) ≤ v) :
    (∀ i,0 < 1-upperTailSecondArgument r h q i) ∧
    -(∑ i,Real.log (1-upperTailSecondArgument r h q i)) ≤
      upperJointCost v k (∑ i,(r i/eta)^3) := by
  let rho : ι → ℝ := fun i => r i/eta
  have hrho : ∀ i,0 ≤ rho i := fun i => div_nonneg (hr i).le heta.le
  have hs : (∑ i,rho i^2) = 1 := by
    simp only [rho,div_pow,← Finset.sum_div,← hnorm]
    exact div_self (pow_ne_zero 2 heta.ne')
  have hmax' : ∀ i,rho i ≤ k := fun i => (div_le_iff₀ heta).2 (hmax i)
  have harg0 (i : ι) : 0 ≤ upperTailSecondArgument r h q i := by
    dsimp [upperTailSecondArgument]
    exact mul_nonneg (div_nonneg hq.le (hden i).le) ((upperTailWeight_properties hr hh).1 i).le
  have harg (i : ι) : upperTailSecondArgument r h q i ≤ v*normalizedShiftWeight rho (h*eta) i := by
    have hh' := mul_le_mul_of_nonneg_right (hrate i) ((upperTailWeight_properties hr hh).1 i).le
    have hn : normalizedShiftWeight rho (h*eta) i = upperTailWeight r h i :=
      (upperTailWeight_normalize hr hh heta i).symm
    rw [hn]
    simpa only [upperTailSecondArgument,mul_assoc] using hh'
  have hgap (i : ι) : 0 < 1-upperTailSecondArgument r h q i := by
    have hb := normalizedShiftWeight_le_shape hrho hs (mul_nonneg hh heta.le) hk.le hmax' i
    have hm := mul_le_mul_of_nonneg_left hb hv.le
    linarith [harg i]
  refine ⟨hgap,?_⟩
  exact normalizedShiftWeight_log_prefactor_of_le hrho hs (mul_nonneg hh heta.le) hk hmax'
    hv.le hvk harg0 harg

theorem upper_extended_spectral_logdet_joint {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {r : ι → ℝ} (hr : ∀ i,0 < r i) {h eta k v v0 theta C : ℝ}
    (hh : 0 < h) (heta : 0 < eta) (hk : 0 < k)
    (hnorm : eta^2 = ∑ i,r i^2) (hmax : ∀ i,r i ≤ k*eta)
    (hv0 : 1 < v0) (hvv : v0 ≤ v) (hvk : v*k^2 < 1)
    (htheta : 1 < theta) (hthetav : theta < v0) (hC : 0 ≤ C)
    (hmargin : h*eta*k*(v0-1) ≤ theta-1) (hFc : upperRateF v0 theta ≤ C) :
    (∀ i,0 < 1-(v0/theta)*upperTailEigenvalue r h i) ∧
      -(∑ i,Real.log (1-(v0/theta)*upperTailEigenvalue r h i)) ≤
        (v0/theta)*h*(∑ i,r i)+C/k^2+upperJointCost v k (∑ i,(r i/eta)^3) := by
  let q := v0/theta
  let x0 := (theta-1)/(v0-1)
  have ht0 : 0 < theta := by linarith
  have hv01 : 0 < v0-1 := by linarith
  have hq : 1 < q := (one_lt_div ht0).2 hthetav
  have hx0 : 0 < x0 := div_pos (by linarith) hv01
  have hnormmargin : h*eta*k ≤ x0 := (le_div_iff₀ hv01).2 hmargin
  have hx (i : ι) : 0 ≤ h*r i := mul_nonneg hh.le (hr i).le
  have hxi (i : ι) : h*r i ≤ x0 := by
    have hi := mul_le_mul_of_nonneg_left (hmax i) hh.le
    nlinarith
  have hendpoint := upper_rate_rescaling_denominator hv0 htheta.le hx0.le
    (show x0*(v0-1) ≤ theta-1 by dsimp [x0];rw [div_mul_cancel₀ _ hv01.ne'])
  have hd : (q-1)*x0 < 1 := by have he := hendpoint.1;change 0 < 1-(q-1)*x0 at he;linarith
  have hden (i : ι) : 0 < 1-(q-1)*h*r i := by nlinarith [hxi i]
  have hrate (i : ι) : q/(1-(q-1)*h*r i) ≤ v := by
    have hm : h*r i*(v0-1) ≤ theta-1 :=
      (mul_le_mul_of_nonneg_right (hxi i) hv01.le).trans_eq
        (div_mul_cancel₀ _ hv01.ne')
    have hh := (upper_rate_rescaling_denominator hv0 htheta.le (hx i) hm).2
    have hh' : q/(1-(q-1)*h*r i) ≤ v0 := by simpa only [mul_assoc] using hh
    exact hh'.trans hvv
  have hxsq : (∑ i,(h*r i)^2) ≤ x0^2/k^2 := by
    have hs : h*eta*k ≤ x0 := hnormmargin
    have hs0 : 0 ≤ h*eta*k := by positivity
    have hs2 : (h*eta*k)^2 ≤ x0^2 := by nlinarith
    apply (le_div_iff₀ (sq_pos_of_pos hk)).2
    simp only [mul_pow,← Finset.mul_sum,← hnorm]
    nlinarith
  have hF := upperFactorF_sum_bound hq hx0 hk hd (fun i => h*r i) hx hxi hxsq
  have hidentity : upperFactorF q x0 = upperRateF v0 theta :=
    upperFactorF_rate_identity hv0 htheta.le
  rw [hidentity] at hF
  have hmaxC : max 0 (upperRateF v0 theta) ≤ C := max_le hC hFc
  have hfirstcost : (∑ i,upperFactorF q (h*r i)) ≤ C/k^2 :=
    hF.trans (div_le_div_of_nonneg_right hmaxC (sq_nonneg k))
  obtain ⟨hsecond,hsecondcost⟩ := upper_tail_second_cost_joint hr hh.le (by linarith : 0 < q)
    (by linarith : 0 < v) hk hvk heta hnorm hmax hden hrate
  have ht := upper_tail_logdet_of_costs hr hh.le hden hsecond hfirstcost hsecondcost
  convert! ht using 1 <;> dsimp [q] <;> ring

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem upperShift_tail_extended_joint {X : Ω → ι → ℝ} {K L w b v v0 C k eta u : ℝ}
    (hsg : SubGaussianMGF μ X K) (hm : Measurable X) (hK : 0 < K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hw : 0 ≤ w) (hL : 0 ≤ L)
    (hcap : K^2*Matrix.trace R+w*K^2*L*eta ≤ b) (hb : b < 1)
    (hv0 : 1 < v0) (hvv : v0 ≤ v) (hk : 0 < k) (hvk : v*k^2 < 1) (hC : 0 ≤ C)
    (hbound : ∀ theta ∈ Icc (1:ℝ) v,upperRateF v theta ≤ C)
    (heta : 0 < eta) (hnorm : eta^2 = ∑ i,hR.isHermitian.eigenvalues i^2)
    (hmax : ∀ i,hR.isHermitian.eigenvalues i ≤ k*eta) (hu : 0 ≤ u)
    (hmargin : u*k*(v0-1) ≤ w*K^2*L) :
    μ.real {ω | u < (1-b)*upperShift R hR (X ω)} ≤
      Real.exp ((C/k^2+upperJointCost v k (∑ i,(hR.isHermitian.eigenvalues i/eta)^3))/2-v0*u/(2*K^2)) := by
  have hK2 : 0 < K^2 := sq_pos_of_pos hK
  have hv : 0 < v := by linarith
  have hb0 : 0 < 1-b := by linarith
  have hcost : 0 ≤ w*K^2*L*eta := by positivity
  have hcap0 : K^2*Matrix.trace R ≤ b := by linarith
  have hcap1 : 0 < 1-K^2*Matrix.trace R := by linarith
  rcases hu.eq_or_lt with rfl | hu
  · have hJ : 0 ≤ upperJointCost v k (∑ i,(hR.isHermitian.eigenvalues i/eta)^3) :=
      upperJointCost_nonneg hv.le hk
        (Finset.sum_nonneg fun i _ => pow_nonneg (div_nonneg (hR.eigenvalues_pos i).le heta.le) 3) hvk
    have he : 1 ≤ Real.exp ((C/k^2+upperJointCost v k (∑ i,(hR.isHermitian.eigenvalues i/eta)^3))/2) :=
      Real.one_le_exp_iff.2 (div_nonneg (add_nonneg (div_nonneg hC (sq_nonneg k)) hJ) (by norm_num))
    simpa using (measureReal_le_one (μ := μ)).trans he
  let r := hR.isHermitian.eigenvalues
  let h := u/(1-b)
  let theta := (1-K^2*Matrix.trace R)/(1-b)
  let q := v0/theta
  have hr : ∀ i,0 < r i := hR.eigenvalues_pos
  have hh : 0 < h := div_pos hu hb0
  have ht0 : 0 < theta := div_pos hcap1 hb0
  have ht1 : 1 ≤ theta := (one_le_div hb0).2 (by linarith)
  have hq : 0 < q := div_pos (by linarith) ht0
  have hnormmargin : h*eta*k*(v0-1) ≤ theta-1 := by
    have hm := mul_le_mul_of_nonneg_right hmargin heta.le
    have hm0 : u*eta*k*(v0-1) ≤ b-K^2*Matrix.trace R := by nlinarith
    have ht := div_le_div_of_nonneg_right hm0 hb0.le
    convert! ht using 1 <;> dsimp [h,theta] <;> field_simp [hb0.ne'] <;> ring
  have hps := upperTailWeight_le_normalized hr hh.le heta hnorm hmax
  have hspec : (∀ i,0 < 1-q*upperTailEigenvalue r h i) ∧
      -(∑ i,Real.log (1-q*upperTailEigenvalue r h i)) ≤
        q*h*(∑ i,r i)+C/k^2+upperJointCost v k (∑ i,(r i/eta)^3) := by
    by_cases hq1 : q ≤ 1
    · have hden (i : ι) : 0 < 1-(q-1)*h*r i := by
        have hnon := mul_nonpos_of_nonpos_of_nonneg (show q-1 ≤ 0 by linarith)
          (mul_nonneg hh.le (hr i).le)
        nlinarith
      have hfirst (i : ι) : Real.exp (-(q*h*r i)) ≤ (1-(q-1)*h*r i)/(1+h*r i) := by
        have he := upper_first_factor_exp_rate (hr i) hh.le hq.le hq1
        convert! he using 1 <;> ring
      have hrate (i : ι) : q/(1-(q-1)*h*r i) ≤ v := by
        have hd : 1 ≤ 1-(q-1)*h*r i := by
          have hnon := mul_nonpos_of_nonpos_of_nonneg (show q-1 ≤ 0 by linarith)
            (mul_nonneg hh.le (hr i).le)
          nlinarith
        have hqv0 : q ≤ v0 := div_le_self (by linarith) ht1
        exact (div_le_self hq.le hd).trans (hqv0.trans hvv)
      obtain ⟨hsecond,hsecondcost⟩ := upper_tail_second_cost_joint hr hh.le hq hv hk hvk
        heta hnorm hmax hden hrate
      have hfirstcost : (∑ i,upperFactorF q (h*r i)) ≤ (0:ℝ) := by
        apply Finset.sum_nonpos
        intro i _
        have hl := Real.log_le_log (Real.exp_pos _) (hfirst i)
        rw [Real.log_exp,Real.log_div (hden i).ne'
          (ne_of_gt (show 0 < 1+h*r i by have hi := hr i; positivity))] at hl
        dsimp [upperFactorF]
        simp only [mul_assoc] at hl ⊢
        nlinarith
      have ht := upper_tail_logdet_of_costs hr hh.le hden hsecond hfirstcost hsecondcost
      refine ⟨ht.1,?_⟩
      have hCf : 0 ≤ C/k^2 := div_nonneg hC (sq_nonneg k)
      linarith [ht.2]
    · have hq1 : 1 < q := lt_of_not_ge hq1
      have htheta : 1 < theta := by
        have hpos : 0 < h*eta*k*(v0-1) :=
          mul_pos (mul_pos (mul_pos hh heta) hk) (by linarith)
        linarith
      have hthetav : theta < v0 := (one_lt_div ht0).1 hq1
      have hFc := upperRateF_envelope hv0 hvv hbound ⟨ht1,hthetav.le⟩
      exact upper_extended_spectral_logdet_joint hr hh heta hk hnorm hmax hv0 hvv hvk
        htheta hthetav hC hnormmargin hFc
  have hlog : -(∑ i,Real.log (1-q*upperTailEigenvalue hR.isHermitian.eigenvalues h i)) ≤
      q*h*Matrix.trace R+(C/k^2+upperJointCost v k (∑ i,(r i/eta)^3)) := by
    rw [real_spectral_trace hR.isHermitian]
    exact (by convert! hspec.2 using 1 <;> ring)
  have ht := upperShift_tail_of_spectral_logdet hsg hm hK hR hh hq hspec.1 hlog
  have hevent : {ω | u < (1-b)*upperShift R hR (X ω)} =
      {ω | h < upperShift R hR (X ω)} := by
    ext ω
    change u < (1-b)*upperShift R hR (X ω) ↔ u/(1-b) < upperShift R hR (X ω)
    rw [div_lt_iff₀ hb0,mul_comm]
  rw [hevent]
  convert! ht using 1
  congr 1
  dsimp [q,h,theta]
  field_simp [hb0.ne',hcap1.ne',hK.ne']
  ring

def extendedJointPrefactor (v k C a : ℝ) : ℝ :=
  Real.exp ((C/k^2+upperJointCost v k a)/2)

def ExtendedJointUpperTailPieces (tail : ℝ → ℝ) (K L w k v C a : ℝ) : Prop :=
  (∀ u,0 ≤ u → u ≤ extendedTailCutoff w k v*K^2*L →
    tail u ≤ extendedJointPrefactor v k C a*Real.exp (-v*u/(2*K^2))) ∧
  (∀ u,extendedTailCutoff w k v*K^2*L < u →
    tail u ≤ extendedJointPrefactor v k C a*
      Real.exp (-u/(2*K^2)-extendedTailCutoff w k v*(v-1)*L/2))

theorem upperShift_tail_extended_joint_two_pieces {X : Ω → ι → ℝ}
    {K L w b v C k eta : ℝ} (hsg : SubGaussianMGF μ X K)
    (hm : Measurable X) (hK : 0 < K) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (hw : 0 < w) (hL : 0 < L)
    (hcap : K^2*Matrix.trace R+w*K^2*L*eta ≤ b) (hb : b < 1)
    (hv : 1 < v) (hk : 0 < k) (hvk : v*k^2 < 1) (hC : 0 ≤ C)
    (hbound : ∀ theta ∈ Icc (1:ℝ) v,upperRateF v theta ≤ C)
    (heta : 0 < eta) (hnorm : eta^2 = ∑ i,hR.isHermitian.eigenvalues i^2)
    (hmax : ∀ i,hR.isHermitian.eigenvalues i ≤ k*eta) :
    ExtendedJointUpperTailPieces
      (fun u => μ.real {ω | u < (1-b)*upperShift R hR (X ω)})
      K L w k v C (∑ i,(hR.isHermitian.eigenvalues i/eta)^3) := by
  let a := ∑ i,(hR.isHermitian.eigenvalues i/eta)^3
  let Ce := C+k^2*upperJointCost v k a+Real.log (1-v*k^2)
  have he : -Real.log (1-v*k^2)/(2*k^2)+Ce/(2*k^2) =
      (C/k^2+upperJointCost v k a)/2 := by
    dsimp [Ce]
    field_simp [hk.ne']
    <;> ring
  have hbase : ∀ rate threshold,1 < rate → rate ≤ v → 0 ≤ threshold →
      threshold*k*(rate-1) ≤ w*K^2*L →
      μ.real {ω | threshold < (1-b)*upperShift R hR (X ω)} ≤
        Real.exp (-Real.log (1-v*k^2)/(2*k^2)+Ce/(2*k^2)-rate*threshold/(2*K^2)) := by
    intro rate threshold hr hrv ht hmargin
    rw [he]
    exact upperShift_tail_extended_joint hsg hm hK hR hw.le hL.le hcap hb hr hrv hk hvk
      hC hbound heta hnorm hmax ht hmargin
  have hpref : extendedTailPrefactor v k Ce = extendedJointPrefactor v k C a := by
    unfold extendedTailPrefactor extendedJointPrefactor
    rw [he]
  constructor
  · intro u hu hcut
    rw [← hpref]
    exact upper_extended_two_piece_low hK hL hw hk hv hbase hu hcut
  · intro u hcut
    rw [← hpref]
    exact upper_extended_two_piece_high hK hL hw hk hv hbase hcut

end
end SingularValueBounds.KL
