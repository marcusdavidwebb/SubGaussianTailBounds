import SingularValueBounds.KL.Upper.ExactTails
open MeasureTheory ProbabilityTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The first-factor logarithmic excess, used also for rates above two. -/
def upperFactorF (q x : ℝ) : ℝ :=
  Real.log (1+x)-Real.log (1-(q-1)*x)-q*x

theorem upperFactorF_hasDerivAt {q x : ℝ} (hx : 0 ≤ x) (hd : (q-1)*x < 1) :
    HasDerivAt (upperFactorF q)
      (q*x*((q-2)+(q-1)*x)/((1+x)*(1-(q-1)*x))) x := by
  have h1 : 1+x ≠ 0 := by linarith
  have h2 : 1-(q-1)*x ≠ 0 := by linarith
  convert! ((((hasDerivAt_const x (1:ℝ)).add (hasDerivAt_id x)).log h1).sub
    (((hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_id x).const_mul (q-1))).log h2)).sub
      ((hasDerivAt_id x).const_mul q) using 1
  simp only [Pi.add_apply, Pi.sub_apply, id_eq]
  field_simp (disch := nlinarith)
  ring

/-- The first determinant factor keeps its exponential bound past rate one
exactly on the margin domain used in S1.6.1. -/
theorem upper_first_factor_exp_extended {q x : ℝ} (hq : 1 < q) (hx : 0 ≤ x)
    (hm : (q-1)*x ≤ 2-q) :
    Real.exp (-q*x) ≤ (1-(q-1)*x)/(1+x) := by
  have hd : (q-1)*x < 1 := by linarith
  have hmono : AntitoneOn (upperFactorF q) (Set.Icc 0 x) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro t ht
      exact (upperFactorF_hasDerivAt ht.1 (by nlinarith [ht.2])).continuousAt.continuousWithinAt
    · intro t ht
      exact (upperFactorF_hasDerivAt (interior_subset ht).1
        (by nlinarith [(interior_subset ht).2])).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(upperFactorF_hasDerivAt (interior_subset ht).1
        (by nlinarith [(interior_subset ht).2])).deriv]
      apply div_nonpos_of_nonpos_of_nonneg
      · apply mul_nonpos_of_nonneg_of_nonpos
        · exact mul_nonneg (by linarith) (interior_subset ht).1
        · nlinarith [(interior_subset ht).2]
      · have ht0 := (interior_subset ht).1
        have htt := (interior_subset ht).2
        have hdt : 0 ≤ 1-(q-1)*t := by nlinarith
        positivity
  have hF := hmono ⟨le_rfl,hx⟩ ⟨hx,le_rfl⟩ hx
  have hzero : upperFactorF q 0 = 0 := by simp [upperFactorF]
  rw [hzero] at hF
  unfold upperFactorF at hF
  have hlog : -q*x ≤ Real.log ((1-(q-1)*x)/(1+x)) := by
    rw [Real.log_div (by linarith) (by linarith)]
    linarith
  have he := Real.exp_le_exp.2 hlog
  rwa [Real.exp_log (div_pos (by linarith) (by linarith))] at he

/-- Shape determinant bound from admissible first factors and rescaled second
factors. It is common to the ordinary, margin, and extended-rate arguments. -/
theorem upper_tail_spectral_shape_of_factors {r : ι → ℝ} (hr : ∀ i,0 < r i)
    {h q q0 s : ℝ} (hh : 0 ≤ h) (hq : 0 < q) (hq0 : 0 < q0)
    (hs : 0 < s) (hps : ∀ i,upperTailWeight r h i ≤ s) (hqs : q0*s < 1)
    (hden : ∀ i,0 < 1-(q-1)*h*r i)
    (hfirst : ∀ i,Real.exp (-(q*h*r i)) ≤ (1-(q-1)*h*r i)/(1+h*r i))
    (hrate : ∀ i,q/(1-(q-1)*h*r i) ≤ q0) :
    (∀ i,0 < 1-q*upperTailEigenvalue r h i) ∧
      Real.exp (-(q*h*∑ i,r i))*Real.exp (Real.log (1-q0*s)/s) ≤
        ∏ i,(1-q*upperTailEigenvalue r h i) := by
  let f := fun i => (1-(q-1)*h*r i)/(1+h*r i)
  let v := fun i => (q/(1-(q-1)*h*r i))/q0*upperTailWeight r h i
  obtain ⟨hp,hpsum,_⟩ := upperTailWeight_properties hr hh
  have hv : ∀ i,0 ≤ v i := fun i => mul_nonneg (div_nonneg
    (div_nonneg hq.le (hden i).le) hq0.le) (hp i).le
  have hvp : ∀ i,v i ≤ upperTailWeight r h i := fun i => by
    apply mul_le_of_le_one_left (hp i).le
    exact (div_le_one hq0).2 (hrate i)
  have hvs : ∀ i,v i ≤ s := fun i => (hvp i).trans (hps i)
  have hsum : ∑ i,v i ≤ 1 := by
    calc
      _ ≤ ∑ i,upperTailWeight r h i := Finset.sum_le_sum (fun i _ => hvp i)
      _ = 1 := hpsum
  have hvpos : ∀ i,0 < 1-q0*v i := fun i => by
    have hm := mul_le_mul_of_nonneg_left (hvs i) hq0.le
    linarith
  have hfpos : ∀ i,0 < f i := fun i => (Real.exp_pos _).trans_le (hfirst i)
  have hfac (i : ι) : 1-q*upperTailEigenvalue r h i = f i*(1-q0*v i) := by
    dsimp [upperTailEigenvalue,f,v]
    have hdr : 1+h*r i ≠ 0 := (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh (hr i).le)).ne'
    have hc : q0*(q/(1-(q-1)*h*r i)/q0*upperTailWeight r h i) =
        q/(1-(q-1)*h*r i)*upperTailWeight r h i := by
      rw [← mul_assoc,mul_div_cancel₀ _ hq0.ne']
    rw [hc]
    rw [div_mul_eq_mul_div]
    have hn : (1-(q-1)*h*r i)*(1-q/(1-(q-1)*h*r i)*upperTailWeight r h i) =
        (1-(q-1)*h*r i)-q*upperTailWeight r h i := by
      rw [mul_sub,mul_one,← mul_assoc,mul_div_cancel₀ _ (hden i).ne']
    rw [hn]
    field_simp [hdr]
    ring
  constructor
  · intro i
    rw [hfac]
    exact mul_pos (hfpos i) (hvpos i)
  · simp_rw [hfac]
    rw [Finset.prod_mul_distrib]
    apply mul_le_mul _ (upper_weight_product_shape hv hsum hvs hs hq0.le hqs)
      (Real.exp_pos _).le (Finset.prod_nonneg (fun i _ => (hfpos i).le))
    have hp := Finset.prod_le_prod (s := Finset.univ)
      (fun i _ => (Real.exp_pos (-(q*h*r i))).le) (fun i _ => hfirst i)
    rw [← Real.exp_sum] at hp
    convert! hp using 1
    congr 1
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum]



/-- The argument of the second logarithmic determinant factor. -/
def upperTailSecondArgument (r : ι → ℝ) (h q : ℝ) (i : ι) : ℝ :=
  (q/(1-(q-1)*h*r i))*upperTailWeight r h i

omit [Nonempty ι] in
/-- Exact factorization, independent of the eventual tail rate. -/
theorem upper_tail_factorization {r : ι → ℝ} (hr : ∀ i,0 < r i)
    {h q : ℝ} (hh : 0 ≤ h) (hden : ∀ i,0 < 1-(q-1)*h*r i) (i : ι) :
    1-q*upperTailEigenvalue r h i =
      ((1-(q-1)*h*r i)/(1+h*r i))*(1-upperTailSecondArgument r h q i) := by
  unfold upperTailEigenvalue upperTailSecondArgument
  have hdr : 1+h*r i ≠ 0 :=
    (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh (hr i).le)).ne'
  rw [div_mul_eq_mul_div]
  have hn : (1-(q-1)*h*r i)*(1-q/(1-(q-1)*h*r i)*upperTailWeight r h i) =
      (1-(q-1)*h*r i)-q*upperTailWeight r h i := by
    rw [mul_sub,mul_one,← mul_assoc,mul_div_cancel₀ _ (hden i).ne']
  rw [hn]
  field_simp [hdr]
  ring

omit [Nonempty ι] in
/-- Separate first-factor and second-factor costs add in the log determinant.
This analytic identity is shared by the joint and extended-rate estimates. -/
theorem upper_tail_logdet_of_costs {r : ι → ℝ} (hr : ∀ i,0 < r i)
    {h q C A : ℝ} (hh : 0 ≤ h) (hden : ∀ i,0 < 1-(q-1)*h*r i)
    (hsecond : ∀ i,0 < 1-upperTailSecondArgument r h q i)
    (hfirstcost : (∑ i,upperFactorF q (h*r i)) ≤ C)
    (hsecondcost : -(∑ i,Real.log (1-upperTailSecondArgument r h q i)) ≤ A) :
    (∀ i,0 < 1-q*upperTailEigenvalue r h i) ∧
      -(∑ i,Real.log (1-q*upperTailEigenvalue r h i)) ≤ q*h*(∑ i,r i)+C+A := by
  have hdr (i : ι) : 0 < 1+h*r i :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh (hr i).le)
  have hf (i : ι) : 0 < (1-(q-1)*h*r i)/(1+h*r i) := div_pos (hden i) (hdr i)
  constructor
  · intro i
    rw [upper_tail_factorization hr hh hden]
    exact mul_pos (hf i) (hsecond i)
  · have he (i : ι) : Real.log (1-q*upperTailEigenvalue r h i) =
        -(q*h*r i)-upperFactorF q (h*r i)+Real.log (1-upperTailSecondArgument r h q i) := by
      rw [upper_tail_factorization hr hh hden,Real.log_mul (hf i).ne' (hsecond i).ne',
        Real.log_div (hden i).ne' (hdr i).ne']
      unfold upperFactorF
      simp only [mul_assoc]
      ring
    simp_rw [he]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_neg_distrib,
      ← Finset.mul_sum]
    linarith

/-- The spectral-shape estimate for just the second determinant factors. -/
theorem upper_tail_second_cost_shape {r : ι → ℝ} (hr : ∀ i,0 < r i)
    {h q v s : ℝ} (hh : 0 ≤ h) (hq : 0 < q) (hv : 0 < v) (hs : 0 < s)
    (hvs : v*s < 1) (hps : ∀ i,upperTailWeight r h i ≤ s)
    (hden : ∀ i,0 < 1-(q-1)*h*r i)
    (hrate : ∀ i,q/(1-(q-1)*h*r i) ≤ v) :
    (∀ i,0 < 1-upperTailSecondArgument r h q i) ∧
      -(∑ i,Real.log (1-upperTailSecondArgument r h q i)) ≤ -Real.log (1-v*s)/s := by
  let w := fun i => upperTailSecondArgument r h q i/v
  obtain ⟨hp,hpsum,_⟩ := upperTailWeight_properties hr hh
  have hw : ∀ i,0 ≤ w i := fun i => div_nonneg (mul_nonneg
    (div_nonneg hq.le (hden i).le) (hp i).le) hv.le
  have hwp : ∀ i,w i ≤ upperTailWeight r h i := fun i => by
    apply (div_le_iff₀ hv).2
    exact (mul_le_mul_of_nonneg_right (hrate i) (hp i).le).trans_eq (mul_comm _ _)
  have hws : ∀ i,w i ≤ s := fun i => (hwp i).trans (hps i)
  have hsum : (∑ i,w i) ≤ 1 := by
    calc
      _ ≤ ∑ i,upperTailWeight r h i := Finset.sum_le_sum (fun i _ => hwp i)
      _ = 1 := hpsum
  have he (i : ι) : v*w i = upperTailSecondArgument r h q i := mul_div_cancel₀ _ hv.ne'
  have hpos : ∀ i,0 < 1-upperTailSecondArgument r h q i := fun i => by
    have hm := mul_le_mul_of_nonneg_left (hws i) hv.le
    rw [he] at hm
    linarith
  have hp := upper_weight_product_shape hw hsum hws hs hv.le hvs
  simp_rw [he] at hp
  have hl := Real.log_le_log (Real.exp_pos _) hp
  rw [Real.log_exp,Real.log_prod (fun i _ => (hpos i).ne')] at hl
  refine ⟨hpos,?_⟩
  rw [neg_div]
  linarith

/-- The elementary rate rescaling with the exact cap margin. -/
theorem upper_margin_rescaling {v theta H : ℝ} (hv : 0 < v) (hv2 : v ≤ 2)
    (htheta : 1 ≤ theta) (hH : 0 ≤ H) (hmargin : H*(v-1) ≤ theta-1) :
    let q := v/theta
    0 < 1-(q-1)*H ∧ q/(1-(q-1)*H) ≤ v ∧
      Real.exp (-q*H) ≤ (1-(q-1)*H)/(1+H) := by
  let q := v/theta
  have ht0 : 0 < theta := by linarith
  have hq : 0 < q := div_pos hv ht0
  have hqtheta : q*theta = v := div_mul_cancel₀ v ht0.ne'
  have hqv : q ≤ v := div_le_self hv.le htheta
  by_cases hq1 : q ≤ 1
  · have hd : 1 ≤ 1-(q-1)*H := by nlinarith
    refine ⟨by linarith,?_,?_⟩
    · exact (div_le_self hq.le hd).trans hqv
    · have he := upper_first_factor_exp_rate (r := (1:ℝ)) zero_lt_one hH hq.le hq1
      convert! he using 1 <;> dsimp [q] <;> ring
  · have hq1 : 1 < q := lt_of_not_ge hq1
    have hv1 : 1 < v := hq1.trans_le hqv
    have hm : (q-1)*H ≤ (theta-1)/theta := by
      apply (le_div_iff₀ ht0).2
      have hrel : (q-1)*H*theta = (v-theta)*H := by
        calc
          _ = (q*theta-theta)*H := by ring
          _ = _ := by rw [hqtheta]
      rw [hrel]
      have hmul := mul_le_mul_of_nonneg_right (show v-theta ≤ v-1 by linarith) hH
      exact hmul.trans (by simpa only [mul_comm] using hmargin)
    have hfrac : (theta-1)/theta < 1 := (div_lt_one ht0).2 (by linarith)
    have hd : 0 < 1-(q-1)*H := by linarith
    have hrate : q/(1-(q-1)*H) ≤ v := by
      apply (div_le_iff₀ hd).2
      have hmul := mul_le_mul_of_nonneg_left hm hv.le
      have he : v*((theta-1)/theta) = v-q := by dsimp [q];field_simp [ht0.ne']
      rw [he] at hmul
      linarith
    have hid : theta*((2-q)*(v-1)-(theta-1)*(q-1)) =
        (v-1)*(2-v)+(theta-1)*(theta+v-2) := by
      dsimp [q]
      field_simp [ht0.ne']
      ring
    have hn : 0 ≤ (2-q)*(v-1)-(theta-1)*(q-1) := by
      have h1 := mul_nonneg (show 0 ≤ v-1 by linarith) (show 0 ≤ 2-v by linarith)
      have h2 := mul_nonneg (show 0 ≤ theta-1 by linarith) (show 0 ≤ theta+v-2 by linarith)
      nlinarith
    have hm2 : (q-1)*H ≤ 2-q := by
      have hmul := mul_le_mul_of_nonneg_right hmargin (show 0 ≤ q-1 by linarith)
      apply (mul_le_mul_iff_left₀ (show 0 < v-1 by linarith)).1
      nlinarith
    exact ⟨hd,hrate,upper_first_factor_exp_extended hq1 hH hm2⟩

/-- The complete margin determinant comparison. The shape controls the
second factors and the cap margin controls the first factors. -/
theorem upper_tail_spectral_margin {r : ι → ℝ} (hr : ∀ i,0 < r i)
    {h v theta s : ℝ} (hh : 0 ≤ h) (hv : 0 < v) (hv2 : v ≤ 2)
    (htheta : 1 ≤ theta) (hs : 0 < s)
    (hps : ∀ i,upperTailWeight r h i ≤ s) (hvs : v*s < 1)
    (hmargin : ∀ i,h*r i*(v-1) ≤ theta-1) :
    (∀ i,0 < 1-(v/theta)*upperTailEigenvalue r h i) ∧
      Real.exp (-((v/theta)*h*∑ i,r i))*Real.exp (Real.log (1-v*s)/s) ≤
        ∏ i,(1-(v/theta)*upperTailEigenvalue r h i) := by
  have ht0 : 0 < theta := by linarith
  have hprops (i : ι) := upper_margin_rescaling hv hv2 htheta (mul_nonneg hh (hr i).le) (hmargin i)
  apply upper_tail_spectral_shape_of_factors hr hh (div_pos hv ht0) hv hs hps hvs
  · intro i
    simpa only [mul_assoc] using (hprops i).1
  · intro i
    convert! (hprops i).2.2 using 1 <;> ring
  · intro i
    simpa only [mul_assoc] using (hprops i).2.1

/-- The normalized spectral shape implies the time-dependent weight bound. -/
theorem upperTailWeight_le_normalized {r : ι → ℝ} (hr : ∀ i,0 < r i)
    {h eta k : ℝ} (hh : 0 ≤ h) (heta : 0 < eta)
    (hnorm : eta^2 = ∑ i,r i^2) (hmax : ∀ i,r i ≤ k*eta) (i : ι) :
    upperTailWeight r h i ≤ k^2 := by
  have ht := upperTailWeight_le_shape hr hh hmax i
  rw [← hnorm] at ht
  have he : (k*eta)^2/eta^2 = k^2 := by field_simp [heta.ne']
  rwa [he] at ht

variable [DecidableEq ι]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Margin-sensitive tail with its finite spectral margin written explicitly. -/
theorem upperShift_tail_margin_of_spectrum {X : Ω → ι → ℝ} {K b v k eta u : ℝ}
    (hsg : SubGaussianMGF μ X K) (hm : Measurable X) (hK : 0 < K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hcap : K^2*Matrix.trace R ≤ b) (hb : b < 1)
    (hv : 0 < v) (hv2 : v ≤ 2) (hk : 0 < k) (hvk : v*k^2 < 1)
    (heta : 0 < eta) (hnorm : eta^2 = ∑ i,hR.isHermitian.eigenvalues i^2)
    (hmax : ∀ i,hR.isHermitian.eigenvalues i ≤ k*eta) (hu : 0 ≤ u)
    (hmargin : ∀ i,u*hR.isHermitian.eigenvalues i*(v-1) ≤ b-K^2*Matrix.trace R) :
    μ.real {ω | u < (1-b)*upperShift R hR (X ω)} ≤
      Real.exp (-Real.log (1-v*k^2)/(2*k^2)-v*u/(2*K^2)) := by
  have hK2 : 0 < K^2 := sq_pos_of_pos hK
  have hb0 : 0 < 1-b := by linarith
  have hcap1 : 0 < 1-K^2*Matrix.trace R := by linarith
  rcases hu.eq_or_lt with rfl | hu
  · have hlog : Real.log (1-v*k^2) ≤ 0 :=
      Real.log_nonpos (by linarith) (by nlinarith [mul_nonneg hv.le (sq_nonneg k)])
    have he : 1 ≤ Real.exp (-Real.log (1-v*k^2)/(2*k^2)) :=
      Real.one_le_exp_iff.2 (div_nonneg (by linarith) (by positivity))
    simpa using (measureReal_le_one (μ := μ)).trans he
  let h := u/(1-b)
  let theta := (1-K^2*Matrix.trace R)/(1-b)
  have hh : 0 < h := div_pos hu hb0
  have ht0 : 0 < theta := div_pos hcap1 hb0
  have ht1 : 1 ≤ theta := (one_le_div hb0).2 (by linarith)
  have hmarg (i : ι) : h*hR.isHermitian.eigenvalues i*(v-1) ≤ theta-1 := by
    have ht := div_le_div_of_nonneg_right (hmargin i) hb0.le
    convert! ht using 1 <;> dsimp [h,theta] <;> field_simp [hb0.ne'] <;> ring
  obtain ⟨hgap,hdet⟩ := upper_tail_spectral_margin hR.eigenvalues_pos hh.le hv hv2 ht1
    (sq_pos_of_pos hk) (upperTailWeight_le_normalized hR.eigenvalues_pos hh.le heta hnorm hmax) hvk hmarg
  have hl := Real.log_le_log (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hdet
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp,
    Real.log_prod (fun i _ => (hgap i).ne')] at hl
  have hlog : -(∑ i,Real.log (1-(v/theta)*upperTailEigenvalue hR.isHermitian.eigenvalues h i)) ≤
      (v/theta)*h*Matrix.trace R-Real.log (1-v*k^2)/k^2 := by
    rw [real_spectral_trace hR.isHermitian]
    linarith
  have ht := upperShift_tail_of_spectral_logdet hsg hm hK hR hh (div_pos hv ht0) hgap hlog
  have hevent : {ω | u < (1-b)*upperShift R hR (X ω)} =
      {ω | h < upperShift R hR (X ω)} := by
    ext ω
    change u < (1-b)*upperShift R hR (X ω) ↔ u/(1-b) < upperShift R hR (X ω)
    rw [div_lt_iff₀ hb0,mul_comm]
  rw [hevent]
  convert! ht using 1
  congr 1
  dsimp [h,theta]
  field_simp [hb0.ne',hcap1.ne',hK.ne']

/-- Supplementary `eq:app-up-tail-margin`, with all cap and rate restrictions. -/
theorem upperShift_tail_margin {X : Ω → ι → ℝ} {K L w b v k eta u : ℝ}
    (hsg : SubGaussianMGF μ X K) (hm : Measurable X) (hK : 0 < K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hw : 0 ≤ w) (hL : 0 ≤ L)
    (hcap : K^2*Matrix.trace R+w*K^2*L*eta ≤ b) (hb : b < 1)
    (hv : 0 < v) (hv2 : v ≤ 2) (hk : 0 < k) (hvk : v*k^2 < 1)
    (heta : 0 < eta) (hnorm : eta^2 = ∑ i,hR.isHermitian.eigenvalues i^2)
    (hmax : ∀ i,hR.isHermitian.eigenvalues i ≤ k*eta) (hu : 0 ≤ u)
    (hmargin : u*k*(v-1) ≤ w*K^2*L) :
    μ.real {ω | u < (1-b)*upperShift R hR (X ω)} ≤
      Real.exp (-Real.log (1-v*k^2)/(2*k^2)-v*u/(2*K^2)) := by
  have hcost : 0 ≤ w*K^2*L*eta := by positivity
  apply upperShift_tail_margin_of_spectrum hsg hm hK hR (by linarith) hb hv hv2 hk hvk heta hnorm hmax hu
  intro i
  by_cases hv1 : 1 ≤ v
  · have hm := mul_le_mul_of_nonneg_right (hmax i) (mul_nonneg hu (sub_nonneg.mpr hv1))
    have hc := mul_le_mul_of_nonneg_right hmargin heta.le
    nlinarith
  · have hprod : u*hR.isHermitian.eigenvalues i*(v-1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hu (hR.eigenvalues_pos i).le) (by linarith)
    linarith

end
end SingularValueBounds.KL
