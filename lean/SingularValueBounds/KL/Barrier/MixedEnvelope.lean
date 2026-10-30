import SingularValueBounds.KL.Barrier.MixedGeometry

/-! The exclude-largest-eigenvalue Cauchy--Schwarz envelope in supplementary
Lemma S1.6. All norms are the explicit Euclidean spectral norms. -/
open Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1800000

def mixedShapeEnvelope (n : ℕ) (x : ℝ) : ℝ :=
  1/((n:ℝ)*x)+Real.sqrt (1-1/(n:ℝ))*Real.sqrt (1-1/((n:ℝ)*x^2))

theorem mixedShapeEnvelope_continuous {n : ℕ} (hn : 0<n) :
    ContinuousOn (mixedShapeEnvelope n) (Icc (1/Real.sqrt n) 1) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hs : 0<Real.sqrt n := Real.sqrt_pos.mpr hn0
  intro x hx
  have hx0 : 0<x := (div_pos zero_lt_one hs).trans_le hx.1
  exact (continuousAt_const.div (continuousAt_const.mul continuousAt_id)
    (mul_ne_zero hn0.ne' hx0.ne')).add
    (continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp
      (continuousAt_const.sub (continuousAt_const.div
        (continuousAt_const.mul (continuousAt_id.pow 2))
        (mul_ne_zero hn0.ne' (pow_ne_zero 2 hx0.ne')))))) |>.continuousWithinAt

theorem mixedShapeEnvelope_base {n : ℕ} (hn : 0<n) :
    mixedShapeEnvelope n (1/Real.sqrt n)=1/Real.sqrt n := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hs : 0<Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hs2 : (Real.sqrt n)^2=(n:ℝ) := Real.sq_sqrt hn0.le
  have harg : 1-1/((n:ℝ)*(1/Real.sqrt n)^2)=0 := by
    field_simp
    nlinarith only [hs2]
  unfold mixedShapeEnvelope
  rw [harg,Real.sqrt_zero,mul_zero,add_zero]
  field_simp
  exact hs2

theorem mixedShapeEnvelope_one {n : ℕ} (hn : 0<n) : mixedShapeEnvelope n 1=1 := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hp : 0≤1-1/(n:ℝ) := sub_nonneg.mpr ((div_le_one (by positivity)).mpr hn1)
  simp only [mixedShapeEnvelope,one_pow,mul_one,Real.mul_self_sqrt hp]
  ring

theorem mixedShapeEnvelope_monotone {n : ℕ} (hn : 0<n) :
    MonotoneOn (mixedShapeEnvelope n) (Icc (1/Real.sqrt n) 1) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hs : 0<Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hs2 : (Real.sqrt n)^2=(n:ℝ) := Real.sq_sqrt hn0.le
  have hp : 0≤1-1/(n:ℝ) := sub_nonneg.mpr ((div_le_one hn0).mpr hn1)
  have hxpos {x : ℝ} (hx : x∈Icc (1/Real.sqrt n) 1) : 0<x :=
    (div_pos zero_lt_one hs).trans_le hx.1
  have hderiv {x : ℝ} (hx0 : 0<x) (hg : 0<1-1/((n:ℝ)*x^2)) :
      HasDerivAt (mixedShapeEnvelope n)
        ((Real.sqrt (1-1/(n:ℝ))-x*Real.sqrt (1-1/((n:ℝ)*x^2)))/
          ((n:ℝ)*x^3*Real.sqrt (1-1/((n:ℝ)*x^2)))) x := by
    have hd := ((hasDerivAt_const x (1:ℝ)).div
      ((hasDerivAt_id x).const_mul (n:ℝ)) (mul_ne_zero hn0.ne' hx0.ne')).add
      ((((hasDerivAt_const x (1:ℝ)).sub
        ((hasDerivAt_const x (1:ℝ)).div
          (((hasDerivAt_id x).pow 2).const_mul (n:ℝ))
          (mul_ne_zero hn0.ne' (pow_ne_zero 2 hx0.ne')))).sqrt hg.ne').const_mul
            (Real.sqrt (1-1/(n:ℝ))))
    change HasDerivAt (mixedShapeEnvelope n) _ x at hd
    convert! hd using 1
    simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,pow_one,zero_mul,sub_zero,one_mul,mul_one,zero_sub]
    generalize Real.sqrt (1-1/(n:ℝ))=c
    generalize hr : Real.sqrt (1-1/((n:ℝ)*x^2))=r
    have hr0 : r≠0 := by rw [←hr];exact (Real.sqrt_pos.mpr hg).ne'
    field_simp [hn0.ne',hx0.ne',hr0]
    <;> ring
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _ )
  · intro x hx
    exact (continuousAt_const.div (continuousAt_const.mul continuousAt_id)
      (mul_ne_zero hn0.ne' (hxpos hx).ne')).add
      (continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp
        (continuousAt_const.sub (continuousAt_const.div
          (continuousAt_const.mul (continuousAt_id.pow 2))
          (mul_ne_zero hn0.ne' (pow_ne_zero 2 (hxpos hx).ne')))))) |>.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0<x := (div_pos zero_lt_one hs).trans hx.1
    have hnx : 1<(n:ℝ)*x^2 := by
      have hh := (div_lt_iff₀ hs).mp hx.1
      nlinarith
    have hg : 0<1-1/((n:ℝ)*x^2) := sub_pos.mpr ((div_lt_one (by positivity)).mpr hnx)
    exact (hderiv hx0 hg).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0<x := (div_pos zero_lt_one hs).trans hx.1
    have hnx : 1<(n:ℝ)*x^2 := by
      have hh := (div_lt_iff₀ hs).mp hx.1
      nlinarith
    have hg : 0<1-1/((n:ℝ)*x^2) := sub_pos.mpr ((div_lt_one (by positivity)).mpr hnx)
    rw [(hderiv hx0 hg).deriv]
    have hroot : x*Real.sqrt (1-1/((n:ℝ)*x^2))≤Real.sqrt (1-1/(n:ℝ)) := by
      have h1 := Real.sq_sqrt hg.le
      have h2 := Real.sq_sqrt hp
      have he : (x*Real.sqrt (1-1/((n:ℝ)*x^2)))^2=x^2-1/(n:ℝ) := by
        rw [mul_pow,h1]
        field_simp
      apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
      rw [he,h2]
      nlinarith [hx.2]

    exact div_nonneg (sub_nonneg.mpr hroot) (by positivity)

theorem mixedShapeEnvelope_range {n : ℕ} (hn : 0<n) {x : ℝ}
    (hx : x∈Icc (1/Real.sqrt n) 1) :
    1/Real.sqrt n≤ mixedShapeEnvelope n x ∧ mixedShapeEnvelope n x≤1 := by
  have hm := mixedShapeEnvelope_monotone hn
  constructor
  · rw [←mixedShapeEnvelope_base hn]
    exact hm ⟨le_rfl,hx.1.trans hx.2⟩ hx hx.1
  · rw [←mixedShapeEnvelope_one hn]
    exact hm hx ⟨hx.1.trans hx.2,le_rfl⟩ hx.2

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem frobenius_trace_ratio_bounds {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    frobenius R/Matrix.trace R∈Icc (1/Real.sqrt (Fintype.card ι)) 1 := by
  have he := frobenius_pos hR
  have ht := trace_pos hR
  have hN : (0:ℝ)<Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have htr : (Matrix.trace R)^2≤(Fintype.card ι:ℝ)*(frobenius R)^2 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (s:=Finset.univ)
      (fun _:ι=>(1:ℝ)) hR.isHermitian.eigenvalues
    have hf := frobenius_sq R
    rw [←trace_square_eq_sum_sq hR.isHermitian,real_spectral_trace_square hR.isHermitian] at hf
    simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
      ←real_spectral_trace hR.isHermitian,←hf] using hh
  have hsq : (frobenius R)^2≤(Matrix.trace R)^2 := by
    rw [frobenius_eq_sqrt_trace_square hR.isHermitian,Real.sq_sqrt (trace_square_pos hR).le,
      real_spectral_trace hR.isHermitian,real_spectral_trace_square hR.isHermitian]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _=>(hR.eigenvalues_pos i).le)
  constructor
  · apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hN) ht).mpr
    have hn2 := Real.sq_sqrt hN.le
    nlinarith [Real.sqrt_nonneg (Fintype.card ι),mul_nonneg he.le (Real.sqrt_nonneg (Fintype.card ι))]
  · exact (div_le_one ht).mpr (by nlinarith)

theorem mixedShapeEnvelope_spectralRatio {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    spectralRatio R hR≤ mixedShapeEnvelope (Fintype.card ι) (frobenius R/Matrix.trace R) := by
  let N := (Fintype.card ι:ℝ)
  let eta := frobenius R
  let tau := Matrix.trace R
  let M := spectralMaximum R hR.isHermitian
  have hn : 0<N := by dsimp [N];exact_mod_cast Fintype.card_pos
  have he : 0<eta := frobenius_pos hR
  have ht : 0<tau := trace_pos hR
  obtain ⟨top,_,htop⟩ := Finset.exists_mem_eq_sup' (s:=Finset.univ)
    Finset.univ_nonempty hR.isHermitian.eigenvalues
  have hrem := spectral_remainder_cauchy hR.isHermitian.eigenvalues top
  have hf : eta^2=∑i,hR.isHermitian.eigenvalues i^2 := by
    dsimp [eta]
    rw [frobenius_eq_sqrt_trace_square hR.isHermitian,Real.sq_sqrt (trace_square_pos hR).le,
      real_spectral_trace_square hR.isHermitian]
  change M=hR.isHermitian.eigenvalues top at htop
  rw [←real_spectral_trace hR.isHermitian,←hf,←htop] at hrem
  change (tau-M)^2≤(N-1)*(eta^2-M^2) at hrem
  have hx := frobenius_trace_ratio_bounds hR
  have hs := mixedShapeEnvelope_range Fintype.card_pos hx
  have hN1 : (1:ℝ)≤N := by dsimp [N];exact_mod_cast Fintype.card_pos
  have h1 : 0≤1-1/N := sub_nonneg.mpr ((div_le_one hn).mpr hN1)
  have h2 : 0≤1-1/(N*(eta/tau)^2) := by
    have hdiv := (div_le_div_iff₀ (Real.sqrt_pos.mpr hn) ht).mp hx.1
    have hn2 := Real.sq_sqrt hn.le
    have hh : 1≤N*(eta/tau)^2 := by
      rw [div_pow,← mul_div_assoc]
      apply (one_le_div (sq_pos_of_pos ht)).mpr
      have hm := mul_nonneg (sub_nonneg.mpr (show tau≤eta*Real.sqrt N by simpa only [one_mul] using hdiv))
        (show 0≤eta*Real.sqrt N+tau by positivity)
      nlinarith
    exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr hh)
  have hid : (tau-M)^2-(N-1)*(eta^2-M^2)=
      N*eta^2*((M/eta-1/(N*(eta/tau)))^2-(1-1/N)*(1-1/(N*(eta/tau)^2))) := by
    field_simp
    <;> ring
  have hprod : N*eta^2*((M/eta-1/(N*(eta/tau)))^2-
      (1-1/N)*(1-1/(N*(eta/tau)^2)))≤0 := by rw [←hid];linarith
  have hh : (M/eta-1/(N*(eta/tau)))^2≤(1-1/N)*(1-1/(N*(eta/tau)^2)) := by
    have hh := (mul_le_mul_iff_right₀ (mul_pos hn (sq_pos_of_pos he))).mp
      (show N*eta^2*((M/eta-1/(N*(eta/tau)))^2-
        (1-1/N)*(1-1/(N*(eta/tau)^2)))≤N*eta^2*0 by simpa only [mul_zero] using hprod)
    linarith
  have hq : (Real.sqrt (1-1/N)*Real.sqrt (1-1/(N*(eta/tau)^2)))^2=
      (1-1/N)*(1-1/(N*(eta/tau)^2)) := by
    rw [mul_pow,Real.sq_sqrt h1,Real.sq_sqrt h2]
  have hq0 : 0≤Real.sqrt (1-1/N)*Real.sqrt (1-1/(N*(eta/tau)^2)) := by positivity
  change M/eta≤1/(N*(eta/tau))+Real.sqrt (1-1/N)*Real.sqrt (1-1/(N*(eta/tau)^2))
  nlinarith

end
end SingularValueBounds.KL
