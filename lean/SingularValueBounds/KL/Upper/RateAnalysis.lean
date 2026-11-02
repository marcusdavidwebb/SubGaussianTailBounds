import SingularValueBounds.KL.Upper.Margin
import SingularValueBounds.KL.Upper.TailExtension
import SingularValueBounds.KL.Upper.RateEnvelope

/-! # Analytic rescaling in supplementary Lemma S1.7 -/
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix
namespace SingularValueBounds.KL
noncomputable section

def upperFactorF1 (q x : ℝ) : ℝ := 1/(1+x)+(q-1)/(1-(q-1)*x)-q
def upperFactorF2 (q x : ℝ) : ℝ := -1/(1+x)^2+(q-1)^2/(1-(q-1)*x)^2
def upperFactorF3 (q x : ℝ) : ℝ := 2/(1+x)^3+2*(q-1)^3/(1-(q-1)*x)^3

private theorem factor_derivatives {q x : ℝ} (hx : 0 ≤ x) (hd : (q-1)*x < 1) :
    HasDerivAt (upperFactorF q) (upperFactorF1 q x) x ∧
    HasDerivAt (upperFactorF1 q) (upperFactorF2 q x) x ∧
    HasDerivAt (upperFactorF2 q) (upperFactorF3 q x) x := by
  have h1 : 1+x ≠ 0 := by linarith
  have h2 : 1-(q-1)*x ≠ 0 := by linarith
  have hd1 := (hasDerivAt_const x (1:ℝ)).add (hasDerivAt_id x)
  have hd2 := (hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_id x).const_mul (q-1))
  refine ⟨?_,?_,?_⟩
  · convert! ((hd1.log h1).sub (hd2.log h2)).sub ((hasDerivAt_id x).const_mul q) using 1 <;>
      simp [upperFactorF1]
    ring
  · convert! ((hd1.inv h1).add ((hd2.inv h2).const_mul (q-1))).sub_const q using 1 <;>
      (try ext t) <;>
      simp only [upperFactorF1, upperFactorF2, id_eq, Pi.add_apply, Pi.sub_apply,
        Pi.inv_apply, div_eq_mul_inv, ← inv_pow, sub_mul, one_mul, mul_one,
        zero_add, zero_sub] <;> ring
  · convert! (((hd1.inv h1).pow 2).neg.add
      (((hd2.inv h2).pow 2).const_mul ((q-1)^2))) using 1 <;>
      (try ext t) <;>
      simp only [upperFactorF2, upperFactorF3, id_eq, Pi.add_apply, Pi.sub_apply,
        Pi.pow_apply, Pi.neg_apply, Pi.inv_apply, div_eq_mul_inv, ← inv_pow,
        sub_mul, mul_one,
        one_mul, zero_add, zero_sub, Nat.cast_ofNat, Nat.reduceSub, pow_one] <;> ring

/-- The rescaling estimate for the first determinant factors, on the full
positive-denominator domain, without assuming a finite certificate. -/
theorem upperFactorF_quadratic_bound {q x x0 : ℝ} (hq : 1 < q)
    (hx : 0 ≤ x) (hxx0 : x ≤ x0) (hx0 : 0 < x0) (hd : (q-1)*x0 < 1) :
    upperFactorF q x ≤ (x/x0)^2*upperFactorF q x0 := by
  apply quadratic_rescaling_of_third_deriv (f1 := upperFactorF1 q)
    (f2 := upperFactorF2 q) (f3 := upperFactorF3 q) hx0 hx hxx0
  · simp [upperFactorF]
  · simp [upperFactorF1]
  · intro t ht
    exact (factor_derivatives ht.1 (by nlinarith [ht.2])).1
  · intro t ht
    exact (factor_derivatives ht.1 (by nlinarith [ht.2])).2.1
  · intro t ht
    exact (factor_derivatives ht.1 (by nlinarith [ht.2])).2.2
  · intro t ht
    have hqt : 0 < 1-(q-1)*t := by nlinarith [ht.2]
    have hq0 : 0 < q-1 := by linarith
    have ht0 := ht.1
    unfold upperFactorF3
    positivity

/-- The summed rescaling estimate, with the negative-endpoint branch retained. -/
theorem upperFactorF_sum_bound {ι : Type*} [Fintype ι] {q x0 k : ℝ}
    (hq : 1 < q) (hx0 : 0 < x0) (hk : 0 < k) (hd : (q-1)*x0 < 1)
    (x : ι → ℝ) (hx : ∀ i,0 ≤ x i) (hxx0 : ∀ i,x i ≤ x0)
    (hxsq : ∑ i,x i^2 ≤ x0^2/k^2) :
    (∑ i,upperFactorF q (x i)) ≤ max 0 (upperFactorF q x0)/k^2 := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    upperFactorF_quadratic_bound hq (hx i) (hxx0 i) hx0 hd)
  have he : (∑ i,(x i/x0)^2*upperFactorF q x0) =
      ((∑ i,x i^2)/x0^2)*upperFactorF q x0 := by
    simp only [div_pow,← Finset.sum_mul,← Finset.sum_div]
  rw [he] at hs
  by_cases hF : 0 ≤ upperFactorF q x0
  · rw [max_eq_right hF]
    have hb := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hxsq (sq_nonneg x0)) hF
    have hid : ((x0^2/k^2)/x0^2)*upperFactorF q x0 = upperFactorF q x0/k^2 := by
      field_simp [hx0.ne',hk.ne']
    exact hs.trans (by simpa only [hid] using hb)
  · have hF0 : upperFactorF q x0 ≤ 0 := le_of_not_ge hF
    rw [max_eq_left hF0,zero_div]
    exact hs.trans (mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (sq_nonneg _)) hF0)
/-- The scalar correction is exactly the first-factor excess at the endpoint. -/
theorem upperFactorF_rate_identity {v theta : ℝ} (hv : 1 < v) (ht : 1 ≤ theta) :
    upperFactorF (v/theta) ((theta-1)/(v-1)) = upperRateF v theta := by
  have ht0 : 0 < theta := by linarith
  have hv0 : 0 < v-1 := by linarith
  have hbase : 0 < (theta-1)^2+v-1 := by nlinarith [sq_nonneg (theta-1)]
  have hplus : 1+(theta-1)/(v-1) = (theta+v-2)/(v-1) := by
    field_simp [hv0.ne']
    ring
  have hminus : 1-(v/theta-1)*((theta-1)/(v-1)) =
      ((theta-1)^2+v-1)/(theta*(v-1)) := by
    field_simp [ht0.ne',hv0.ne']
    ring
  have hp : 0 < 1+(theta-1)/(v-1) := add_pos_of_pos_of_nonneg zero_lt_one
    (div_nonneg (by linarith) hv0.le)
  have hm : 0 < 1-(v/theta-1)*((theta-1)/(v-1)) := by
    rw [hminus]
    exact div_pos hbase (mul_pos ht0 hv0)
  unfold upperFactorF upperRateF
  rw [← Real.log_div hp.ne' hm.ne',hplus,hminus]
  have hratio : ((theta+v-2)/(v-1))/(((theta-1)^2+v-1)/(theta*(v-1))) =
      theta*(theta+v-2)/((theta-1)^2+v-1) := by
    field_simp [ht0.ne',hv0.ne',hbase.ne']
  rw [hratio]
  congr 1
  field_simp [ht0.ne',hv0.ne']

/-- Positivity and rate control for the second factors need no upper bound
of two on the target rate. -/
theorem upper_rate_rescaling_denominator {v theta H : ℝ} (hv : 1 < v)
    (htheta : 1 ≤ theta) (hH : 0 ≤ H) (hmargin : H*(v-1) ≤ theta-1) :
    let q := v/theta
    0 < 1-(q-1)*H ∧ q/(1-(q-1)*H) ≤ v := by
  let q := v/theta
  have ht0 : 0 < theta := by linarith
  have hq : 0 < q := div_pos (by linarith) ht0
  have hqtheta : q*theta = v := div_mul_cancel₀ v ht0.ne'
  by_cases hq1 : q ≤ 1
  · have hd : 1 ≤ 1-(q-1)*H := by nlinarith
    exact ⟨by linarith,(div_le_self hq.le hd).trans (div_le_self (by linarith) htheta)⟩
  · have hm : (q-1)*H ≤ (theta-1)/theta := by
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
    refine ⟨hd,(div_le_iff₀ hd).2 ?_⟩
    have hmul := mul_le_mul_of_nonneg_left hm (show 0 ≤ v by linarith)
    have he : v*((theta-1)/theta) = v-q := by dsimp [q];field_simp [ht0.ne']
    rw [he] at hmul
    linarith

/-- Complete spectral log-determinant estimate in the `q>1` branch of the
extended-rate proof, retaining the rate correction `C/k²`. -/
theorem upper_extended_spectral_logdet {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {r : ι → ℝ} (hr : ∀ i,0 < r i) {h eta k v v0 theta C : ℝ}
    (hh : 0 < h) (heta : 0 < eta) (hk : 0 < k)
    (hnorm : eta^2 = ∑ i,r i^2) (hmax : ∀ i,r i ≤ k*eta)
    (hv0 : 1 < v0) (hvv : v0 ≤ v) (hvk : v*k^2 < 1)
    (htheta : 1 < theta) (hthetav : theta < v0) (hC : 0 ≤ C)
    (hmargin : h*eta*k*(v0-1) ≤ theta-1) (hFc : upperRateF v0 theta ≤ C) :
    (∀ i,0 < 1-(v0/theta)*upperTailEigenvalue r h i) ∧
      -(∑ i,Real.log (1-(v0/theta)*upperTailEigenvalue r h i)) ≤
        (v0/theta)*h*(∑ i,r i)+C/k^2-Real.log (1-v*k^2)/k^2 := by
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
  have hps := upperTailWeight_le_normalized hr hh.le heta hnorm hmax
  obtain ⟨hsecond,hsecondcost⟩ := upper_tail_second_cost_shape hr hh.le (by linarith : 0 < q)
    (by linarith : 0 < v) (sq_pos_of_pos hk) hvk hps hden hrate
  have ht := upper_tail_logdet_of_costs hr hh.le hden hsecond hfirstcost hsecondcost
  convert! ht using 1 <;> dsimp [q] <;> ring

end
end SingularValueBounds.KL
