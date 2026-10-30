import SingularValueBounds.Core.ScalarTail
import SingularValueBounds.KL.Certificates.Enclosures

open MeasureTheory Set Filter
open scoped ENNReal
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000

/-- The finite sum in the exact first-moment cutoff formula. -/
def tailMomentSeries (p : ℕ) (A s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range p, A^j*s^(p-1-j)/(j.factorial : ℝ)

/-- Its exact factorial recurrence. -/
theorem tailMomentSeries_succ {p : ℕ} (hp : 1 ≤ p) (A s : ℝ) :
    tailMomentSeries (p+1) A s = s*tailMomentSeries p A s + A^p/(p.factorial : ℝ) := by
  unfold tailMomentSeries
  rw [Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hjp : j < p := Finset.mem_range.mp hj
    have hpow : p-j = (p-1-j)+1 := by omega
    simp only [Nat.add_sub_cancel, hpow, pow_succ]
    ring
  · simp

/-- Positivity of the finite sum, needed when replacing the tail coefficient. -/
theorem tailMomentSeries_nonneg {p : ℕ} {A s : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s) :
    0 ≤ tailMomentSeries p A s := by
  unfold tailMomentSeries
  exact Finset.sum_nonneg fun j hj => by positivity

/-- The last summand controls the extra term in the factorial recurrence. -/
theorem tailMomentSeries_succ_le {p : ℕ} (hp : 1 ≤ p) {A s : ℝ}
    (hA : 0 ≤ A) (hs : 0 ≤ s) :
    tailMomentSeries (p+1) A s ≤ (s+A/p)*tailMomentSeries p A s := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hlast : A^(p-1)/((p-1).factorial : ℝ) ≤ tailMomentSeries p A s := by
    have h := Finset.single_le_sum (f := fun j => A^j*s^(p-1-j)/(j.factorial : ℝ))
      (fun j hj => by positivity) (show p-1 ∈ Finset.range p by simp; omega)
    simpa [tailMomentSeries] using h
  have hf : (p.factorial : ℝ) = (p : ℝ)*((p-1).factorial : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : p ≠ 0)).symm
  have he : A^p/(p.factorial : ℝ) = (A/p)*(A^(p-1)/((p-1).factorial : ℝ)) := by
    rw [hf]
    nth_rw 1 [show p = (p-1)+1 by omega]
    rw [pow_succ]
    field_simp
  rw [tailMomentSeries_succ hp, he]
  nlinarith [mul_le_mul_of_nonneg_left hlast (div_nonneg hA hp0.le)]

/-- The numerical majorant obtained after epsilon is bounded by one quarter. -/
def tailMomentCoefficient (p : ℕ) : ℝ :=
  (3/4 : ℝ)*(15/2 : ℝ)^(p-1)/(p.factorial : ℝ) +
    (1/4 : ℝ)*tailMomentSeries p (15/2) (20/9)

/-- Every order at least three satisfies the required geometric bound. -/
theorem tailMomentCoefficient_le {p : ℕ} (hp : 3 ≤ p) :
    tailMomentCoefficient p ≤ (9/2 : ℝ)^(p-1) := by
  have h3 : tailMomentCoefficient 3 ≤ (9/2 : ℝ)^2 := by
    norm_num [tailMomentCoefficient, tailMomentSeries, Finset.sum_range_succ]
  by_cases hp3 : p = 3
  · simpa [hp3] using h3
  have hp4 : 4 ≤ p := by omega
  have h4 : tailMomentCoefficient 4 ≤ (9/2 : ℝ)^3 := by
    norm_num [tailMomentCoefficient, tailMomentSeries, Finset.sum_range_succ]
  have hstep : ∀ n : ℕ, 4 ≤ n →
      tailMomentCoefficient (n+1) ≤ (9/2 : ℝ)*tailMomentCoefficient n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hT := tailMomentSeries_succ_le (show 1 ≤ n by omega)
      (A := (15/2 : ℝ)) (s := (20/9 : ℝ)) (by norm_num) (by norm_num)
    have hT0 := tailMomentSeries_nonneg (p := n) (A := (15/2 : ℝ)) (s := (20/9 : ℝ))
      (by norm_num) (by norm_num)
    have hratio : (20/9 : ℝ)+(15/2 : ℝ)/n ≤ 9/2 := by
      have hdiv : (15/2 : ℝ)/n ≤ 9/2-20/9 :=
        (div_le_iff₀ hn0).2 (by nlinarith)
      linarith
    have hA : (15/2 : ℝ)^n/((n+1).factorial : ℝ) ≤
        (9/2 : ℝ)*((15/2 : ℝ)^(n-1)/(n.factorial : ℝ)) := by
      have he : (15/2 : ℝ)^n/((n+1).factorial : ℝ) =
          ((15/2 : ℝ)/(n+1))*((15/2 : ℝ)^(n-1)/(n.factorial : ℝ)) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        have hpow : (15/2 : ℝ)^n = (15/2 : ℝ)*(15/2 : ℝ)^(n-1) := by
          calc
            _ = (15/2 : ℝ)^((n-1)+1) := congrArg _ (by omega)
            _ = _ := by rw [pow_succ]; ring
        rw [hpow]
        field_simp
        <;> ring
      rw [he]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < n+1)).2
      nlinarith
    dsimp [tailMomentCoefficient]
    have hTT : tailMomentSeries (n+1) (15/2 : ℝ) (20/9) ≤
        (9/2 : ℝ)*tailMomentSeries n (15/2) (20/9) :=
      hT.trans (mul_le_mul_of_nonneg_right hratio hT0)
    convert! add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 3/4))
      (mul_le_mul_of_nonneg_left hTT (by norm_num : (0 : ℝ) ≤ 1/4)) using 1 <;> ring
  clear hp hp3
  induction p, hp4 using Nat.le_induction with
  | base => simpa using h4
  | succ p hp ih =>
    have h := hstep p hp
    have hpow : (9/2 : ℝ)^p = (9/2 : ℝ)*(9/2 : ℝ)^(p-1) := by
      calc
        _ = (9/2 : ℝ)^((p-1)+1) := congrArg _ (by omega)
        _ = _ := by rw [pow_succ]; ring
    simpa only [Nat.add_sub_cancel, hpow] using
      h.trans (mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 9/2))

private theorem monomial_exp_integrable (n : ℕ) {r A : ℝ} (hr : 0 < r) (hA : 0 ≤ A) :
    IntegrableOn (fun u : ℝ => u^n*Real.exp (-(r*u))) (Ioi A) := by
  exact integrableOn_pow_mul_exp_neg_mul_Ioi n hr hA

/-- Exact incomplete factorial integral, proved by integration by parts. -/
theorem integral_monomial_exp_cutoff (n : ℕ) {r A : ℝ} (hr : 0 < r) (hA : 0 ≤ A) :
    (∫ u in Ioi A, u^n*Real.exp (-(r*u))) =
      (n.factorial : ℝ)*(1/r)*Real.exp (-(r*A))*tailMomentSeries (n+1) A (1/r) := by
  induction n with
  | zero =>
    simp only [pow_zero, one_mul]
    rw [show (fun u : ℝ => Real.exp (-(r*u))) = (fun u => Real.exp ((-r)*u)) by
      ext u; congr 1; ring, integral_exp_mul_Ioi (by linarith : -r < 0) A]
    norm_num [tailMomentSeries, Finset.sum_range_succ]
    ring
  | succ n ih =>
    let F : ℝ → ℝ := fun u => u^(n+1)*Real.exp (-(r*u))
    let g : ℝ → ℝ := fun u => (n+1 : ℝ)*(u^n*Real.exp (-(r*u))) -
      r*(u^(n+1)*Real.exp (-(r*u)))
    have hd : ∀ u ∈ Ici A, HasDerivAt F (g u) u := by
      intro u hu
      convert! ((hasDerivAt_pow (n+1) u).mul
        (((hasDerivAt_id u).const_mul (-r)).exp)) using 1 <;>
        (try ext x) <;> simp [F, g, Nat.cast_add, Nat.cast_one, Pi.mul_apply] <;> ring
    have hgi : IntegrableOn g (Ioi A) :=
      ((monomial_exp_integrable n hr hA).const_mul (n+1 : ℝ)).sub
        ((monomial_exp_integrable (n+1) hr hA).const_mul r)
    have hlim : Tendsto F atTop (nhds 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n+1 : ℕ) r hr
      simpa only [F, Real.rpow_natCast, neg_mul] using h
    have hi := integral_Ioi_of_hasDerivAt_of_tendsto' hd hgi hlim
    change (∫ u in Ioi A, (n+1 : ℝ)*(u^n*Real.exp (-(r*u))) -
      r*(u^(n+1)*Real.exp (-(r*u)))) = 0-F A at hi
    rw [integral_sub ((monomial_exp_integrable n hr hA).const_mul _)
      ((monomial_exp_integrable (n+1) hr hA).const_mul _), integral_const_mul,
      integral_const_mul, ih] at hi
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    dsimp [F] at hi
    have hsolve : (∫ u in Ioi A, u^(n+1)*Real.exp (-(r*u))) =
        ((n+1 : ℝ)*((n.factorial : ℝ)*(1/r)*Real.exp (-(r*A))*
          tailMomentSeries (n+1) A (1/r)) + A^(n+1)*Real.exp (-(r*A)))/r := by
      apply (eq_div_iff hr.ne').2
      linarith [hi]
    rw [hsolve, tailMomentSeries_succ (by omega : 1 ≤ n+1), Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp [hr.ne', hf]
    <;> ring

private theorem cutoff_lintegral_translate (f : ℝ → ℝ≥0∞) (A : ℝ) :
    (∫⁻ u in Ioi 0, f (A+u)) = ∫⁻ u in Ioi A, f u := by
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
  have h := lintegral_add_left_eq_self (μ := volume) ((Ioi A).indicator f) A
  convert! h using 1
  apply lintegral_congr
  intro u
  by_cases hu : 0 < u
  · simp [Set.indicator_of_mem, hu, show A < A+u by linarith]
  · simp [Set.indicator_of_notMem, hu, show ¬ A < A+u by linarith]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Exact first-moment cutoff bound, supplementary equation
`eq:app-tail-moment-integration`, with arbitrary cutoff and exponential rate.
All moments and the tail integral are proved finite from the exponential tail. -/
theorem first_moment_cutoff [IsProbabilityMeasure μ] {Y : Ω → ℝ} {C r A : ℝ}
    (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hC : 0 ≤ C) (hr : 0 < r) (hA : 0 ≤ A)
    (htail : ∀ u : ℝ, 0 ≤ u → μ.real {ω | u < Y ω} ≤ C*Real.exp (-(r*u)))
    (hmean : (∫ ω, Y ω ∂μ) ≤ 1) (n : ℕ) :
    (∫ ω, Y ω^(n+1) ∂μ)/((n+1).factorial : ℝ) ≤
      (1-C/r*Real.exp (-(r*A)))*A^n/((n+1).factorial : ℝ) +
      (C/r*Real.exp (-(r*A)))*tailMomentSeries (n+1) A (1/r) := by
  let U : Ω → ℝ := fun ω => max (Y ω-A) 0
  let F : ℝ → ℝ := fun t => (A+t)^(n+1)-A^(n+1)-A^n*t
  let g : ℝ → ℝ := fun t => (n+1 : ℝ)*(A+t)^n-A^n
  let H : ℝ → ℝ := fun u => C*((n+1 : ℝ)*(u^n*Real.exp (-(r*u)))-
    A^n*Real.exp (-(r*u)))
  have hYi : Integrable Y μ := by
    simpa using (exponential_tail_moment hY.aemeasurable hY0 hC hr htail 0).1
  have hYp : Integrable (fun ω => Y ω^(n+1)) μ :=
    (exponential_tail_moment hY.aemeasurable hY0 hC hr htail n).1
  have hU0 : ∀ ω, 0 ≤ U ω := fun ω => le_max_right _ _
  have hg0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ g t := by
    intro t ht
    have hpow := pow_le_pow_left₀ hA (show A ≤ A+t by linarith) n
    have hn : (1 : ℝ) ≤ n+1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    dsimp [g]
    nlinarith [pow_nonneg hA n, pow_nonneg (show 0 ≤ A+t by linarith) n]
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hd : ∀ t : ℝ, HasDerivAt F (g t) t := by
    intro t
    convert! (((((hasDerivAt_const t A).add (hasDerivAt_id t)).pow (n+1)).sub_const
      (A^(n+1))).sub ((hasDerivAt_id t).const_mul (A^n))) using 1 <;>
      simp [F, g, Nat.cast_add, Nat.cast_one] <;> ring
  have hFi : ∀ t : ℝ, (∫ u in (0 : ℝ)..t, g u) = F t := by
    intro t
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => hd u) (hg.intervalIntegrable 0 t)
    simpa [F] using hi
  have hFn : ∀ t : ℝ, 0 ≤ t → 0 ≤ F t := by
    intro t ht
    rw [← hFi]
    exact intervalIntegral.integral_nonneg ht (fun u hu => hg0 u hu.1)
  have hFU : ∀ ω, F (U ω) =
      ({ω | A < Y ω}.indicator (fun ω => Y ω^(n+1)-A^n*Y ω)) ω := by
    intro ω
    by_cases hw : A < Y ω
    · simp only [Set.indicator, Set.mem_setOf_eq, hw, if_true]
      dsimp [F, U]
      rw [max_eq_left (by linarith : 0 ≤ Y ω-A), show A+(Y ω-A) = Y ω by ring]
      rw [pow_succ]
      ring
    · simp only [Set.indicator, Set.mem_setOf_eq, hw, if_false]
      dsimp [F, U]
      rw [max_eq_right (by linarith : Y ω-A ≤ 0)]
      simp
  have hFint : Integrable (fun ω => F (U ω)) μ := by
    have hi := (hYp.sub (hYi.const_mul (A^n))).indicator
      (measurableSet_lt (measurable_const : Measurable (fun _ : Ω => A)) hY)
    exact hi.congr (Filter.Eventually.of_forall fun ω => (hFU ω).symm)
  have hPoint : ∀ ω, Y ω^(n+1) ≤ A^n*Y ω+F (U ω) := by
    intro ω
    rw [hFU]
    by_cases hw : A < Y ω
    · simp only [Set.indicator, Set.mem_setOf_eq, hw, if_true]
      linarith
    · simp only [Set.indicator, Set.mem_setOf_eq, hw, if_false, add_zero]
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hY0 ω) (le_of_not_gt hw) n) (hY0 ω)
  have hpointint := integral_mono hYp ((hYi.const_mul (A^n)).add hFint) hPoint
  change (∫ ω, Y ω^(n+1) ∂μ) ≤ (∫ ω, A^n*Y ω+F (U ω) ∂μ) at hpointint
  rw [integral_add (hYi.const_mul _) hFint, integral_const_mul] at hpointint
  have hmeanmul := mul_le_mul_of_nonneg_left hmean (pow_nonneg hA n)
  have he : IntegrableOn (fun u : ℝ => Real.exp (-(r*u))) (Ioi A) := by
    simpa using monomial_exp_integrable 0 hr hA
  have hHi : IntegrableOn H (Ioi A) := by
    exact (((monomial_exp_integrable n hr hA).const_mul (n+1 : ℝ)).sub
      (he.const_mul (A^n))).const_mul C
  have hH0 : ∀ᵐ u ∂volume.restrict (Ioi A), 0 ≤ H u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hg := hg0 (u-A) (by have hu' : A < u := hu; linarith)
    have hid : H u = C*Real.exp (-(r*u))*g (u-A) := by
      dsimp [H, g]
      rw [show A+(u-A) = u by ring]
      ring
    rw [hid]
    positivity
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (Filter.Eventually.of_forall hU0) ((hY.sub_const A).max measurable_const).aemeasurable
    (fun t ht => hg.intervalIntegrable 0 t)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact hg0 t ht.le)
  have hleft : (∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..U ω, g t) ∂μ) =
      ENNReal.ofReal (∫ ω, F (U ω) ∂μ) := by
    simp_rw [hFi]
    exact (ofReal_integral_eq_lintegral_ofReal hFint
      (Filter.Eventually.of_forall fun ω => hFn _ (hU0 ω))).symm
  have hLayerBound : ENNReal.ofReal (∫ ω, F (U ω) ∂μ) ≤
      ENNReal.ofReal (∫ u in Ioi A, H u) := by
    rw [← hleft, hlayer, ofReal_integral_eq_lintegral_ofReal hHi hH0,
      ← cutoff_lintegral_translate (fun u => ENNReal.ofReal (H u)) A]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hset : {ω | t < U ω} = {ω | A+t < Y ω} := by
      ext ω
      dsimp [U]
      simp only [Set.mem_setOf_eq, lt_max_iff]
      constructor
      · rintro (h | h) <;> linarith
      · intro h; exact Or.inl (by linarith)
    rw [hset]
    have htail' := ENNReal.ofReal_le_ofReal (htail (A+t) (by linarith))
    rw [ofReal_measureReal] at htail'
    calc
      _ ≤ ENNReal.ofReal (C*Real.exp (-(r*(A+t)))) * ENNReal.ofReal (g t) :=
        mul_le_mul_left htail' _
      _ = ENNReal.ofReal (H (A+t)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        dsimp [H, g]
        ring
  have hFbound : (∫ ω, F (U ω) ∂μ) ≤ ∫ u in Ioi A, H u :=
    (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hH0)).1 hLayerBound
  have hHint : (∫ u in Ioi A, H u) =
      C/r*Real.exp (-(r*A))*
        (((n+1).factorial : ℝ)*tailMomentSeries (n+1) A (1/r)-A^n) := by
    dsimp [H]
    rw [integral_const_mul,
      integral_sub ((monomial_exp_integrable n hr hA).const_mul (n+1 : ℝ))
        (he.const_mul (A^n)), integral_const_mul, integral_const_mul,
      integral_monomial_exp_cutoff n hr hA]
    have hz : (∫ u in Ioi A, Real.exp (-(r*u))) = (1/r)*Real.exp (-(r*A)) := by
      simpa [tailMomentSeries, Finset.sum_range_succ] using integral_monomial_exp_cutoff 0 hr hA
    rw [hz, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  rw [hHint] at hFbound
  have hf : (0 : ℝ) < ((n+1).factorial : ℝ) := by positivity
  apply (div_le_iff₀ hf).2
  have hfinal : (∫ ω, Y ω^(n+1) ∂μ) ≤ A^n +
      C/r*Real.exp (-(r*A))*(((n+1).factorial : ℝ)*tailMomentSeries (n+1) A (1/r)-A^n) := by
    nlinarith
  convert! hfinal using 1
  field_simp [hf.ne']
  <;> ring

/-- Scaling both arguments of the factorial sum is homogeneous. -/
theorem tailMomentSeries_scale (p : ℕ) (A s B : ℝ) :
    tailMomentSeries p (A*B) (s*B) = B^(p-1)*tailMomentSeries p A s := by
  unfold tailMomentSeries
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he : j+(p-1-j) = p-1 := by have := Finset.mem_range.mp hj; omega
  simp only [mul_pow]
  calc
    _ = (A^j*s^(p-1-j))*(B^j*B^(p-1-j))/(j.factorial : ℝ) := by ring
    _ = _ := by rw [← pow_add, he]; ring

/-- Monotonicity in the exponential scale. -/
theorem tailMomentSeries_mono_scale (p : ℕ) {A s t : ℝ}
    (hA : 0 ≤ A) (hs : 0 ≤ s) (hst : s ≤ t) :
    tailMomentSeries p A s ≤ tailMomentSeries p A t := by
  apply Finset.sum_le_sum
  intro j hj
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst _) (pow_nonneg hA _))
    (Nat.cast_nonneg _)

/-- The coefficient of epsilon in the cutoff estimate is nonnegative. -/
theorem tailMomentSeries_ge_leading (n : ℕ) {A s : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s) :
    A^n/((n+1).factorial : ℝ) ≤ tailMomentSeries (n+1) A s := by
  have hlast : A^n/(n.factorial : ℝ) ≤ tailMomentSeries (n+1) A s := by
    have h := Finset.single_le_sum (f := fun j => A^j*s^(n+1-1-j)/(j.factorial : ℝ))
      (fun j hj => by positivity) (show n ∈ Finset.range (n+1) by simp)
    simpa [tailMomentSeries] using h
  apply le_trans _ hlast
  apply div_le_div_of_nonneg_left (pow_nonneg hA _) (by positivity)
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  nlinarith [Nat.cast_nonneg (α := ℝ) n, (show (0 : ℝ) ≤ n.factorial by positivity)]

/-- Replacing epsilon by one quarter and the scale by its uniform upper bound. -/
theorem cutoff_coefficient_le (n : ℕ) {B s ε : ℝ}
    (hB : 0 ≤ B) (hs : 0 ≤ s) (hsB : s ≤ (20/9 : ℝ)*B)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1/4) :
    (1-ε)*((15/2 : ℝ)*B)^n/((n+1).factorial : ℝ) +
      ε*tailMomentSeries (n+1) ((15/2 : ℝ)*B) s ≤
      B^n*tailMomentCoefficient (n+1) := by
  let a := ((15/2 : ℝ)*B)^n/((n+1).factorial : ℝ)
  let T := tailMomentSeries (n+1) ((15/2 : ℝ)*B) s
  have hTa : a ≤ T := tailMomentSeries_ge_leading n (by positivity) hs
  have hInterp : (1-ε)*a+ε*T ≤ (3/4 : ℝ)*a+(1/4 : ℝ)*T := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hε) (sub_nonneg.mpr hTa)]
  have hT := tailMomentSeries_mono_scale (n+1) (A := (15/2 : ℝ)*B) (by positivity) hs hsB
  rw [tailMomentSeries_scale] at hT
  have hh := hInterp.trans (add_le_add_right (mul_le_mul_of_nonneg_left hT
    (by norm_num : (0 : ℝ) ≤ 1/4)) ((3/4 : ℝ)*a))
  convert! hh using 1 <;> dsimp [a, T, tailMomentCoefficient] <;>
    simp only [Nat.add_sub_cancel, mul_pow] <;> ring

/-- The finite Taylor lower bound used in the epsilon estimate. -/
theorem exp_twenty_seven_eighths_lower : (146/5 : ℝ) < Real.exp (27/8) := by
  have h := Certificates.expTaylor_le_exp 10 (x := (27/8 : ℝ)) (by norm_num)
  norm_num [Certificates.expTaylor, Finset.sum_range_succ] at h ⊢
  linarith

/-- The decaying epsilon bound, with the real exponential argument proved. -/
theorem cutoff_epsilon_bound (L : ℝ) :
    (20*Real.sqrt 10/9)*Real.exp (-2-11*L/8) ≤
      (1/4 : ℝ)*Real.exp (-11*(L-1)/8) := by
  have hs : Real.sqrt 10 ≤ (3163/1000 : ℝ) := by
    have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)
    nlinarith [Real.sqrt_nonneg (10 : ℝ)]
  have he := Certificates.exp_neg_le_reciprocal (x := (27/8 : ℝ))
    (lo := (146/5 : ℝ)) (by norm_num) exp_twenty_seven_eighths_lower.le
  have hc : (20*Real.sqrt 10/9)*Real.exp (-(27/8 : ℝ)) ≤ 1/4 := by
    have hpos : 0 ≤ Real.exp (-(27/8 : ℝ)) := Real.exp_nonneg _
    nlinarith
  rw [show -2-11*L/8 = -(27/8 : ℝ)+(-11*(L-1)/8) by ring, Real.exp_add]
  nlinarith [mul_le_mul_of_nonneg_right hc (Real.exp_nonneg (-11*(L-1)/8))]

/-- Rewriting the cutoff tail mass in terms of `L=1+log K`. -/
theorem cutoff_epsilon_identity {K L : ℝ} (hK : 0 < K) (hKL : L = 1+Real.log K) :
    Real.sqrt 10/(9/(20*K^2))*Real.exp (-((9/(20*K^2))*((15/2)*K^2*L))) =
      (20*Real.sqrt 10/9)*Real.exp (-2-11*L/8) := by
  have hK2 : K^2 ≠ 0 := pow_ne_zero _ hK.ne'
  have harg : (9/(20*K^2))*((15/2)*K^2*L) = (27/8)*L := by field_simp <;> ring
  have hpow : K^2 = Real.exp (2*(L-1)) := by
    rw [show 2*(L-1) = Real.log K+Real.log K by rw [hKL]; ring,
      Real.exp_add, Real.exp_log hK]
    ring
  rw [harg]
  have hm : K^2*Real.exp (-((27/8)*L)) = Real.exp (-2-11*L/8) := by
    rw [hpow, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (20*Real.sqrt 10/9)*(K^2*Real.exp (-((27/8)*L))) := by field_simp <;> ring
    _ = _ := by rw [hm]

/-- Supplementary Lemma S1.11: the complete higher-moment assertion. -/
theorem upper_tail_higher_moments [IsProbabilityMeasure μ] {Y : Ω → ℝ} {K L : ℝ}
    (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hK : 1 ≤ K)
    (hKL : L = 1+Real.log K)
    (hmean : (∫ ω, Y ω ∂μ) ≤ 1)
    (htail : ∀ u : ℝ, 0 ≤ u → μ.real {ω | u < Y ω} ≤
      Real.sqrt 10*Real.exp (-(9*u/(20*K^2))))
    (p : ℕ) (hp : 3 ≤ p) :
    Integrable (fun ω => Y ω^p) μ ∧
      (∫ ω, Y ω^p ∂μ)/(p.factorial : ℝ) ≤ ((9/2)*K^2*L)^(p-1) := by
  have hKpos : 0 < K := by linarith
  have hL : 1 ≤ L := by rw [hKL]; linarith [Real.log_nonneg hK]
  have hB : 0 ≤ K^2*L := by positivity
  have hr : 0 < (9 : ℝ)/(20*K^2) := by positivity
  have ht : ∀ u : ℝ, 0 ≤ u → μ.real {ω | u < Y ω} ≤
      Real.sqrt 10*Real.exp (-((9/(20*K^2))*u)) := by
    intro u hu
    convert! htail u hu using 1 <;> congr 2 <;> ring
  have hcut := first_moment_cutoff hY hY0 (Real.sqrt_nonneg 10) hr
    (A := (15/2)*K^2*L) (by positivity) ht hmean (p-1)
  have hpEq : p-1+1 = p := by omega
  rw [hpEq] at hcut
  let ε := Real.sqrt 10/(9/(20*K^2))*Real.exp (-((9/(20*K^2))*((15/2)*K^2*L)))
  have hε0 : 0 ≤ ε := by dsimp [ε]; positivity
  have hε : ε ≤ 1/4 := by
    dsimp [ε]
    rw [cutoff_epsilon_identity hKpos hKL]
    have h := cutoff_epsilon_bound L
    have hExp : Real.exp (-11*(L-1)/8) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    nlinarith
  have hcoeff := cutoff_coefficient_le (p-1) hB
    (s := 1/(9/(20*K^2))) (by positivity)
    (by field_simp; nlinarith [sq_nonneg K]) hε0 hε
  rw [hpEq] at hcoeff
  have hAeq : (15/2 : ℝ)*(K^2*L) = (15/2)*K^2*L := by ring
  rw [hAeq] at hcoeff
  have hmain := hcut.trans hcoeff
  have hfinal := mul_le_mul_of_nonneg_left (tailMomentCoefficient_le hp)
    (pow_nonneg hB (p-1))
  refine ⟨?_, ?_⟩
  · simpa [hpEq] using (exponential_tail_moment hY.aemeasurable hY0
      (Real.sqrt_nonneg 10) hr ht (p-1)).1
  · convert! hmain.trans hfinal using 1
    rw [← mul_pow]
    congr 1
    ring

/-- The second-moment cost from the decaying epsilon estimate. -/
def upperSecondMomentCost (L : ℝ) : ℝ :=
  15/4+(1/4)*Real.exp (-11*(L-1)/8)*(15/4+(20/9)/L) -
    (1/2)*Real.exp (-2*(L-1))/L

def upperSecondMomentDerivative (L : ℝ) : ℝ :=
  (1/4)*Real.exp (-11*(L-1)/8)*
    ((-11/8)*(15/4+(20/9)/L)-(20/9)/L^2) +
    Real.exp (-2*(L-1))*(1/L+1/(2*L^2))

/-- Differentiating the actual second-moment cost. -/
theorem hasDerivAt_upperSecondMomentCost {L : ℝ} (hL : L ≠ 0) :
    HasDerivAt upperSecondMomentCost (upperSecondMomentDerivative L) L := by
  have he1 := ((((hasDerivAt_id L).sub_const 1).const_mul (-11 : ℝ)).div_const 8).exp
  have he2 := (((hasDerivAt_id L).sub_const 1).const_mul (-2 : ℝ)).exp
  have hr := (hasDerivAt_const L (20/9 : ℝ)).div (hasDerivAt_id L) hL
  have ht := (he2.const_mul (1/2 : ℝ)).div (hasDerivAt_id L) hL
  convert! ((hasDerivAt_const L (15/4 : ℝ)).add
    ((he1.mul ((hasDerivAt_const L (15/4 : ℝ)).add hr)).const_mul (1/4 : ℝ))).sub ht using 1 <;>
      (try ext x) <;> simp only [upperSecondMomentCost, upperSecondMomentDerivative,
        Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, id_eq] <;>
      field_simp <;> ring

/-- The printed derivative certificate, including its exponential factor. -/
theorem upperSecondMomentCost_scaled_derivative {L : ℝ} (hL : 1 ≤ L) :
    -L^2*Real.exp (2*(L-1))*upperSecondMomentDerivative L ≥
      (165/128 : ℝ)*L^2-(17/72 : ℝ)*L+1/18 := by
  have hL0 : L ≠ 0 := ne_of_gt (by linarith)
  have he1 : Real.exp (-11*(L-1)/8)*Real.exp (2*(L-1)) = Real.exp (5*(L-1)/8) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he2 : Real.exp (-2*(L-1))*Real.exp (2*(L-1)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hid : -L^2*Real.exp (2*(L-1))*upperSecondMomentDerivative L =
      Real.exp (5*(L-1)/8)*((165/128 : ℝ)*L^2+(55/72 : ℝ)*L+5/9)-L-1/2 := by
    calc
      _ = (Real.exp (-11*(L-1)/8)*Real.exp (2*(L-1)))*
          ((165/128 : ℝ)*L^2+(55/72 : ℝ)*L+5/9) -
          (Real.exp (-2*(L-1))*Real.exp (2*(L-1)))*(L+1/2) := by
        dsimp [upperSecondMomentDerivative]
        field_simp
        <;> ring
      _ = _ := by rw [he1, he2]; ring
  rw [hid]
  have he : 1 ≤ Real.exp (5*(L-1)/8) := Real.one_le_exp_iff.mpr (by linarith)
  have hQ : 0 ≤ (165/128 : ℝ)*L^2+(55/72 : ℝ)*L+5/9 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right he hQ]

/-- The cost decreases throughout `L ≥ 1`, rather than only on a finite grid. -/
theorem upperSecondMomentCost_antitone : AntitoneOn upperSecondMomentCost (Ici 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 1)
  · intro L hL
    exact (hasDerivAt_upperSecondMomentCost (ne_of_gt (by have hL1 : 1 ≤ L := hL; linarith))).continuousAt.continuousWithinAt
  · intro L hL
    have hL1 : 1 ≤ L := interior_subset hL
    exact (hasDerivAt_upperSecondMomentCost (ne_of_gt (by linarith : 0 < L))).hasDerivWithinAt
  · intro L hL
    have hL1 : 1 ≤ L := interior_subset hL
    have hscaled := upperSecondMomentCost_scaled_derivative hL1
    have hP : (0 : ℝ) < (165/128 : ℝ)*L^2-(17/72 : ℝ)*L+1/18 := by
      nlinarith [sq_nonneg (L-1)]
    have hpos : 0 < L^2*Real.exp (2*(L-1)) := by positivity
    nlinarith

/-- The finite Taylor check at the printed second-moment endpoint. -/
theorem upperSecondMomentCost_five_quarters : upperSecondMomentCost (5/4) < (9/2 : ℝ) := by
  have h11 := Certificates.expTaylor_le_exp 2 (x := (11/32 : ℝ)) (by norm_num)
  have hhalf := Certificates.exp_le_expTaylorUpper 2 (x := (1/2 : ℝ))
    (by norm_num) (by norm_num)
  have hlo : (0 : ℝ) < Certificates.expTaylor 2 (11/32) := by
    norm_num [Certificates.expTaylor, Finset.sum_range_succ]
  have hup : (0 : ℝ) < Certificates.expTaylorUpper 2 (1/2) := by
    norm_num [Certificates.expTaylorUpper, Certificates.expTaylor, Finset.sum_range_succ]
  have h11' := Certificates.exp_neg_le_reciprocal hlo h11
  have hhalf' : 1/Certificates.expTaylorUpper 2 (1/2) ≤ Real.exp (-(1/2 : ℝ)) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) hhalf
  have hbound : (15/4 : ℝ)+(1/4)*(1/Certificates.expTaylor 2 (11/32))*(15/4+16/9) -
      (2/5)*(1/Certificates.expTaylorUpper 2 (1/2)) < 9/2 := by
    norm_num [Certificates.expTaylorUpper, Certificates.expTaylor, Finset.sum_range_succ]
  norm_num [upperSecondMomentCost] at *
  nlinarith

/-- The uniform second-moment cost bound for all `L ≥ 5/4`. -/
theorem upperSecondMomentCost_lt {L : ℝ} (hL : (5/4 : ℝ) ≤ L) :
    upperSecondMomentCost L < (9/2 : ℝ) :=
  (upperSecondMomentCost_antitone (show (5/4 : ℝ) ∈ Ici 1 by norm_num)
    (show L ∈ Ici 1 by change 1 ≤ L; linarith) hL).trans_lt
    upperSecondMomentCost_five_quarters

/-- Supplementary Lemma S1.11: the strict second-moment assertion. -/
theorem upper_tail_second_moment [IsProbabilityMeasure μ] {Y : Ω → ℝ} {K L : ℝ}
    (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hK : 1 ≤ K)
    (hKL : L = 1+Real.log K) (hL : (5/4 : ℝ) ≤ L)
    (hmean : (∫ ω, Y ω ∂μ) ≤ 1)
    (htail : ∀ u : ℝ, 0 ≤ u → μ.real {ω | u < Y ω} ≤
      Real.sqrt 10*Real.exp (-(9*u/(20*K^2)))) :
    Integrable (fun ω => Y ω^2) μ ∧
      (∫ ω, Y ω^2 ∂μ)/(2*K^2*L)-1/(2*K^2*L) < (9/2 : ℝ) := by
  have hKpos : 0 < K := by linarith
  have hK2 : K^2 ≠ 0 := pow_ne_zero _ hKpos.ne'
  have hLpos : 0 < L := by linarith
  have hr : 0 < (9 : ℝ)/(20*K^2) := by positivity
  have ht : ∀ u : ℝ, 0 ≤ u → μ.real {ω | u < Y ω} ≤
      Real.sqrt 10*Real.exp (-((9/(20*K^2))*u)) := by
    intro u hu
    convert! htail u hu using 1 <;> congr 2 <;> ring
  have hcut := first_moment_cutoff hY hY0 (Real.sqrt_nonneg 10) hr
    (A := (15/2)*K^2*L) (by positivity) ht hmean 1
  let ε := Real.sqrt 10/(9/(20*K^2))*Real.exp (-((9/(20*K^2))*((15/2)*K^2*L)))
  have hcut' : (∫ ω, Y ω^2 ∂μ)/2 ≤ (15/4)*K^2*L+
      ε*((15/4)*K^2*L+(20/9)*K^2) := by
    convert! hcut using 1 <;>
      norm_num [tailMomentSeries, Finset.sum_range_succ, ε] <;> field_simp <;> ring
  have hε : ε ≤ (1/4 : ℝ)*Real.exp (-11*(L-1)/8) := by
    dsimp [ε]
    rw [cutoff_epsilon_identity hKpos hKL]
    exact cutoff_epsilon_bound L
  have hB : 0 < K^2*L := by positivity
  have hdiv := div_le_div_of_nonneg_right hcut' hB.le
  have hcost : (∫ ω, Y ω^2 ∂μ)/(2*K^2*L)-1/(2*K^2*L) ≤
      15/4+ε*(15/4+(20/9)/L)-(1/2)*(1/K^2)/L := by
    convert! sub_le_sub_right hdiv (1/(2*K^2*L)) using 1 <;>
      field_simp [hK2, hLpos.ne'] <;> ring
  have hpow : K^2 = Real.exp (2*(L-1)) := by
    rw [show 2*(L-1) = Real.log K+Real.log K by rw [hKL]; ring,
      Real.exp_add, Real.exp_log hKpos]
    ring
  have hinv : 1/K^2 = Real.exp (-2*(L-1)) := by
    rw [show -2*(L-1) = -(2*(L-1)) by ring, Real.exp_neg, ← hpow]
    simp [one_div]
  rw [hinv] at hcost
  have hεcost := mul_le_mul_of_nonneg_right hε
    (show 0 ≤ (15/4 : ℝ)+(20/9)/L by positivity)
  have hcost' : (∫ ω, Y ω^2 ∂μ)/(2*K^2*L)-1/(2*K^2*L) ≤
      upperSecondMomentCost L := by
    dsimp [upperSecondMomentCost]
    nlinarith
  exact ⟨by simpa using (exponential_tail_moment hY.aemeasurable hY0
    (Real.sqrt_nonneg 10) hr ht 1).1, hcost'.trans_lt (upperSecondMomentCost_lt hL)⟩

/-- The actual moment series is summable throughout the geometric range. -/
theorem upper_tail_moment_series_summable [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {K L t : ℝ}
    (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hK : 1 ≤ K)
    (hKL : L = 1+Real.log K) (hmean : (∫ ω, Y ω ∂μ) ≤ 1)
    (htail : ∀ u : ℝ, 0 ≤ u → μ.real {ω | u < Y ω} ≤
      Real.sqrt 10*Real.exp (-(9*u/(20*K^2))))
    (ht0 : 0 ≤ t) (ht : ((9/2)*K^2*L)*t < 1) :
    Summable (fun p : ℕ => ((∫ ω, Y ω^p ∂μ)/(p.factorial : ℝ))*t^p) := by
  let v : ℝ := (9/2)*K^2*L
  have hL : 1 ≤ L := by rw [hKL]; linarith [Real.log_nonneg hK]
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hgeo : Summable (fun n : ℕ => (v^2*t^3)*(v*t)^n) := by
    apply Summable.mul_left
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hv ht0)]
    exact ht
  have hs : Summable (fun n : ℕ => ((∫ ω, Y ω^(n+3) ∂μ)/((n+3).factorial : ℝ))*t^(n+3)) := by
    apply Summable.of_nonneg_of_le _ _ hgeo
    · intro n
      exact mul_nonneg (div_nonneg (integral_nonneg fun ω => pow_nonneg (hY0 ω) _)
        (by positivity)) (pow_nonneg ht0 _)
    · intro n
      have hm := (upper_tail_higher_moments hY hY0 hK hKL hmean htail (n+3) (by omega)).2
      have hh := mul_le_mul_of_nonneg_right hm (pow_nonneg ht0 (n+3))
      convert! hh using 1
      dsimp [v]
      simp only [Nat.add_sub_cancel_right, pow_add, mul_pow]
      ring
  exact (summable_nat_add_iff 3).1 hs

/-- Integrating the actual exponential series from finite moments and a
summable moment series. Nonnegative Taylor terms justify finiteness and the
interchange; exponential integrability is a conclusion. -/
theorem exp_integrable_and_eq_tsum_of_moments {Y : Ω → ℝ} {t : ℝ}
    (hY : AEMeasurable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω) (ht : 0 ≤ t)
    (hMom : ∀ p : ℕ, Integrable (fun ω => Y ω^p) μ)
    (hSum : Summable (fun p : ℕ => ((∫ ω, Y ω^p ∂μ)/(p.factorial : ℝ))*t^p)) :
    Integrable (fun ω => Real.exp (t*Y ω)) μ ∧
      (∫ ω, Real.exp (t*Y ω) ∂μ) =
        ∑' p : ℕ, ((∫ ω, Y ω^p ∂μ)/(p.factorial : ℝ))*t^p := by
  let F : ℕ → Ω → ℝ := fun p ω => (Y ω^p/(p.factorial : ℝ))*t^p
  have hF0 : ∀ p ω, 0 ≤ F p ω := fun p ω => by
    have hy0 := hY0 ω
    dsimp [F]
    positivity
  have hFi : ∀ p, Integrable (F p) μ := fun p => ((hMom p).div_const _).mul_const _
  have hIntegral : ∀ p, (∫ ω, F p ω ∂μ) = ((∫ ω, Y ω^p ∂μ)/(p.factorial : ℝ))*t^p := by
    intro p
    dsimp [F]
    rw [integral_mul_const, integral_div]
  have hPoint : ∀ ω, HasSum (fun p => F p ω) (Real.exp (t*Y ω)) := by
    intro ω
    have h : HasSum (fun p : ℕ => (t*Y ω)^p/(p.factorial : ℝ)) (Real.exp (t*Y ω)) := by
      simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (t*Y ω)
    convert! h using 1
    ext p
    dsimp [F]
    rw [mul_pow]
    ring
  have hSum' : Summable (fun p => ∫ ω, F p ω ∂μ) := by simpa only [hIntegral] using hSum
  have hFin : (∫⁻ ω, ENNReal.ofReal (Real.exp (t*Y ω)) ∂μ) ≠ ⊤ := by
    have heq : (fun ω => ENNReal.ofReal (Real.exp (t*Y ω))) =
        (fun ω => ∑' p : ℕ, ENNReal.ofReal (F p ω)) := by
      funext ω
      rw [← (hPoint ω).tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun p => hF0 p ω) (hPoint ω).summable]
    rw [heq, lintegral_tsum (fun p => (hFi p).aemeasurable.ennreal_ofReal)]
    have hEach : ∀ p, (∫⁻ ω, ENNReal.ofReal (F p ω) ∂μ) = ENNReal.ofReal (∫ ω, F p ω ∂μ) := by
      intro p
      exact (ofReal_integral_eq_lintegral_ofReal (hFi p)
        (Filter.Eventually.of_forall (hF0 p))).symm
    simp_rw [hEach]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun p => integral_nonneg (hF0 p)) hSum']
    exact ENNReal.ofReal_ne_top
  have hExp : Integrable (fun ω => Real.exp (t*Y ω)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable ((hY.const_mul t).exp.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)).1 hFin
  refine ⟨hExp, ?_⟩
  have hNorm : Summable (fun p => ∫ ω, ‖F p ω‖ ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 _ _)] using hSum'
  have heq := integral_tsum_of_summable_integral_norm hFi hNorm
  simp_rw [hIntegral, (hPoint _).tsum_eq] at heq
  exact heq.symm

/-- Actual exponential integrability and moment-series identity in the upper
Bernstein range. This includes `t=0` and proves every moment finite. -/
theorem upper_tail_mgf_integrable_and_eq [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {K L t : ℝ}
    (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hK : 1 ≤ K)
    (hKL : L = 1+Real.log K) (hmean : (∫ ω, Y ω ∂μ) ≤ 1)
    (htail : ∀ u : ℝ, 0 ≤ u → μ.real {ω | u < Y ω} ≤
      Real.sqrt 10*Real.exp (-(9*u/(20*K^2))))
    (ht0 : 0 ≤ t) (ht : ((9/2)*K^2*L)*t < 1) :
    Integrable (fun ω => Real.exp (t*Y ω)) μ ∧
      (∫ ω, Real.exp (t*Y ω) ∂μ) =
        ∑' p : ℕ, ((∫ ω, Y ω^p ∂μ)/(p.factorial : ℝ))*t^p := by
  apply exp_integrable_and_eq_tsum_of_moments hY.aemeasurable hY0 ht0
  · intro p
    cases p with
    | zero => simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ)
    | succ n =>
      have hKpos : 0 < K := by linarith
      have hr : 0 < (9 : ℝ)/(20*K^2) := by positivity
      apply (exponential_tail_moment hY.aemeasurable hY0 (Real.sqrt_nonneg 10) hr _ n).1
      intro u hu
      convert! htail u hu using 1 <;> congr 2 <;> ring
  · exact upper_tail_moment_series_summable hY hY0 hK hKL hmean htail ht0 ht

/-- Exponential integrability follows from the upper-tail moment theorem. -/
theorem upper_tail_mgf_integrable [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {K L t : ℝ}
    (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hK : 1 ≤ K)
    (hKL : L = 1+Real.log K) (hmean : (∫ ω, Y ω ∂μ) ≤ 1)
    (htail : ∀ u : ℝ, 0 ≤ u → μ.real {ω | u < Y ω} ≤
      Real.sqrt 10*Real.exp (-(9*u/(20*K^2))))
    (ht0 : 0 ≤ t) (ht : ((9/2)*K^2*L)*t < 1) :
    Integrable (fun ω => Real.exp (t*Y ω)) μ :=
  (upper_tail_mgf_integrable_and_eq hY hY0 hK hKL hmean htail ht0 ht).1

/-- The MGF is the actual sum of its finite moments throughout the geometric range. -/
theorem upper_tail_mgf_eq_tsum [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {K L t : ℝ}
    (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hK : 1 ≤ K)
    (hKL : L = 1+Real.log K) (hmean : (∫ ω, Y ω ∂μ) ≤ 1)
    (htail : ∀ u : ℝ, 0 ≤ u → μ.real {ω | u < Y ω} ≤
      Real.sqrt 10*Real.exp (-(9*u/(20*K^2))))
    (ht0 : 0 ≤ t) (ht : ((9/2)*K^2*L)*t < 1) :
    (∫ ω, Real.exp (t*Y ω) ∂μ) =
      ∑' p : ℕ, ((∫ ω, Y ω^p ∂μ)/(p.factorial : ℝ))*t^p :=
  (upper_tail_mgf_integrable_and_eq hY hY0 hK hKL hmean htail ht0 ht).2

end
end SingularValueBounds.KL
