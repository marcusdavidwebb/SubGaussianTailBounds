import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Set Finset
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Normalizing denominator for the upper-tail spectral weights. -/
def shiftedWeightNormalizer (ρ : ι → ℝ) (H : ℝ) : ℝ :=
  ∑ i, ρ i^2/(1+H*ρ i)

/-- The shifted spectral probability vector. -/
def normalizedShiftWeight (ρ : ι → ℝ) (H : ℝ) (i : ι) : ℝ :=
  (ρ i^2/(1+H*ρ i))/shiftedWeightNormalizer ρ H

/-- The unnormalised spectral weight increases with the spectral coordinate. -/
theorem unnormalizedShiftWeight_mono {a b H : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hH : 0 ≤ H) :
    a^2/(1+H*a) ≤ b^2/(1+H*b) := by
  have hb : 0 ≤ b := ha.trans hab
  apply (div_le_div_iff₀ (by positivity : 0 < 1+H*a) (by positivity : 0 < 1+H*b)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ a+b+H*a*b by positivity)]

/-- Denominator bounds, positivity, and normalization, including zero coordinates. -/
theorem normalizedShiftWeight_properties {ρ : ι → ℝ} {H κ : ℝ}
    (hρ : ∀ i, 0 ≤ ρ i) (hSum : (∑ i, ρ i^2) = 1)
    (hH : 0 ≤ H) (hκ : 0 ≤ κ) (hBound : ∀ i, ρ i ≤ κ) :
    1/(1+H*κ) ≤ shiftedWeightNormalizer ρ H ∧
    shiftedWeightNormalizer ρ H ≤ 1 ∧
    0 < shiftedWeightNormalizer ρ H ∧
    (∀ i, 0 ≤ normalizedShiftWeight ρ H i) ∧
    (∑ i, normalizedShiftWeight ρ H i) = 1 := by
  have hlo : 1/(1+H*κ) ≤ shiftedWeightNormalizer ρ H := by
    rw [← hSum, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    have hiρ := hρ i
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (by nlinarith [hBound i])
  have hup : shiftedWeightNormalizer ρ H ≤ 1 := by
    rw [← hSum]
    apply Finset.sum_le_sum
    intro i hi
    have hiρ := hρ i
    exact (div_le_iff₀ (by positivity : 0 < 1+H*ρ i)).2
      (by nlinarith [mul_nonneg (sq_nonneg (ρ i)) (mul_nonneg hH (hρ i))])
  have hz : 0 < shiftedWeightNormalizer ρ H := lt_of_lt_of_le (by positivity) hlo
  refine ⟨hlo, hup, hz, fun i => by have hiρ := hρ i; dsimp [normalizedShiftWeight]; positivity, ?_⟩
  simp only [normalizedShiftWeight, ← Finset.sum_div]
  exact div_self hz.ne'

/-- A common crossing level: each shifted weight lies between its original
weight and one fixed nonnegative level. This proves the convex majorization
comparison without a separate sorting convention. -/
theorem normalizedShiftWeight_crossing {ρ : ι → ℝ} {H κ : ℝ}
    (hρ : ∀ i, 0 ≤ ρ i) (hSum : (∑ i, ρ i^2) = 1)
    (hH : 0 ≤ H) (hκ : 0 ≤ κ) (hBound : ∀ i, ρ i ≤ κ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ i,
      (ρ i^2 ≤ normalizedShiftWeight ρ H i ∧ normalizedShiftWeight ρ H i ≤ T) ∨
      (T ≤ normalizedShiftWeight ρ H i ∧ normalizedShiftWeight ρ H i ≤ ρ i^2) := by
  have hz := normalizedShiftWeight_properties hρ hSum hH hκ hBound
  by_cases hHz : H = 0
  · refine ⟨0, le_rfl, fun i => Or.inr ?_⟩
    simp [normalizedShiftWeight, shiftedWeightNormalizer, hHz, hSum, sq_nonneg]
  have hHp : 0 < H := lt_of_le_of_ne hH (Ne.symm hHz)
  let Z := shiftedWeightNormalizer ρ H
  let t := (1-Z)/(H*Z)
  have hZ : 0 < Z := hz.2.2.1
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hz.2.1) (mul_nonneg hH hZ.le)
  have hcross : 1+H*t = 1/Z := by dsimp [t]; field_simp [hHp.ne', hZ.ne']; ring
  have hden : ∀ x : ℝ, 0 ≤ x → 0 < 1+H*x := fun x hx => by positivity
  have hvalue : (t^2/(1+H*t))/Z = t^2 := by rw [hcross]; field_simp [hZ.ne']
  refine ⟨t^2, sq_nonneg _, fun i => ?_⟩
  by_cases hi : ρ i ≤ t
  · left
    have hd : (1+H*ρ i)*Z ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_right hi (mul_nonneg hH hZ.le)
      have hidentity : (1+H*t)*Z = 1 := by rw [hcross]; field_simp [hZ.ne']
      nlinarith
    constructor
    · dsimp [normalizedShiftWeight]
      change ρ i^2 ≤ (ρ i^2/(1+H*ρ i))/Z
      apply (le_div_iff₀ hZ).2
      apply (le_div_iff₀ (hden _ (hρ i))).2
      nlinarith [mul_le_mul_of_nonneg_left hd (sq_nonneg (ρ i))]
    · have hm := div_le_div_of_nonneg_right (unnormalizedShiftWeight_mono (hρ i) hi hH) hZ.le
      simpa [normalizedShiftWeight, Z, hvalue] using hm
  · right
    have hi' : t ≤ ρ i := le_of_not_ge hi
    have hd : 1 ≤ (1+H*ρ i)*Z := by
      have hmul := mul_le_mul_of_nonneg_right hi' (mul_nonneg hH hZ.le)
      have hidentity : (1+H*t)*Z = 1 := by rw [hcross]; field_simp [hZ.ne']
      nlinarith
    constructor
    · have hm := div_le_div_of_nonneg_right (unnormalizedShiftWeight_mono ht hi' hH) hZ.le
      simpa [normalizedShiftWeight, Z, hvalue] using hm
    · dsimp [normalizedShiftWeight]
      change (ρ i^2/(1+H*ρ i))/Z ≤ ρ i^2
      apply (div_le_iff₀ hZ).2
      apply (div_le_iff₀ (hden _ (hρ i))).2
      nlinarith [mul_le_mul_of_nonneg_left hd (sq_nonneg (ρ i))]

private theorem convex_tangent_upper {f : ℝ → ℝ} {p q d : ℝ}
    (hf : ConvexOn ℝ (Ici 0) f) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hd : HasDerivAt f d p) : f p-f q ≤ d*(p-q) := by
  rcases lt_trichotomy p q with hpq | rfl | hqp
  · have h := hf.le_slope_of_hasDerivAt hp hq hpq hd
    rw [slope_def_field] at h
    have hh := (le_div_iff₀ (sub_pos.mpr hpq)).1 h
    nlinarith
  · simp
  · have h := hf.slope_le_of_hasDerivAt hq hp hqp hd
    rw [slope_def_field] at h
    have hh := (div_le_iff₀ (sub_pos.mpr hqp)).1 h
    nlinarith

/-- Convex majorization for the actual normalized shifted spectral vector. -/
theorem normalizedShiftWeight_convex_sum {ρ : ι → ℝ} {H κ : ℝ} {f f' : ℝ → ℝ}
    (hρ : ∀ i, 0 ≤ ρ i) (hSum : (∑ i, ρ i^2) = 1)
    (hH : 0 ≤ H) (hκ : 0 ≤ κ) (hBound : ∀ i, ρ i ≤ κ)
    (hf : ConvexOn ℝ (Ici 0) f) (hderiv : ∀ x : ℝ, 0 ≤ x → HasDerivAt f (f' x) x) :
    (∑ i, f (normalizedShiftWeight ρ H i)) ≤ ∑ i, f (ρ i^2) := by
  have hp := normalizedShiftWeight_properties hρ hSum hH hκ hBound
  obtain ⟨T, hT, hcross⟩ := normalizedShiftWeight_crossing hρ hSum hH hκ hBound
  have hmono : MonotoneOn f' (Ici 0) := by
    intro x hx y hy hxy
    have h := hf.monotoneOn_deriv (fun u hu => (hderiv u hu).differentiableAt) hx hy hxy
    simpa only [(hderiv x hx).deriv, (hderiv y hy).deriv] using h
  have hpoint : ∀ i, f (normalizedShiftWeight ρ H i)-f (ρ i^2) ≤
      f' T*(normalizedShiftWeight ρ H i-ρ i^2) := by
    intro i
    have htangent := convex_tangent_upper hf (hp.2.2.2.1 i) (sq_nonneg (ρ i)) (hderiv _ (hp.2.2.2.1 i))
    rcases hcross i with hi | hi
    · exact htangent.trans (mul_le_mul_of_nonneg_right
        (hmono (hp.2.2.2.1 i) hT hi.2) (sub_nonneg.mpr hi.1))
    · exact htangent.trans (mul_le_mul_of_nonpos_right
        (hmono hT (hp.2.2.2.1 i) hi.1) (sub_nonpos.mpr hi.2))
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i hi => hpoint i)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hp.2.2.2.2, hSum] at h
  linarith

/-- All convex power sums decrease under the spectral shift. -/
theorem normalizedShiftWeight_power_sum {ρ : ι → ℝ} {H κ : ℝ}
    (hρ : ∀ i, 0 ≤ ρ i) (hSum : (∑ i, ρ i^2) = 1)
    (hH : 0 ≤ H) (hκ : 0 ≤ κ) (hBound : ∀ i, ρ i ≤ κ) (r : ℕ) :
    (∑ i, normalizedShiftWeight ρ H i^r) ≤ ∑ i, ρ i^(2*r) := by
  have h := normalizedShiftWeight_convex_sum hρ hSum hH hκ hBound
    (convexOn_pow r) (fun x hx => hasDerivAt_pow r x)
  simpa only [← pow_mul] using h

/-- Every subset consisting of largest spectral coordinates has no larger
shifted mass than original mass. In particular this applies to every initial
partial sum after decreasing rearrangement. -/
theorem normalizedShiftWeight_top_sum {ρ : ι → ℝ} {H κ : ℝ}
    (hρ : ∀ i, 0 ≤ ρ i) (hSum : (∑ i, ρ i^2) = 1)
    (hH : 0 ≤ H) (hκ : 0 ≤ κ) (hBound : ∀ i, ρ i ≤ κ)
    (S : Finset ι) (hTop : ∀ i ∈ S, ∀ j ∉ S, ρ j ≤ ρ i) :
    (∑ i ∈ S, normalizedShiftWeight ρ H i) ≤ ∑ i ∈ S, ρ i^2 := by
  have hz := (normalizedShiftWeight_properties hρ hSum hH hκ hBound).2.2.1
  let a := ∑ i ∈ S, ρ i^2
  let b := ∑ i ∈ S, ρ i^2/(1+H*ρ i)
  let Z := shiftedWeightNormalizer ρ H
  have hq : (∑ j ∈ Sᶜ, ρ j^2) = 1-a := by
    have h := Finset.sum_add_sum_compl S (fun i => ρ i^2)
    rw [hSum] at h
    dsimp [a]
    linarith
  have hn : (∑ j ∈ Sᶜ, ρ j^2/(1+H*ρ j)) = Z-b := by
    have h := Finset.sum_add_sum_compl S (fun i => ρ i^2/(1+H*ρ i))
    change b+(∑ j ∈ Sᶜ, ρ j^2/(1+H*ρ j)) = Z at h
    linarith
  have hcross : b*(∑ j ∈ Sᶜ, ρ j^2) ≤ a*(∑ j ∈ Sᶜ, ρ j^2/(1+H*ρ j)) := by
    dsimp [a, b]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hiρ := hρ i
    have hjρ := hρ j
    have hij := hTop i hi j (Finset.mem_compl.mp hj)
    have hdiv := div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg (ρ i)) (sq_nonneg (ρ j)))
      (show 0 < 1+H*ρ j by positivity) (show 1+H*ρ j ≤ 1+H*ρ i by nlinarith)
    convert hdiv using 1 <;> ring
  rw [hq, hn] at hcross
  simp only [normalizedShiftWeight, ← Finset.sum_div]
  change b/Z ≤ a
  apply (div_le_iff₀ hz).2
  nlinarith

/-- The shifted weights obey the same maximum-coordinate cap. -/
theorem normalizedShiftWeight_le_shape {ρ : ι → ℝ} {H κ : ℝ}
    (hρ : ∀ i, 0 ≤ ρ i) (hSum : (∑ i, ρ i^2) = 1)
    (hH : 0 ≤ H) (hκ : 0 ≤ κ) (hBound : ∀ i, ρ i ≤ κ) (i : ι) :
    normalizedShiftWeight ρ H i ≤ κ^2 := by
  have hz := normalizedShiftWeight_properties hρ hSum hH hκ hBound
  have hden : 0 < 1+H*κ := by positivity
  have hZ := (div_le_iff₀ hden).1 hz.1
  change (ρ i^2/(1+H*ρ i))/shiftedWeightNormalizer ρ H ≤ κ^2
  apply (div_le_iff₀ hz.2.2.1).2
  calc
    _ ≤ κ^2/(1+H*κ) := unnormalizedShiftWeight_mono (hρ i) (hBound i) hH
    _ ≤ κ^2*shiftedWeightNormalizer ρ H := (div_le_iff₀ hden).2 (by
      nlinarith [mul_le_mul_of_nonneg_left hZ (sq_nonneg κ)])

/-- The normalized third moment and maximal coordinate control every higher
spectral moment, with precisely the exponent used in the joint prefactor. -/
theorem normalizedShiftWeight_power_sum_shape {ρ : ι → ℝ} {H κ : ℝ}
    (hρ : ∀ i, 0 ≤ ρ i) (hSum : (∑ i, ρ i^2) = 1)
    (hH : 0 ≤ H) (hκ : 0 ≤ κ) (hBound : ∀ i, ρ i ≤ κ)
    (r : ℕ) (hr : 2 ≤ r) :
    (∑ i, normalizedShiftWeight ρ H i^r) ≤ (∑ i, ρ i^3)*κ^(2*r-3) := by
  apply (normalizedShiftWeight_power_sum hρ hSum hH hκ hBound r).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  calc
    ρ i^(2*r) = ρ i^3*ρ i^(2*r-3) := by rw [← pow_add]; congr 1; omega
    _ ≤ ρ i^3*κ^(2*r-3) := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hρ i) (hBound i) _) (pow_nonneg (hρ i) _)

private theorem hasSum_log_remainder {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => x^(n+2)/(n+2 : ℝ)) (-Real.log (1-x)-x) := by
  have h := (hasSum_nat_add_iff' 1).2 (Real.hasSum_pow_div_log_of_abs_lt_one hx)
  norm_num [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc] at h
  exact h

private theorem shape_power_term_identity {q κ a : ℝ} (hκ : κ ≠ 0) (m : ℕ) (hm : 2 ≤ m) :
    (q^m/(m : ℝ))*(a*κ^(2*m-3)) = (a/κ^3)*((q*κ^2)^m/(m : ℝ)) := by
  have he : κ^(2*m-3)*κ^3 = κ^(2*m) := by rw [← pow_add]; congr 1; omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  apply mul_right_cancel₀ (pow_ne_zero 3 hκ)
  calc
    _ = (q^m/(m : ℝ))*a*(κ^(2*m-3)*κ^3) := by ring
    _ = (q^m/(m : ℝ))*a*κ^(2*m) := by rw [he]
    _ = _ := by
      rw [mul_pow, ← pow_mul]
      field_simp
      <;> ring

/-- The joint determinant prefactor from the complete convergent logarithmic
series, with all higher spectral moments controlled by the third moment. -/
theorem normalizedShiftWeight_log_prefactor {ρ : ι → ℝ} {H κ q : ℝ}
    (hρ : ∀ i, 0 ≤ ρ i) (hSum : (∑ i, ρ i^2) = 1)
    (hH : 0 ≤ H) (hκ : 0 < κ) (hBound : ∀ i, ρ i ≤ κ)
    (hq : 0 ≤ q) (hqκ : q*κ^2 < 1) :
    -(∑ i, Real.log (1-q*normalizedShiftWeight ρ H i)) ≤
      q+((∑ i, ρ i^3)/κ^3)*(-Real.log (1-q*κ^2)-q*κ^2) := by
  have hp := normalizedShiftWeight_properties hρ hSum hH hκ.le hBound
  have hqp : ∀ i, |q*normalizedShiftWeight ρ H i| < 1 := by
    intro i
    rw [abs_of_nonneg (mul_nonneg hq (hp.2.2.2.1 i))]
    exact (mul_le_mul_of_nonneg_left (normalizedShiftWeight_le_shape hρ hSum hH hκ.le hBound i) hq).trans_lt hqκ
  have hkabs : |q*κ^2| < 1 := by rwa [abs_of_nonneg (mul_nonneg hq (sq_nonneg κ))]
  have hs := hasSum_sum (s := Finset.univ) (fun i hi => hasSum_log_remainder (hqp i))
  have hu := (hasSum_log_remainder hkabs).mul_left ((∑ i, ρ i^3)/κ^3)
  have hterm : ∀ n : ℕ,
      (∑ i, (q*normalizedShiftWeight ρ H i)^(n+2)/(n+2 : ℝ)) ≤
        ((∑ i, ρ i^3)/κ^3)*((q*κ^2)^(n+2)/(n+2 : ℝ)) := by
    intro n
    have hm := normalizedShiftWeight_power_sum_shape hρ hSum hH hκ.le hBound (n+2) (by omega)
    have hn0 : (0 : ℝ) ≤ q^(n+2)/(n+2 : ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_left hm hn0
    have hident := shape_power_term_identity (q := q) (a := ∑ i, ρ i^3) hκ.ne' (n+2) (by omega)
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at hident
    rw [hident] at h
    convert h using 1
    simp only [mul_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have h := hasSum_le hterm hs hu
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, hp.2.2.2.2] at h
  nlinarith

/-- The same prefactor controls any smaller nonnegative determinant arguments,
including the rescaled shifted-squared-resolvent eigenvalues in the joint tail. -/
theorem normalizedShiftWeight_log_prefactor_of_le {ρ v : ι → ℝ} {H κ q : ℝ}
    (hρ : ∀ i, 0 ≤ ρ i) (hSum : (∑ i, ρ i^2) = 1)
    (hH : 0 ≤ H) (hκ : 0 < κ) (hBound : ∀ i, ρ i ≤ κ)
    (hq : 0 ≤ q) (hqκ : q*κ^2 < 1)
    (hv : ∀ i, 0 ≤ v i) (hvp : ∀ i, v i ≤ q*normalizedShiftWeight ρ H i) :
    -(∑ i, Real.log (1-v i)) ≤
      q+((∑ i, ρ i^3)/κ^3)*(-Real.log (1-q*κ^2)-q*κ^2) := by
  apply le_trans _ (normalizedShiftWeight_log_prefactor hρ hSum hH hκ hBound hq hqκ)
  apply neg_le_neg
  apply Finset.sum_le_sum
  intro i hi
  have hcap := normalizedShiftWeight_le_shape hρ hSum hH hκ.le hBound i
  apply Real.log_le_log
  · nlinarith [mul_le_mul_of_nonneg_left hcap hq]
  · linarith [hvp i]

end
end SingularValueBounds.KL
