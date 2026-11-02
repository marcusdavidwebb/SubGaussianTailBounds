import SingularValueBounds.KL.Lower.Shape

/-! Positive logarithmic series and the continuous lower-shape envelope. -/
open scoped BigOperators
open Set
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 800000

theorem lowerJ_hasSum {q : ℝ} (hq : |q| < 1) :
    HasSum (fun n : ℕ => q^(n+2)/(n+2 : ℝ)) (lowerJ q) := by
  have h := (hasSum_nat_add_iff' 1).2 (Real.hasSum_pow_div_log_of_abs_lt_one hq)
  norm_num [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one,Nat.add_assoc,add_assoc] at h
  exact h

theorem lowerJ_div_hasSum {q : ℝ} (hq0 : 0 < q) (hq : q < 1) :
    HasSum (fun n : ℕ => q^(n+2)/(n+3 : ℝ)) (lowerJ q/q-q/2) := by
  have hJ := lowerJ_hasSum (show |q| < 1 by rwa [abs_of_pos hq0])
  have ht := ((hasSum_nat_add_iff' 1).2 hJ).div_const q
  have ht' : HasSum (fun n : ℕ => q^(n+2)/(n+3 : ℝ))
      (lowerJ q/q-q/2) := by
    convert! ht using 1
    · ext n
      norm_num only [Nat.cast_add,Nat.cast_one,Finset.sum_range_succ] at *
      simp only [show n+1+2 = n+2+1 by omega,pow_succ]
      field_simp [hq0.ne']
      <;> ring
    · simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,zero_add,
        zero_add,pow_two]
      field_simp [hq0.ne']
      <;> ring
  exact ht'

theorem lowerM_hasSum {q : ℝ} (hq0 : 0 < q) (hq : q < 1) :
    HasSum (fun n : ℕ => 2*q^(n+2)/((n+2 : ℝ)*(n+3 : ℝ))) (lowerM q) := by
  have hJ := lowerJ_hasSum (show |q| < 1 by rwa [abs_of_pos hq0])
  have ht' := lowerJ_div_hasSum hq0 hq
  have hs := (hJ.sub ht').mul_left 2
  convert! hs using 1
  · ext n
    have hn : (n+2 : ℝ) ≠ 0 := by positivity
    have hn' : (n+3 : ℝ) ≠ 0 := by positivity
    field_simp
    <;> ring
  · unfold lowerM
    field_simp
    <;> ring

theorem lowerJ_scaled_hasSum {u k : ℝ} (hk : k ≠ 0) (huk : |u*k| < 1) :
    HasSum (fun n : ℕ => u^(n+2)*k^n/(n+2 : ℝ)) (lowerJ (u*k)/k^2) := by
  convert! (lowerJ_hasSum huk).div_const (k^2) using 1
  ext n
  rw [mul_pow,pow_add k n 2]
  field_simp

theorem lowerM_scaled_hasSum {u k : ℝ} (hu : 0 < u) (hk : 0 < k) (huk : u*k < 1) :
    HasSum (fun n : ℕ => 2*u^(n+2)*k^n/((n+2 : ℝ)*(n+3 : ℝ)))
      (lowerM (u*k)/k^2) := by
  convert! (lowerM_hasSum (mul_pos hu hk) huk).div_const (k^2) using 1
  ext n
  rw [mul_pow,pow_add k n 2]
  field_simp

theorem lowerJ_scaled_mono {u v k l : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hk : 0 < k) (hkl : k ≤ l) (hvl : v*l < 1) :
    lowerJ (u*k)/k^2 ≤ lowerJ (v*l)/l^2 := by
  have hl := hk.trans_le hkl
  have hv := hu.trans huv
  have huk : u*k < 1 := (mul_le_mul huv hkl hk.le hv).trans_lt hvl
  apply hasSum_le _ (lowerJ_scaled_hasSum hk.ne' (by rwa [abs_of_nonneg (mul_nonneg hu hk.le)]))
    (lowerJ_scaled_hasSum hl.ne' (by rwa [abs_of_nonneg (mul_nonneg hv hl.le)]))
  intro n
  exact div_le_div_of_nonneg_right
    (mul_le_mul (pow_le_pow_left₀ hu huv _) (pow_le_pow_left₀ hk.le hkl _)
      (pow_nonneg hk.le _) (pow_nonneg hv _)) (by positivity)

theorem lowerM_scaled_mono {u v k l : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hk : 0 < k) (hkl : k ≤ l) (hvl : v*l < 1) :
    lowerM (u*k)/k^2 ≤ lowerM (v*l)/l^2 := by
  have hl := hk.trans_le hkl
  have hv := hu.trans_le huv
  have huk : u*k < 1 := (mul_le_mul huv hkl hk.le hv.le).trans_lt hvl
  apply hasSum_le _ (lowerM_scaled_hasSum hu hk huk) (lowerM_scaled_hasSum hv hl hvl)
  intro n
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left
      (mul_le_mul (pow_le_pow_left₀ hu.le huv _) (pow_le_pow_left₀ hk.le hkl _)
        (pow_nonneg hk.le _) (pow_nonneg hv.le _)) (by norm_num : (0 : ℝ) ≤ 2))

theorem lowerM_partial_le {q : ℝ} (hq0 : 0 < q) (hq : q < 1) (N : ℕ) :
    (∑ n ∈ Finset.range N,2*q^(n+2)/((n+2 : ℝ)*(n+3 : ℝ))) ≤ lowerM q :=
  sum_le_hasSum _ (by intros; positivity) (lowerM_hasSum hq0 hq)

theorem lowerM_quadratic_le {q : ℝ} (hq0 : 0 < q) (hq : q < 1) :
    q^2/3 ≤ lowerM q := by
  have h := lowerM_partial_le hq0 hq 1
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lowerM_lt_log_ratio {q : ℝ} (hq0 : 0 < q) (hq : q < 1) :
    lowerM q < lowerJ q/q-q/2 := by
  have hs := (lowerJ_div_hasSum hq0 hq).sub (lowerM_hasSum hq0 hq)
  have hpos (n : ℕ) : 0 ≤ q^(n+2)/(n+3 : ℝ)-2*q^(n+2)/((n+2 : ℝ)*(n+3 : ℝ)) := by
    have hn : (0 : ℝ) < n+2 := by positivity
    have hn' : (0 : ℝ) < n+3 := by positivity
    rw [sub_nonneg]
    apply (div_le_iff₀ (mul_pos hn hn')).2
    have hid : q^(n+2)/(n+3 : ℝ)*((n+2 : ℝ)*(n+3 : ℝ)) = q^(n+2)*(n+2 : ℝ) := by
      field_simp [hn'.ne']
    rw [hid]
    nlinarith [pow_nonneg hq0.le (n+2),mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (pow_nonneg hq0.le (n+2))]
  have h := sum_le_hasSum (Finset.range 2) (fun n _ => hpos n) hs
  norm_num [Finset.sum_range_succ] at h
  have : 0 < q^3/12 := by positivity
  linarith

theorem lower_shape_envelope {u k : ℝ} (hu : 0 < u) (hk : 0 < k)
    (hk1 : k ≤ 1) (huk : u*k < 1) (hM : k^2 < lowerM (u*k))
    {r : ℝ} (hr : r ∈ Icc (0:ℝ) k) :
    -Real.log (1-u*lowerShapeEigenvalue k r)-u*r ≤ (lowerJ (u*k)/k^2)*r^2 := by
  let c := lowerJ (u*k)/k^2
  have hq := mul_pos hu hk
  have hJ := lowerJ_pos hq huk
  have hc : 0 < c := div_pos hJ (sq_pos_of_pos hk)
  have hcdef : c*k^2 = lowerJ (u*k) := div_mul_cancel₀ _ (pow_ne_zero 2 hk.ne')
  have hJM := lowerM_lt_log_ratio hq huk
  have heleft : k^2*(2*c-u^2-2*u*k) =
      2*(u*k)*(lowerJ (u*k)/(u*k)-u*k/2-k^2) := by
    dsimp [c]
    field_simp
  have hleft : 0 < 2*c-u^2-2*u*k := by
    have hdelta : 0 < lowerJ (u*k)/(u*k)-u*k/2-k^2 := by linarith
    have h : 0 < k^2*(2*c-u^2-2*u*k) := by rw [heleft]; positivity
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hk)).1 h
  have heright : k^2*((2*c-u^2-2*u*k)+(3*u-u^2*k-2*u*c)*k+
      (u^2-2*u*c*k)*k^2+2*u*c*k^3) = u*k*(k^2-lowerM (u*k)) := by
    dsimp [c,lowerM]
    field_simp
    <;> ring
  have hright : (2*c-u^2-2*u*k)+(3*u-u^2*k-2*u*c)*k+
      (u^2-2*u*c*k)*k^2+2*u*c*k^3 < 0 := by
    have h : k^2*((2*c-u^2-2*u*k)+(3*u-u^2*k-2*u*c)*k+
        (u^2-2*u*c*k)*k^2+2*u*c*k^3) < 0 := by
      rw [heright]
      exact mul_neg_of_pos_of_neg hq (sub_neg.mpr hM)
    exact neg_of_mul_neg_right h (sq_nonneg k)
  exact lower_shape_envelope_of_cubic hu hk hk1 huk hc hcdef hleft hright hr

end
end SingularValueBounds.KL
