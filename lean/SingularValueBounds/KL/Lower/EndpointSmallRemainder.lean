import SingularValueBounds.KL.Lower.EndpointBlocks

/-! # Endpoint spectra with a small perpendicular Frobenius norm

Supplementary S1.5, the branch `p≤3/20`, in which the canonical comparison
already gives the cost `73/50`.
-/

open scoped BigOperators Matrix
namespace SingularValueBounds.KL
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem endpoint_rest_third_le (r : ι → ℝ) (top : ι)
    (hr : ∀ i, 0 ≤ r i) (h2 : spectralMoment r 2 = 1) :
    endpointRestMoment r top 3 ≤
      Real.sqrt (1-r top^2)*endpointRestP r top := by
  have hs2 := endpointRestMoment_split r top 2
  rw [h2] at hs2
  have hr2 : 0 ≤ 1-r top^2 := by
    have := Finset.sum_nonneg (s := Finset.univ.erase top) (fun i _ => sq_nonneg (r i))
    change 0 ≤ endpointRestMoment r top 2 at this
    linarith
  have hc : endpointRestMoment r top 3 ^ 2 ≤
      endpointRestMoment r top 2*endpointRestMoment r top 4 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro i _
      positivity
    · intro i _
      positivity
    · intro i _
      ring
  have hp2 := endpointRestP_sq r top
  have hroot := Real.sq_sqrt hr2
  have hnonneg : 0 ≤ endpointRestMoment r top 3 :=
    Finset.sum_nonneg fun i _ => pow_nonneg (hr i) _
  have he : (Real.sqrt (1-r top^2)*endpointRestP r top)^2 =
      (1-r top^2)*endpointRestMoment r top 4 := by rw [mul_pow, hroot, hp2]
  have hprod : 0 ≤ Real.sqrt (1-r top^2)*endpointRestP r top := by
    dsimp [endpointRestP]
    positivity
  have hs2' : endpointRestMoment r top 2 = 1-r top^2 := by linarith
  rw [hs2'] at hc
  nlinarith only [hc, he, hprod, hnonneg]

theorem endpoint_rest_sixth_le (r : ι → ℝ) (top : ι)
    (h2 : spectralMoment r 2 = 1) :
    endpointRestMoment r top 6 ≤ (1-r top^2)*endpointRestMoment r top 4 := by
  have hb := Finset.sum_le_sum (s := Finset.univ.erase top)
    (f := fun i => r i^6) (g := fun i => (1-r top^2)*r i^4) (fun i hi => by
      have hr2 := normalized_other_square_le r top rfl h2 (Finset.mem_erase.mp hi).1
      have hmul := mul_le_mul_of_nonneg_right hr2 (show 0 ≤ r i^4 by positivity)
      change r i^6 ≤ (1-r top^2)*r i^4
      nlinarith only [hmul])
  simpa only [← Finset.mul_sum, endpointRestMoment] using hb

theorem endpoint_canonical_remainder_norm_bound (r : ι → ℝ) (top : ι)
    (hr : ∀ i, 0 ≤ r i) (h2 : spectralMoment r 2 = 1) :
    (∑ i, endpointComparisonEigen (r top) 1 (r i)^2) ≤
      1+2*r top*Real.sqrt (1-r top^2)*endpointRestP r top-endpointRestP r top^2 := by
  have h3 := endpoint_rest_third_le r top hr h2
  have h6 := endpoint_rest_sixth_le r top h2
  have h5 : r top^5 ≤ spectralMoment r 5 :=
    Finset.single_le_sum (fun i _ => pow_nonneg (hr i) _) (Finset.mem_univ top)
  have hs3 := endpointRestMoment_split r top 3
  have hs4 := endpointRestMoment_split r top 4
  have hs6 := endpointRestMoment_split r top 6
  have hp2 := endpointRestP_sq r top
  have hn := endpointComparisonEigen_sq_sum r (r top) 1
  rw [h2] at hn
  have h3mul := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 2*r top from mul_nonneg (by norm_num) (hr top))
  have h5mul := mul_le_mul_of_nonneg_left h5 (show 0 ≤ 2*r top from mul_nonneg (by norm_num) (hr top))
  rw [hs3,hs4,hs6,← hp2] at hn
  rw [← hp2] at h6
  nlinarith only [hn, h6, h3mul, h5mul]

set_option maxHeartbeats 800000 in
/-- The small-perpendicular-block certificate, with its strict rational
rounding proved in Lean. No external numerical premise is needed. -/
theorem endpoint_small_remainder_cost (r : ι → ℝ) (top : ι)
    (hr : ∀ i, 0 ≤ r i) (h2 : spectralMoment r 2 = 1)
    (hk : r top ≤ 7/9) (hp : endpointRestP r top ≤ 3/20) :
    endpointOrdinaryCost r (r top) 1 < 73/50 := by
  let k := r top
  let p := endpointRestP r top
  have hk0 : 0 ≤ k := hr top
  have hp0 : 0 ≤ p := Real.sqrt_nonneg _
  have hk1 : k ≤ 1 := by linarith
  have hk2 : 0 ≤ 1-k^2 := by nlinarith
  have hp2 := endpointRestP_sq r top
  have hs4 := endpointRestMoment_split r top 4
  have hs4eq : spectralMoment r 4 = k^4+p^2 := by nlinarith only [hs4,hp2]
  have hs40 : 0 ≤ spectralMoment r 4 := Finset.sum_nonneg fun i _ => by positivity
  have hn0 : 0 ≤ ∑ i, endpointComparisonEigen k 1 (r i)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hn := endpoint_canonical_remainder_norm_bound r top hr h2
  have hroot := Real.sq_sqrt hk2
  have hcross : 2*k*Real.sqrt (1-k^2) ≤ 1 := by
    have he : (2*k*Real.sqrt (1-k^2))^2 = 4*k^2*(1-k^2) := by rw [mul_pow,mul_pow,hroot]; ring
    nlinarith [sq_nonneg (2*k^2-1)]
  have hn' : (∑ i, endpointComparisonEigen k 1 (r i)^2) ≤ 1+p-p^2 := by
    have hc := mul_le_mul_of_nonneg_right hcross hp0
    nlinarith only [hn,hc]
  have hpmax : p^2 ≤ (3/20 : ℝ)^2 := by nlinarith
  have hkmax : k^4 ≤ (7/9 : ℝ)^4 := by nlinarith [sq_nonneg (k^2-(7/9 : ℝ)^2)]
  have hfac1 : spectralMoment r 4 ≤ (7/9 : ℝ)^4+(3/20 : ℝ)^2 := by linarith
  have hfac2 : 1+p-p^2 ≤ 1+(3/20 : ℝ)-(3/20 : ℝ)^2 := by nlinarith
  have hprod : spectralMoment r 4*(∑ i, endpointComparisonEigen k 1 (r i)^2) ≤
      ((7/9 : ℝ)^4+(3/20 : ℝ)^2)*(1+(3/20 : ℝ)-(3/20 : ℝ)^2) := by
    exact mul_le_mul hfac1 (hn'.trans hfac2) hn0 (by norm_num)
  let gap : ℝ := 73/50-7/9-(7/9)*(3/20)^2
  have hgap : 0 < gap := by norm_num [gap]
  have hfinite : ((7/9 : ℝ)^4+(3/20 : ℝ)^2)*(1+(3/20 : ℝ)-(3/20 : ℝ)^2) < gap^2 := by
    norm_num [gap]
  have hrootprod : Real.sqrt (spectralMoment r 4)*
      Real.sqrt (∑ i, endpointComparisonEigen k 1 (r i)^2) < gap := by
    have he : (Real.sqrt (spectralMoment r 4)*Real.sqrt (∑ i, endpointComparisonEigen k 1 (r i)^2))^2 =
        spectralMoment r 4*(∑ i, endpointComparisonEigen k 1 (r i)^2) := by
      rw [mul_pow, Real.sq_sqrt hs40, Real.sq_sqrt hn0]
    apply (sq_lt_sq₀ (by positivity) hgap.le).mp
    rw [he]
    exact hprod.trans_lt hfinite
  have h5 : k^5 ≤ spectralMoment r 5 :=
    Finset.single_le_sum (fun i _ => pow_nonneg (hr i) _) (Finset.mem_univ top)
  have hkpmul := mul_le_mul hpmax hk hk0 (by norm_num : (0 : ℝ) ≤ (3/20)^2)
  have hks4 : k*spectralMoment r 4 = k^5+k*p^2 := by rw [hs4eq]; ring
  dsimp [endpointOrdinaryCost]
  norm_num only [sub_self, zero_mul, add_zero, one_mul]
  dsimp [gap] at hrootprod
  nlinarith only [hrootprod,h5,hks4,hkpmul,hk]

end
end SingularValueBounds.KL
