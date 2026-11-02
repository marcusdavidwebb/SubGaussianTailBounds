import SingularValueBounds.KL.Lower.EndpointBlocks

/-! # Endpoint perpendicular-block norm and covariance-ratio bounds -/

open scoped BigOperators Matrix
namespace SingularValueBounds.KL
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma endpoint_eigen_le_five_fourths {A c x : ℝ}
    (hc : 0 < c) (hA : A^2 ≤ c) (hx : 0 ≤ x) :
    endpointComparisonEigen A c x ≤ (5/4)*x := by
  have hs := sq_nonneg (A-2*c*x)
  have hq : A*x-c*x^2 ≤ 1/4 := by
    nlinarith only [hs,hA,hc]
  have hm := mul_le_mul_of_nonneg_left hq hx
  dsimp [endpointComparisonEigen]
  nlinarith only [hm]

theorem endpoint_rest_q_lt (r : ι → ℝ) (top : ι) {A c : ℝ}
    (hr : ∀ i, 0 ≤ r i) (h2 : spectralMoment r 2 = 1)
    (hk : 73/100 ≤ r top) (hc : 0 < c) (hA : A^2 ≤ c)
    (hf : ∀ i, 0 ≤ endpointComparisonEigen A c (r i)) :
    endpointRestQ r top A c < 6/7 := by
  have hs := Finset.sum_le_sum (s := Finset.univ.erase top)
    (f := fun i => endpointComparisonEigen A c (r i)^2)
    (g := fun i => (25/16)*r i^2) (fun i _ => by
      have hfi := hf i
      have hri := hr i
      have he := endpoint_eigen_le_five_fourths hc hA (hr i)
      nlinarith [mul_nonneg (sub_nonneg.mpr he)
        (show 0 ≤ (5/4)*r i+endpointComparisonEigen A c (r i) by positivity)])
  rw [← Finset.mul_sum] at hs
  have he2 := endpointRestMoment_split r top 2
  rw [h2] at he2
  have hr2 : endpointRestMoment r top 2 = 1-r top^2 := by linarith
  change (∑ i ∈ Finset.univ.erase top, endpointComparisonEigen A c (r i)^2) ≤
    (25/16)*endpointRestMoment r top 2 at hs
  rw [hr2, ← endpointRestQ_sq] at hs
  have hq0 : 0 ≤ endpointRestQ r top A c := Real.sqrt_nonneg _
  nlinarith only [hs,hk,hq0]

lemma endpoint_eigen_ratio_monotone {k x A c : ℝ}
    (hk : 0 ≤ k) (hx : 0 ≤ x) (hxk : x ≤ k) (hc : 0 ≤ c) :
    endpointComparisonEigen A c k*x^2 ≤ k^2*endpointComparisonEigen A c x := by
  have hdiff : 0 ≤ k-x := sub_nonneg.mpr hxk
  have h := mul_nonneg
    (show 0 ≤ k*x*(k-x) by positivity) (show 0 ≤ 1+c*k*x by positivity)
  dsimp [endpointComparisonEigen]
  nlinarith only [h]

theorem endpoint_rest_ratio_lower (r : ι → ℝ) (top : ι) {A c : ℝ}
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ r top) (hc : 0 ≤ c)
    (hd : 0 ≤ endpointComparisonEigen A c (r top))
    (hf : ∀ i, 0 ≤ endpointComparisonEigen A c (r i)) :
    endpointComparisonEigen A c (r top)*endpointRestP r top ≤
      r top^2*endpointRestQ r top A c := by
  have hs := Finset.sum_le_sum (s := Finset.univ.erase top)
    (f := fun i => endpointComparisonEigen A c (r top)^2*r i^4)
    (g := fun i => r top^4*endpointComparisonEigen A c (r i)^2) (fun i _ => by
      have hfi := hf i
      have h := endpoint_eigen_ratio_monotone (A := A) (hr top).1 (hr i).1 (hr i).2 hc
      have hm := mul_le_mul h h
        (show 0 ≤ endpointComparisonEigen A c (r top)*r i^2 by positivity)
        (show 0 ≤ r top^2*endpointComparisonEigen A c (r i) by positivity)
      change endpointComparisonEigen A c (r top)^2*r i^4 ≤ r top^4*endpointComparisonEigen A c (r i)^2
      nlinarith only [hm])
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hs
  change endpointComparisonEigen A c (r top)^2*endpointRestMoment r top 4 ≤
      r top^4*(∑ i ∈ Finset.univ.erase top, endpointComparisonEigen A c (r i)^2) at hs
  rw [← endpointRestP_sq, ← endpointRestQ_sq] at hs
  have hp0 : 0 ≤ endpointRestP r top := Real.sqrt_nonneg _
  have hq0 : 0 ≤ endpointRestQ r top A c := Real.sqrt_nonneg _
  have hn1 : 0 ≤ endpointComparisonEigen A c (r top)*endpointRestP r top := mul_nonneg hd hp0
  have hn2 : 0 ≤ r top^2*endpointRestQ r top A c := mul_nonneg (sq_nonneg _) hq0
  nlinarith only [hs,hn1,hn2]

theorem endpoint_covariance_ratio (r : ι → ℝ) (top : ι) {A c : ℝ}
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ r top) (h2 : spectralMoment r 2 = 1)
    (hk : 73/100 ≤ r top) (hc : 0 < c) (hA : A^2 ≤ c)
    (hd : r top^2 ≤ endpointComparisonEigen A c (r top))
    (hf : ∀ i, 0 ≤ endpointComparisonEigen A c (r i))
    (hp : 3/20 ≤ endpointRestP r top) :
    0 < endpointRestQ r top A c ∧
      (r top^2*endpointRestQ r top A c) /
          (endpointComparisonEigen A c (r top)*endpointRestP r top) +
        (endpointComparisonEigen A c (r top)*endpointRestP r top) /
          (r top^2*endpointRestQ r top A c) ≤ 6 := by
  let k := r top
  let p := endpointRestP r top
  let q := endpointRestQ r top A c
  let d := endpointComparisonEigen A c k
  have hk0 : 0 < k := by linarith
  have hp0 : 0 < p := by linarith
  have hd0 : 0 < d := lt_of_lt_of_le (sq_pos_of_pos hk0) hd
  have hlower := endpoint_rest_ratio_lower r top hr hc.le (by positivity) hf
  have hupper := endpoint_rest_q_lt r top (fun i => (hr i).1) h2 hk hc hA hf
  have hq0 : 0 < q := by
    have hdp : 0 < d*p := mul_pos hd0 hp0
    have hk2 : 0 < k^2 := sq_pos_of_pos hk0
    change d*p ≤ k^2*q at hlower
    nlinarith only [hdp,hk2,hlower]
  refine ⟨hq0, ?_⟩
  let ratio := k^2*q/(d*p)
  have hr1 : 1 ≤ ratio := (le_div_iff₀ (mul_pos hd0 hp0)).mpr (by simpa using hlower)
  have hrmax : ratio ≤ 40/7 := by
    apply (div_le_iff₀ (mul_pos hd0 hp0)).mpr
    have hqp : q ≤ (40/7)*p := by linarith
    have h1 := mul_le_mul_of_nonneg_left hqp hd0.le
    have h2 := mul_le_mul_of_nonneg_right hd hq0.le
    nlinarith only [h1,h2]
  have hr0 : 0 < ratio := by linarith
  have hs : ratio^2+1 ≤ 6*ratio := by
    have hh := mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hrmax)
    nlinarith only [hh,hrmax]
  have he : (d*p)/(k^2*q) = 1/ratio := by
    dsimp [ratio]
    field_simp [hk0.ne',hp0.ne',hq0.ne',hd0.ne']
  change ratio+(d*p)/(k^2*q) ≤ 6
  rw [he]
  apply (mul_le_mul_iff_left₀ hr0).mp
  have hi : (ratio+1/ratio)*ratio = ratio^2+1 := by field_simp [hr0.ne']
  rw [hi]
  exact hs

end
end SingularValueBounds.KL
