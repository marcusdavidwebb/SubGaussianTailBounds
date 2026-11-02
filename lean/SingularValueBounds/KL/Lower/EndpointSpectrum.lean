import SingularValueBounds.KL.Lower.EndpointRankOne
import SingularValueBounds.KL.Lower.Comparison

/-! # The endpoint operator cost for normalized spectra

Supplementary S1.5, the spectral inequality in the paragraph “An
operator-norm cost”. The Euclidean quantities are explicit finite sums.
-/

open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def spectralMoment (r : ι → ℝ) (j : ℕ) : ℝ := ∑ i, r i ^ j

def endpointComparisonEigen (A c x : ℝ) : ℝ := x + A*x^2-c*x^3

def endpointPair (k x y : ℝ) : ℝ :=
  x^2*y^2*(x-y)^2*(2*k*(x+y)-x^2*y^2)

lemma endpointPair_comm (k x y : ℝ) : endpointPair k x y = endpointPair k y x := by
  dsimp [endpointPair]
  ring

lemma endpointPair_self (k x : ℝ) : endpointPair k x x = 0 := by
  simp [endpointPair]

lemma endpointPair_nonneg {k x y : ℝ} (hk : 0 ≤ k) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxk : x ≤ k) (hyk : y ≤ k) (hk1 : k ≤ 1) : 0 ≤ endpointPair k x y := by
  have hx1 : x ≤ 1 := hxk.trans hk1
  have hy1 : y ≤ 1 := hyk.trans hk1
  have hxy : x*y ≤ 1 := by nlinarith
  have hxy2 : x^2*y^2 ≤ x*y := by nlinarith [mul_nonneg hx hy]
  have hxx : x*y ≤ k*(x+y) := by
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hyk), mul_nonneg hy (sub_nonneg.mpr hxk)]
  exact mul_nonneg (by positivity) (by nlinarith [mul_nonneg hk (add_nonneg hx hy)])

omit [DecidableEq ι] in
lemma endpointComparisonEigen_sq_sum (r : ι → ℝ) (A c : ℝ) :
    (∑ i, endpointComparisonEigen A c (r i)^2) =
      spectralMoment r 2 + 2*A*spectralMoment r 3 +
      (A^2-2*c)*spectralMoment r 4 - 2*A*c*spectralMoment r 5 + c^2*spectralMoment r 6 := by
  have hp (x : ℝ) : endpointComparisonEigen A c x ^ 2 =
      x^2 + 2*A*x^3 + (A^2-2*c)*x^4 - 2*A*c*x^5+c^2*x^6 := by
    dsimp [endpointComparisonEigen]
    ring
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, spectralMoment]

set_option maxRecDepth 4000 in
omit [DecidableEq ι] in
lemma endpointPair_sum (r : ι → ℝ) (k : ℝ) :
    (∑ i, ∑ j, endpointPair k (r i) (r j)) =
      2 * (2*k*(spectralMoment r 5*spectralMoment r 2 -
        spectralMoment r 4*spectralMoment r 3) -
        spectralMoment r 6*spectralMoment r 4 + spectralMoment r 5 ^ 2) := by
  have hp (x y : ℝ) : endpointPair k x y =
      2*k*(x^5*y^2+x^2*y^5-x^4*y^3-x^3*y^4) -
        x^6*y^4-x^4*y^6+2*x^5*y^5 := by
    dsimp [endpointPair]
    ring
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, spectralMoment]
  ring

theorem endpointPair_top_le_sum (r : ι → ℝ) {k : ℝ} (hk : 0 ≤ k) (hk1 : k ≤ 1)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ k) (top : ι) :
    2*(∑ j, endpointPair k (r top) (r j)) ≤
      ∑ i, ∑ j, endpointPair k (r i) (r j) := by
  classical
  let rest := Finset.univ.erase top
  have ht : top ∈ (Finset.univ : Finset ι) := Finset.mem_univ _
  have hall (i j : ι) : 0 ≤ endpointPair k (r i) (r j) :=
    endpointPair_nonneg hk (hr i).1 (hr j).1 (hr i).2 (hr j).2 hk1
  have hsplit (i : ι) : (∑ j, endpointPair k (r i) (r j)) =
      endpointPair k (r i) (r top) + ∑ j ∈ rest, endpointPair k (r i) (r j) := by
    exact (Finset.add_sum_erase _ _ ht).symm
  have houter : (∑ i, ∑ j, endpointPair k (r i) (r j)) =
      (∑ j, endpointPair k (r top) (r j)) +
        ∑ i ∈ rest, ∑ j, endpointPair k (r i) (r j) :=
    (Finset.add_sum_erase _ _ ht).symm
  rw [houter]
  simp_rw [hsplit]
  rw [endpointPair_self]
  simp only [zero_add, Finset.sum_add_distrib]
  have hs : (∑ i ∈ rest, endpointPair k (r i) (r top)) =
      ∑ j ∈ rest, endpointPair k (r top) (r j) := by
    apply Finset.sum_congr rfl
    intro i _
    exact endpointPair_comm _ _ _
  rw [hs]
  have hn : 0 ≤ ∑ i ∈ rest, ∑ j ∈ rest, endpointPair k (r i) (r j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hall i j
  linarith

lemma endpointPair_top_lower {k x : ℝ} (hk : 0 ≤ k) (hx : 0 ≤ x)
    (hv0 : 1/2 ≤ k^2) (hv1 : k^2 ≤ 4/5) (hx2 : x^2 ≤ 1-k^2) :
    (2*k^2-1)^2*x^2*(k^2-x^2) ≤ endpointPair k k x := by
  have hxk : x ≤ k := by nlinarith
  have hdiff : 0 ≤ k^2-x^2 := by nlinarith
  have hkmx : 0 ≤ k-x := sub_nonneg.mpr hxk
  have hbase : (2*k^2-1)/2 ≤ k*(k-x) := by nlinarith [sq_nonneg (k-x)]
  have hbr : (3/2)*k*(k+x) ≤ 2*k*(k+x)-k^2*x^2 := by
    nlinarith [mul_nonneg (sq_nonneg k) (sub_nonneg.mpr hx2),
      mul_nonneg hk hx]
  have hp1 := mul_le_mul_of_nonneg_left hbr
    (show 0 ≤ k^2*x^2*(k-x)^2 by positivity)
  have hp2 := mul_le_mul_of_nonneg_right hbase
    (show 0 ≤ (3/2)*k^2*x^2*(k^2-x^2) by positivity)
  have hp3 := mul_le_mul_of_nonneg_right
    (show (2*k^2-1)^2 ≤ (3/4)*k^2*(2*k^2-1) by nlinarith)
    (show 0 ≤ x^2*(k^2-x^2) by positivity)
  dsimp [endpointPair]
  nlinarith only [hp1, hp2, hp3]

omit [DecidableEq ι] in
lemma normalized_fourth_le_top_square (r : ι → ℝ) {k : ℝ}
    (hk : 0 ≤ k) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ k)
    (h2 : spectralMoment r 2 = 1) : spectralMoment r 4 ≤ k^2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (f := fun i => r i ^ 4)
    (g := fun i => k^2 * r i^2) (fun i _ => by
      have hi : r i ^ 2 ≤ k^2 := by nlinarith [(hr i).1, (hr i).2]
      change r i^4 ≤ k^2*r i^2
      nlinarith only [mul_nonneg (sq_nonneg (r i)) (sub_nonneg.mpr hi)])
  rw [← Finset.mul_sum] at h
  change spectralMoment r 4 ≤ k^2*spectralMoment r 2 at h
  simpa only [h2, mul_one] using h

lemma normalized_other_square_le (r : ι → ℝ) {k : ℝ} (top : ι) (ht : r top = k)
    (h2 : spectralMoment r 2 = 1) {i : ι} (hi : i ≠ top) : r i ^ 2 ≤ 1-k^2 := by
  have hs : (∑ j ∈ Finset.univ.erase top, r j^2) = 1-k^2 := by
    have he := Finset.add_sum_erase (s := Finset.univ) (fun j => r j^2) (Finset.mem_univ top)
    change r top ^ 2 + _ = spectralMoment r 2 at he
    rw [h2, ht] at he
    linarith
  rw [← hs]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (r j)) (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩)

lemma normalized_fourth_split_le (r : ι → ℝ) {k : ℝ} (top : ι) (ht : r top = k)
    (h2 : spectralMoment r 2 = 1) : spectralMoment r 4 ≤ k^4+(1-k^2)^2 := by
  let rest := Finset.univ.erase top
  have he2 := Finset.add_sum_erase (s := Finset.univ) (fun j => r j^2) (Finset.mem_univ top)
  have he4 := Finset.add_sum_erase (s := Finset.univ) (fun j => r j^4) (Finset.mem_univ top)
  change r top^2 + (∑ j ∈ rest, r j^2) = spectralMoment r 2 at he2
  change r top^4 + (∑ j ∈ rest, r j^4) = spectralMoment r 4 at he4
  rw [ht, h2] at he2
  rw [ht] at he4
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := rest) (fun j _ => sq_nonneg (r j))
  simp only [← pow_mul, show 2*2=4 from rfl] at hs
  nlinarith only [he2, he4, hs]

set_option maxHeartbeats 800000 in
/-- The squared spectral inequality behind the endpoint operator cost.
The proof separates `s₄≤1/2` from the unique-top-coordinate regime. -/
theorem endpoint_operator_discriminant (r : ι → ℝ) {k : ℝ}
    (hk : 0 ≤ k) (hkmax : k ≤ 73/100)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ k) (h2 : spectralMoment r 2 = 1)
    (top : ι) (ht : r top = k) :
    spectralMoment r 4 * (∑ i, endpointComparisonEigen k 1 (r i)^2) ≤
      (k-k*spectralMoment r 4+spectralMoment r 5)^2 := by
  have hk1 : k ≤ 1 := by linarith
  have hs4 := normalized_fourth_le_top_square r hk hr h2
  have hpair0 := Finset.sum_nonneg (s := Finset.univ) (fun i _ =>
    Finset.sum_nonneg (s := Finset.univ) (fun j _ =>
      endpointPair_nonneg hk (hr i).1 (hr j).1 (hr i).2 (hr j).2 hk1))
  have he := endpointPair_sum r k
  have hnorm := endpointComparisonEigen_sq_sum r k 1
  rw [h2] at he hnorm
  rw [hnorm]
  by_cases hs : spectralMoment r 4 ≤ 1/2
  · have hp : 0 ≤ (k^2-spectralMoment r 4)*(1-2*spectralMoment r 4) :=
      mul_nonneg (sub_nonneg.mpr hs4) (by linarith)
    nlinarith only [he, hp, hpair0]
  · have hv0 : 1/2 ≤ k^2 := by linarith
    have hv1 : k^2 ≤ 4/5 := by nlinarith
    have hsbound := normalized_fourth_split_le r top ht h2
    have hsneg : 2*spectralMoment r 4-1 ≤ (2*k^2-1)^2 := by nlinarith only [hsbound]
    have hpt := endpointPair_top_le_sum r hk hk1 hr top
    rw [ht] at hpt
    have hplower : (2*k^2-1)^2 * (k^2-spectralMoment r 4) ≤
        ∑ j, endpointPair k k (r j) := by
      have hb := Finset.sum_le_sum (s := Finset.univ)
        (f := fun j => (2*k^2-1)^2 * r j^2 * (k^2-r j^2))
        (g := fun j => endpointPair k k (r j)) (fun j _ => by
          by_cases hj : j = top
          · subst j
            simp only [ht, sub_self, mul_zero, endpointPair_self, le_refl]
          · exact endpointPair_top_lower hk (hr j).1 hv0 hv1
              (normalized_other_square_le r top ht h2 hj))
      have hsum : (∑ j, (2*k^2-1)^2 * r j^2 * (k^2-r j^2)) =
          (2*k^2-1)^2*(k^2-spectralMoment r 4) := by
        have hp (x : ℝ) : (2*k^2-1)^2*x^2*(k^2-x^2) =
            (2*k^2-1)^2*(k^2*x^2-x^4) := by ring
        simp_rw [hp]
        simp only [← Finset.mul_sum, Finset.sum_sub_distrib]
        change (2*k^2-1)^2*(k^2*spectralMoment r 2-spectralMoment r 4) = _
        rw [h2]
        ring
      rwa [hsum] at hb
    have hprod := mul_le_mul_of_nonneg_left hsneg (sub_nonneg.mpr hs4)
    nlinarith only [he, hpt, hplower, hprod]

/-- The endpoint mixed-cost scalar inequality for `κ≤73/100`. -/
theorem endpoint_operator_cost (r : ι → ℝ) {k : ℝ}
    (hk : 0 ≤ k) (hkmax : k ≤ 73/100)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ k) (h2 : spectralMoment r 2 = 1)
    (top : ι) (ht : r top = k) :
    k+k*spectralMoment r 4-spectralMoment r 5 +
      Real.sqrt (spectralMoment r 4) *
        Real.sqrt (∑ i, endpointComparisonEigen k 1 (r i)^2) ≤ 2*k := by
  have hd := endpoint_operator_discriminant r hk hkmax hr h2 top ht
  have hs4 := normalized_fourth_le_top_square r hk hr h2
  have hs40 : 0 ≤ spectralMoment r 4 := Finset.sum_nonneg fun i _ => pow_nonneg (hr i).1 _
  have hs50 : 0 ≤ spectralMoment r 5 := Finset.sum_nonneg fun i _ => pow_nonneg (hr i).1 _
  have hn : 0 ≤ ∑ i, endpointComparisonEigen k 1 (r i)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hk1 : k ≤ 1 := by linarith
  have hb : 0 ≤ k-k*spectralMoment r 4+spectralMoment r 5 := by
    have hs41 : spectralMoment r 4 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg hk (sub_nonneg.mpr hs41)]
  have hroot : Real.sqrt (spectralMoment r 4) *
        Real.sqrt (∑ i, endpointComparisonEigen k 1 (r i)^2) ≤
      k-k*spectralMoment r 4+spectralMoment r 5 := by
    have he1 := Real.sq_sqrt hs40
    have he2 := Real.sq_sqrt hn
    have he : (Real.sqrt (spectralMoment r 4) *
      Real.sqrt (∑ i, endpointComparisonEigen k 1 (r i)^2))^2 =
      spectralMoment r 4 * (∑ i, endpointComparisonEigen k 1 (r i)^2) := by
      rw [mul_pow, he1, he2]
    nlinarith only [he, hd, hb, mul_nonneg (Real.sqrt_nonneg (spectralMoment r 4))
      (Real.sqrt_nonneg (∑ i, endpointComparisonEigen k 1 (r i)^2))]
  linarith

end
end SingularValueBounds.KL
