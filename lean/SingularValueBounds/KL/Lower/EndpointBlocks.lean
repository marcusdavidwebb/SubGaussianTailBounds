import SingularValueBounds.KL.Lower.EndpointMixed

/-! # Rank-one block costs for concentrated endpoint spectra -/

open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ι → ℝ}

def endpointRestMoment (r : ι → ℝ) (top : ι) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.erase top, r i ^ j

def endpointRestP (r : ι → ℝ) (top : ι) : ℝ := Real.sqrt (endpointRestMoment r top 4)
def endpointRestQ (r : ι → ℝ) (top : ι) (A c : ℝ) : ℝ :=
  Real.sqrt (∑ i ∈ Finset.univ.erase top, endpointComparisonEigen A c (r i)^2)

lemma endpoint_sum_zero_top (f : ι → ℝ) (top : ι) :
    (∑ i, if i = top then 0 else f i) = ∑ i ∈ Finset.univ.erase top, f i := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ top)]
  simp only [ite_true, zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  rw [if_neg (Finset.mem_erase.mp hi).1]

lemma endpointRestMoment_split (r : ι → ℝ) (top : ι) (j : ℕ) :
    spectralMoment r j = r top ^ j + endpointRestMoment r top j :=
  (Finset.add_sum_erase _ _ (Finset.mem_univ top)).symm

lemma endpointRestP_sq (r : ι → ℝ) (top : ι) :
    endpointRestP r top ^ 2 = endpointRestMoment r top 4 :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)

lemma endpointRestQ_sq (r : ι → ℝ) (top : ι) (A c : ℝ) :
    endpointRestQ r top A c ^ 2 = ∑ i ∈ Finset.univ.erase top, endpointComparisonEigen A c (r i)^2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem endpoint_diagonal_rankone_cost (hsg : SubGaussianMGF μ X 1)
    (hiso : CentredIsotropic μ X) (r : ι → ℝ) (top : ι) (A c : ℝ)
    (h2 : spectralMoment r 2 = 1)
    (hk : 0 < r top) (hd : 0 < endpointComparisonEigen A c (r top))
    (hf : ∀ i, 0 ≤ endpointComparisonEigen A c (r i))
    (hp : 0 < endpointRestP r top) (hq : 0 < endpointRestQ r top A c)
    (hratio : (r top ^ 2*endpointRestQ r top A c) /
        (endpointComparisonEigen A c (r top)*endpointRestP r top) +
      (endpointComparisonEigen A c (r top)*endpointRestP r top) /
        (r top ^ 2*endpointRestQ r top A c) ≤ 6) :
    (∫ ω, diagonalQuadratic (fun i => r i^2) X ω *
      diagonalQuadratic (fun i => endpointComparisonEigen A c (r i)) X ω ∂μ) -
      (∑ i, r i) ≤ A-c*spectralMoment r 3 +
      2*r top^2*endpointComparisonEigen A c (r top)+
      2*endpointRestP r top*endpointRestQ r top A c := by
  let u : ι → ℝ := Pi.single top 1
  let P : Matrix ι ι ℝ := Matrix.diagonal (fun i => if i = top then 0 else r i^2)
  let B : Matrix ι ι ℝ := Matrix.diagonal
    (fun i => if i = top then 0 else endpointComparisonEigen A c (r i))
  have hu : u ⬝ᵥ u = 1 := by simp [u, dotProduct, Pi.single_apply]
  have hP : P.PosSemidef := Matrix.posSemidef_diagonal_iff.mpr (fun i => by
    split_ifs <;> positivity)
  have hB : B.PosSemidef := Matrix.posSemidef_diagonal_iff.mpr (fun i => by
    split_ifs <;> first | positivity | exact hf i)
  have hPu : P *ᵥ u = 0 := by
    ext i
    by_cases hi : i = top <;> simp [P, u, Matrix.mulVec_diagonal, hi]
  have hBu : B *ᵥ u = 0 := by
    ext i
    by_cases hi : i = top <;> simp [B, u, Matrix.mulVec_diagonal, hi]
  have hfp : frobenius P = endpointRestP r top := by
    rw [frobenius_diagonal_eq]
    simp only [ite_pow, zero_pow (by decide : 2 ≠ 0), ← pow_mul, show 2*2=4 from rfl]
    rw [endpoint_sum_zero_top]
    rfl
  have hfq : frobenius B = endpointRestQ r top A c := by
    rw [frobenius_diagonal_eq]
    simp only [ite_pow, zero_pow (by decide : 2 ≠ 0)]
    rw [endpoint_sum_zero_top]
    rfl
  have htotal (f : ι → ℝ) :
      f top • Matrix.vecMulVec u u + Matrix.diagonal (fun i => if i = top then 0 else f i) =
        Matrix.diagonal f := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i = top
      · subst i
        simp [u, Matrix.vecMulVec_apply, Matrix.diagonal]
      · simp [u, Matrix.vecMulVec_apply, Matrix.diagonal, hi]
    · by_cases hi : i = top <;> by_cases hj : j = top <;>
        simp_all [u, Matrix.vecMulVec_apply, Matrix.diagonal]
  have he := endpoint_rankone_covariance_le hsg hiso u P B hu hP hB hPu hBu
    (sq_pos_of_pos hk) hd (by rwa [hfp]) (by rwa [hfq])
    (by simpa only [hfp,hfq] using hratio)
  rw [show r top^2 • Matrix.vecMulVec u u + P = Matrix.diagonal (fun i => r i^2) from htotal (fun i => r i^2),
    show endpointComparisonEigen A c (r top) • Matrix.vecMulVec u u + B =
      Matrix.diagonal (fun i => endpointComparisonEigen A c (r i)) from htotal (fun i => endpointComparisonEigen A c (r i)),
    quadraticCovariance_eq_mixed hsg hiso, hfp, hfq] at he
  simp only [Matrix.trace_diagonal, quadraticForm_diagonal_eq] at he
  change (∫ ω, diagonalQuadratic (fun i => r i^2) X ω *
      diagonalQuadratic (fun i => endpointComparisonEigen A c (r i)) X ω ∂μ) -
      spectralMoment r 2 * (∑ i, endpointComparisonEigen A c (r i)) ≤ _ at he
  rw [h2, one_mul] at he
  have hsum : (∑ i, endpointComparisonEigen A c (r i)) - (∑ i, r i) =
      A-c*spectralMoment r 3 := by
    dsimp [endpointComparisonEigen]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    change (∑ i, r i)+A*spectralMoment r 2-c*spectralMoment r 3-(∑ i, r i) = _
    rw [h2]
    ring
  linarith

def endpointN (A c χ x : ℝ) : ℝ :=
  (2*A/χ-c)*x + (χ+(A^2-2*c)/χ)*x^2 - (2*A*c/χ)*x^3+c^2/χ*x^4

def endpointRankOneMajorant (r : ι → ℝ) (top : ι) (A c χ : ℝ) : ℝ :=
  A-c*r top^3+2*r top^2*endpointComparisonEigen A c (r top)+(1-r top^2)/χ+
    ∑ i ∈ Finset.univ.erase top, r i^2*endpointN A c χ (r i)

theorem endpoint_rankone_cost_young (r : ι → ℝ) (top : ι) (A c : ℝ)
    (h2 : spectralMoment r 2 = 1) {χ : ℝ} (hχ : 0 < χ) :
    A-c*spectralMoment r 3+2*r top^2*endpointComparisonEigen A c (r top)+
      2*endpointRestP r top*endpointRestQ r top A c ≤
        endpointRankOneMajorant r top A c χ := by
  have hy : 2*endpointRestP r top*endpointRestQ r top A c ≤
      χ*endpointRestP r top^2+endpointRestQ r top A c^2/χ := by
    apply (mul_le_mul_iff_left₀ hχ).mp
    have hs := sq_nonneg (χ*endpointRestP r top-endpointRestQ r top A c)
    have he : (χ*endpointRestP r top^2+endpointRestQ r top A c^2/χ)*χ =
        χ^2*endpointRestP r top^2+endpointRestQ r top A c^2 := by
      field_simp [hχ.ne']
    rw [he]
    nlinarith only [hs]
  have hp (x : ℝ) : -c*x^3+χ*x^4+endpointComparisonEigen A c x^2/χ =
      x^2/χ+x^2*endpointN A c χ x := by
    dsimp [endpointComparisonEigen, endpointN]
    field_simp [hχ.ne']
    ring
  have hs2 := endpointRestMoment_split r top 2
  have hs3 := endpointRestMoment_split r top 3
  rw [h2] at hs2
  have he : A-c*spectralMoment r 3+2*r top^2*endpointComparisonEigen A c (r top)+
      χ*endpointRestP r top^2+endpointRestQ r top A c^2/χ =
        endpointRankOneMajorant r top A c χ := by
    rw [endpointRestP_sq, endpointRestQ_sq, hs3]
    dsimp [endpointRankOneMajorant]
    have hsum : -c*endpointRestMoment r top 3+χ*endpointRestMoment r top 4+
        (∑ i ∈ Finset.univ.erase top, endpointComparisonEigen A c (r i)^2)/χ =
        (1-r top^2)/χ + ∑ i ∈ Finset.univ.erase top, r i^2*endpointN A c χ (r i) := by
      dsimp [endpointRestMoment]
      rw [Finset.sum_div, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      simp_rw [hp]
      rw [Finset.sum_add_distrib, ← Finset.sum_div]
      have hrest : (∑ i ∈ Finset.univ.erase top, r i^2) = 1-r top^2 := by
        change endpointRestMoment r top 2 = _
        linarith only [hs2]
      rw [hrest]
    linarith only [hsum]
  rw [← he]
  linarith

end
end SingularValueBounds.KL
