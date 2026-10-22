import SingularValueBounds.KL.Lower.EndpointQuartic

/-! # Orthogonal rank-one covariance refinement

Supplementary `eq:app-K-one-rankone-covariance`. A direct combination of
the same quartic inequalities avoids divisions by `v` and `2-v`; it therefore
includes both variance endpoints in the main proof.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

namespace SingularValueBounds.KL
noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ι → ℝ}

theorem quadraticCovariance_rankone_expansion (hsg : SubGaussianMGF μ X 1)
    (E P B : Matrix ι ι ℝ) (a d : ℝ) :
    quadraticCovariance μ X (a • E + P) (d • E + B) =
      a*d*quadraticCovariance μ X E E + d*quadraticCovariance μ X E P +
      a*quadraticCovariance μ X E B + quadraticCovariance μ X P B := by
  have he := centeredQuadratic_memLp hsg E
  have hp := centeredQuadratic_memLp hsg P
  have hb := centeredQuadratic_memLp hsg B
  have hpoint (ω : Ω) :
      centeredQuadratic (a • E + P) X ω * centeredQuadratic (d • E + B) X ω =
      (a*d)*(centeredQuadratic E X ω * centeredQuadratic E X ω) +
      d*(centeredQuadratic E X ω * centeredQuadratic P X ω) +
      a*(centeredQuadratic E X ω * centeredQuadratic B X ω) +
      centeredQuadratic P X ω * centeredQuadratic B X ω := by
    have hae := centeredQuadratic_add_smul (X := X) E P a 1 ω
    have hde := centeredQuadratic_add_smul (X := X) E B d 1 ω
    simp only [one_smul, one_mul] at hae hde
    rw [hae, hde]
    ring
  unfold quadraticCovariance
  simp_rw [hpoint]
  rw [integral_add (f := fun ω => (a*d)*(centeredQuadratic E X ω * centeredQuadratic E X ω) +
        d*(centeredQuadratic E X ω * centeredQuadratic P X ω) +
        a*(centeredQuadratic E X ω * centeredQuadratic B X ω))
      (g := fun ω => centeredQuadratic P X ω * centeredQuadratic B X ω)
      ((((he.integrable_mul he).const_mul _).add ((he.integrable_mul hp).const_mul _)).add
        ((he.integrable_mul hb).const_mul _)) (hp.integrable_mul hb),
    integral_add (f := fun ω => (a*d)*(centeredQuadratic E X ω * centeredQuadratic E X ω) +
        d*(centeredQuadratic E X ω * centeredQuadratic P X ω))
      (g := fun ω => a*(centeredQuadratic E X ω * centeredQuadratic B X ω))
      (((he.integrable_mul he).const_mul _).add ((he.integrable_mul hp).const_mul _))
      ((he.integrable_mul hb).const_mul _),
    integral_add (f := fun ω => (a*d)*(centeredQuadratic E X ω * centeredQuadratic E X ω))
      (g := fun ω => d*(centeredQuadratic E X ω * centeredQuadratic P X ω))
      ((he.integrable_mul he).const_mul _) ((he.integrable_mul hp).const_mul _)]
  simp only [integral_const_mul]

set_option maxHeartbeats 800000 in
/-- The scalar covariance combination. The quartic tests used here are at
`(h,j)=(dp,q)` and `(aq,p)`; their scales are nonnegative even at `v=0,2`. -/
theorem endpoint_rankone_scalar {a d p q v x y z vy vw : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hv : v ≤ 2)
    (hr : (a*q)^2 + (d*p)^2 ≤ 6*a*d*p*q)
    (hY : 0 ≤ (2-v)*(d*p)^2 - 6*x*(d*p)*q + 3*(2*p^2-vy)*q^2)
    (hW : 0 ≤ (2-v)*(a*q)^2 - 6*y*(a*q)*p + 3*(2*q^2-vw)*p^2)
    (hcov : 0 ≤ q^2*vy - 2*q*p*z + p^2*vw) :
    a*d*v + d*x + a*y + z ≤ 2*a*d + 2*p*q := by
  have hr' := mul_le_mul_of_nonneg_left hr (sub_nonneg.mpr hv)
  have hsum : 6*p*q*(a*d*v + d*x + a*y + z - (2*a*d+2*p*q)) ≤ 0 := by
    nlinarith only [hY, hW, hcov, hr']
  have hpos : 0 < 6*p*q := by positivity
  have := (mul_le_mul_left hpos).mp (show 6*p*q*(a*d*v+d*x+a*y+z-(2*a*d+2*p*q)) ≤ 6*p*q*0 by simpa using hsum)
  linarith

/-- Supplementary `eq:app-K-one-rankone-covariance`, with no commutation
assumption on the two perpendicular PSD blocks. -/
theorem endpoint_rankone_covariance_le (hsg : SubGaussianMGF μ X 1)
    (hiso : CentredIsotropic μ X) (u : ι → ℝ)
    (P B : Matrix ι ι ℝ) (hu : u ⬝ᵥ u = 1)
    (hP : P.PosSemidef) (hB : B.PosSemidef)
    (hPu : P *ᵥ u = 0) (hBu : B *ᵥ u = 0)
    {a d : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hp : 0 < frobenius P) (hq : 0 < frobenius B)
    (hr : (a * frobenius B) / (d * frobenius P) +
      (d * frobenius P) / (a * frobenius B) ≤ 6) :
    quadraticCovariance μ X (a • Matrix.vecMulVec u u + P)
      (d • Matrix.vecMulVec u u + B) ≤ 2*a*d + 2*frobenius P*frobenius B := by
  let E := Matrix.vecMulVec u u
  have hE : E.PosSemidef := outer_posSemidef u
  have hE2 : Matrix.trace (E^2) = 1 := by
    have he : E*E = (u ⬝ᵥ u) • E := outer_mul_outer u u u u
    rw [pow_two, he, hu, one_smul]
    change (∑ i, u i * u i) = 1
    exact hu
  have hv := quadraticCovariance_self_le hsg hiso E hE
  rw [hE2] at hv
  have htP : Matrix.trace (P^2) = frobenius P ^ 2 := by
    rw [trace_square_eq_sum_sq hP.isHermitian, frobenius_sq]
  have htB : Matrix.trace (B^2) = frobenius B ^ 2 := by
    rw [trace_square_eq_sum_sq hB.isHermitian, frobenius_sq]
  have hy := endpoint_orthogonal_quartic hsg hiso u P hu hP hPu
    (mul_nonneg hd.le hp.le) hq.le
  have hw := endpoint_orthogonal_quartic hsg hiso u B hu hB hBu
    (mul_nonneg ha.le hq.le) hp.le
  rw [htP] at hy
  rw [htB] at hw
  have hc := quadraticCovariance_self_nonneg (μ := μ) (X := X)
    (frobenius B • P + (-frobenius P) • B)
  rw [quadraticCovariance_add_smul hsg] at hc
  have hr' : (a*frobenius B)^2 + (d*frobenius P)^2 ≤
      6*a*d*frobenius P*frobenius B := by
    have hdp : 0 < d*frobenius P := mul_pos hd hp
    have haq : 0 < a*frobenius B := mul_pos ha hq
    have hs := (div_le_iff₀ (mul_pos hdp haq)).mp
      (show ((a*frobenius B)^2+(d*frobenius P)^2) /
          ((d*frobenius P)*(a*frobenius B)) ≤ 6 from by
        convert hr using 1 <;> field_simp [hdp.ne', haq.ne'] <;> ring)
    nlinarith only [hs]
  rw [quadraticCovariance_rankone_expansion hsg]
  apply endpoint_rankone_scalar hp hq (by simpa using hv) hr' hy hw
  nlinarith only [hc]

end
end SingularValueBounds.KL
