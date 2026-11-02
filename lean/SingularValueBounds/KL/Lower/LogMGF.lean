import SingularValueBounds.KL.Lower.ShapeSeries
import SingularValueBounds.KL.Weighted.Gaussian

/-! Applying the scalar lower shape envelope to the actual normalized
comparison matrix; all determinant and centering operations are internal. -/
open MeasureTheory
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [Nonempty ι] in
theorem normalized_trace_square {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (hF : frobenius R = 1) : Matrix.trace (R^2) = 1 := by
  have h := frobenius_sq R
  rw [← trace_square_eq_sum_sq hR.isHermitian,hF] at h
  norm_num at h
  exact h.symm

theorem normalized_lower_comparison_spectral {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (hF : frobenius R = 1) :
    lowerComparison0 R hR = (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ)*
      Matrix.diagonal (fun i => lowerShapeEigenvalue (spectralMaximum R hR.isHermitian)
        (hR.isHermitian.eigenvalues i))*star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) := by
  rw [lowerComparison0,lowerComparison_spectral hR,normalized_trace_square hR hF]
  simp [hF,lowerShapeEigenvalue]

/-- The determinant factors are in the original resolvent eigenbasis; no
continuous or measurable choice of ordered eigenvectors is needed. -/
theorem normalized_lower_gap {R : Matrix ι ι ℝ} (hR : R.PosDef) (hF : frobenius R = 1)
    {u : ℝ} (hu : 0 ≤ u) (huk : u*spectralMaximum R hR.isHermitian < 1) :
    (1-u • lowerComparison0 R hR).PosDef ∧
    Matrix.det (1-u • lowerComparison0 R hR) =
      ∏ i, (1-u*lowerShapeEigenvalue (spectralMaximum R hR.isHermitian) (hR.isHermitian.eigenvalues i)) := by
  let U := hR.isHermitian.eigenvectorUnitary
  let k := spectralMaximum R hR.isHermitian
  let b := fun i => lowerShapeEigenvalue k (hR.isHermitian.eigenvalues i)
  have hk : 0 < k := (hR.eigenvalues_pos (Classical.arbitrary ι)).trans_le (eigenvalue_le_spectralMaximum hR.isHermitian _)
  have hk1 : k ≤ 1 := by simpa [hF] using spectralMaximum_le_frobenius hR.posSemidef
  have hb (i : ι) : 0 < 1-u*b i := by
    have h := (lowerShapeEigenvalue_bounds hk1
      ⟨(hR.eigenvalues_pos i).le,eigenvalue_le_spectralMaximum hR.isHermitian i⟩).2
    dsimp [b,k] at *
    nlinarith [mul_le_mul_of_nonneg_left h hu]
  have hd : Matrix.diagonal (fun i => 1-u*b i) =
      1-u • Matrix.diagonal b := by
    rw [← Matrix.diagonal_one,← Matrix.diagonal_smul,← Matrix.diagonal_sub]
    rfl
  have he : 1-u • lowerComparison0 R hR = (U : Matrix ι ι ℝ)*
      Matrix.diagonal (fun i => 1-u*b i)*star (U : Matrix ι ι ℝ) := by
    rw [hd,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,U.2.2,Matrix.mul_smul,
      smul_mul_assoc,← normalized_lower_comparison_spectral hR hF]
  constructor
  · rw [he]
    exact unitary_conjugate_posDef U _ (Matrix.PosDef.diagonal hb)
  · rw [he,Matrix.det_mul_right_comm,U.2.2,one_mul,Matrix.det_diagonal]

/-- The centered log-MGF bound used by the higher-moment entropy step. -/
theorem normalized_lower_log_mgf {X : Ω → ι → ℝ} {K : ℝ}
    (hsg : SubGaussianMGF μ X K) (hm : Measurable X) (hK : 0 < K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hF : frobenius R = 1)
    {u : ℝ} (hu : 0 < u) (huk : u*spectralMaximum R hR.isHermitian < 1)
    (hM : (spectralMaximum R hR.isHermitian)^2 < lowerM (u*spectralMaximum R hR.isHermitian)) :
    Integrable (fun ω => Real.exp (u/(2*K^2)*(quadraticForm (lowerComparison0 R hR) X ω-
      K^2*Matrix.trace R))) μ ∧
    Real.log (∫ ω,Real.exp (u/(2*K^2)*(quadraticForm (lowerComparison0 R hR) X ω-
      K^2*Matrix.trace R)) ∂μ) ≤ lowerJ (u*spectralMaximum R hR.isHermitian)/
        (2*(spectralMaximum R hR.isHermitian)^2) := by
  let k := spectralMaximum R hR.isHermitian
  let B := lowerComparison0 R hR
  let lam := u/(2*K^2)
  have hk : 0 < k := (hR.eigenvalues_pos (Classical.arbitrary ι)).trans_le (eigenvalue_le_spectralMaximum hR.isHermitian _)
  have hk1 : k ≤ 1 := by simpa [hF] using spectralMaximum_le_frobenius hR.posSemidef
  have hB := (lowerComparison0_posDef hR).posSemidef
  have hf := normalized_lower_gap hR hF hu.le huk
  have hscale : 2*K^2*lam = u := by dsimp [lam]; field_simp
  have hgap : (1-(2*K^2*lam) • B).PosDef := by rw [hscale]; exact hf.1
  have hpos : 0 ≤ lam := by dsimp [lam]; positivity
  have hi := (quadratic_exponential_det_bound hsg hm B hB lam hpos hgap).1
  have hl := quadratic_log_mgf_le_logdet hsg hm B hB lam hpos hgap
  rw [hscale,hf.2] at hl
  have hfactor (i : ι) : 0 < 1-u*lowerShapeEigenvalue k (hR.isHermitian.eigenvalues i) := by
    have h := (lowerShapeEigenvalue_bounds hk1
      ⟨(hR.eigenvalues_pos i).le,eigenvalue_le_spectralMaximum hR.isHermitian i⟩).2
    nlinarith [mul_le_mul_of_nonneg_left h hu.le]
  rw [Real.log_prod (fun i _ => (hfactor i).ne')] at hl
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    lower_shape_envelope hu hk hk1 huk hM
      ⟨(hR.eigenvalues_pos i).le,eigenvalue_le_spectralMaximum hR.isHermitian i⟩)
  rw [Finset.sum_sub_distrib,Finset.sum_neg_distrib,← Finset.mul_sum,
    ← Finset.mul_sum,← real_spectral_trace_square hR.isHermitian,
    normalized_trace_square hR hF,mul_one,← real_spectral_trace hR.isHermitian] at hs
  have hpoint (ω : Ω) : Real.exp (lam*(quadraticForm B X ω-K^2*Matrix.trace R)) =
      Real.exp (-u*Matrix.trace R/2)*Real.exp (lam*quadraticForm B X ω) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [lam]
    field_simp
    <;> ring
  have hint : Integrable (fun ω => Real.exp (lam*(quadraticForm B X ω-K^2*Matrix.trace R))) μ := by
    simp_rw [hpoint]
    exact hi.const_mul _
  refine ⟨hint,?_⟩
  change Real.log (∫ ω,Real.exp (lam*(quadraticForm B X ω-K^2*Matrix.trace R)) ∂μ) ≤ _
  simp_rw [hpoint]
  rw [integral_const_mul,Real.log_mul (Real.exp_ne_zero _) (integral_exp_pos hi).ne',Real.log_exp]
  change _ ≤ lowerJ (u*k)/(2*k^2)
  change Real.log (∫ ω,Real.exp (lam*quadraticForm B X ω) ∂μ) ≤ _ at hl
  have hid : lowerJ (u*k)/(2*k^2) = (lowerJ (u*k)/k^2)/2 := by ring
  rw [hid]
  linarith

end
end SingularValueBounds.KL
