import SingularValueBounds.KL.Lower.GeneralProfile
import SingularValueBounds.KL.Lower.EndpointCap

/-! Positive scaling of the normalized lower comparison. Only the comparison
matrix, not the nonlinear exact shift, is scaled. -/
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem lower_posDef_smul {R : Matrix ι ι ℝ} (hR : R.PosDef) {s : ℝ} (hs : 0<s) :
    (s • R).PosDef := by
  constructor
  · change (s • R)ᴴ=s • R
    simp only [Matrix.conjTranspose_smul,star_trivial,hR.isHermitian.eq]
  · intro x hx
    simpa only [Matrix.smul_mulVec_assoc,dotProduct_smul,smul_eq_mul] using mul_pos hs (hR.2 x hx)

theorem lower_frobenius_smul (R : Matrix ι ι ℝ) {s : ℝ} (hs : 0≤s) :
    frobenius (s • R)=s*frobenius R := by
  have hsum : (∑i,∑j,((s • R) i j)^2)=s^2*(∑i,∑j,R i j^2) := by
    simp only [Matrix.smul_apply,smul_eq_mul,mul_pow,Finset.mul_sum]
  unfold frobenius
  rw [hsum,Real.sqrt_mul (sq_nonneg s),Real.sqrt_sq hs]

theorem lower_spectralMaximum_smul {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {s : ℝ} (hs : 0<s) :
    spectralMaximum (s • R) (lower_posDef_smul hR hs).isHermitian=
      s*spectralMaximum R hR.isHermitian := by
  apply le_antisymm
  · apply (spectralMaximum_le_iff_euclidean_quadratic _ _).mpr
    intro x
    simpa only [Matrix.smul_mulVec_assoc,dotProduct_smul,smul_eq_mul,mul_assoc] using
      mul_le_mul_of_nonneg_left (euclidean_quadratic_le_spectralMaximum hR.isHermitian x) hs.le
  · obtain ⟨x,hx,hq⟩ := spectralMaximum_attained hR.isHermitian
    have hh := euclidean_quadratic_le_spectralMaximum (lower_posDef_smul hR hs).isHermitian x
    simpa only [Matrix.smul_mulVec_assoc,dotProduct_smul,smul_eq_mul,hq,hx,one_pow,mul_one] using hh

theorem lowerWeight_smul {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {s : ℝ} (hs : s≠0) : lowerWeight (s • R)=lowerWeight R := by
  have hp : (s • R)^2=s^2 • R^2 := by simp only [pow_two,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [lowerWeight,hp,Matrix.trace_smul,smul_eq_mul,smul_smul]
  have ht := (trace_square_pos hR).ne'
  have hfactor : (s^2*Matrix.trace (R^2))⁻¹*s^2=(Matrix.trace (R^2))⁻¹ := by
    field_simp
  rw [hfactor]
  rfl

theorem lowerComparison_smul {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {s : ℝ} (hs : 0<s) (A c : ℝ) :
    lowerComparison (s • R) A c=s • lowerComparison R A c := by
  rw [lowerComparison,lower_frobenius_smul R hs.le,lowerWeight_smul hR hs.ne']
  rw [show (A*(s*frobenius R)) • (1 : Matrix ι ι ℝ)-c • (s • R)=
      s • ((A*frobenius R) • (1 : Matrix ι ι ℝ)-c • R) by
    simp only [smul_sub,smul_smul]
    rw [show A*(s*frobenius R)=s*(A*frobenius R) by ring,
      show c*s=s*c by ring]]
  rw [Matrix.mul_smul,← smul_add]
  rfl

end
end SingularValueBounds.KL
