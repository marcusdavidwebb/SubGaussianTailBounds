import SingularValueBounds.Main.Statement
import SingularValueBounds.KL.Weighted.Gaussian
import SingularValueBounds.KL.Certificates.Enclosures
import SingularValueBounds.KL.Barrier.Roots

/-!
# Internal tail statements and one-row estimates

The canonical proofs supply the row estimates and all finite numerical facts.
Matrix quantities are given explicitly in Euclidean/spectral form, avoiding
the default norm on the function representation of a matrix.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

namespace SingularValueBounds.KL
noncomputable section

structure TailConstants where
  alpha : ℝ
  beta : ℝ
  gamma : ℝ
  delta : ℝ
  alpha_pos : 0 < alpha
  beta_pos : 0 < beta
  gamma_pos : 0 < gamma
  delta_pos : 0 < delta

def generalConstants : TailConstants :=
  ⟨96 / 25, 79 / 50, 47 / 20, 3 / 2, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

def oneConstants : TailConstants :=
  ⟨33 / 25, 28 / 25, 58 / 25, Real.sqrt 2, by norm_num, by norm_num,
    by norm_num, Real.sqrt_pos.2 (by norm_num)⟩

def LowerThreshold (c : TailConstants) (m n : ℕ) (K t : ℝ) : ℝ :=
  Real.sqrt m - K * Real.sqrt n - c.alpha * K * logParameter K -
    c.beta * K * Real.sqrt (logParameter K) * t

def UpperThreshold (c : TailConstants) (m n : ℕ) (K t : ℝ) : ℝ :=
  Real.sqrt m + K * Real.sqrt n + c.gamma * K * logParameter K +
    c.delta * K * Real.sqrt (logParameter K) * t

def TailBounds {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {m n : ℕ} [NeZero n] (X : Fin m → Ω → Fin n → ℝ)
    (c : TailConstants) (K t : ℝ) : Prop :=
  μ.real {ω | smallestSingularValue (rowMatrix X ω) ≤ LowerThreshold c m n K t} ≤
    Real.exp (-t ^ 2 / 2) ∧
  μ.real {ω | UpperThreshold c m n K t ≤ largestSingularValue (rowMatrix X ω)} ≤
    Real.exp (-t ^ 2 / 2)

/-- Full current target, with exactly the original row assumptions. -/
def TheoremKL {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : TailConstants) : Prop :=
  ∀ (m n : ℕ) [NeZero n], n ≤ m →
    ∀ (X : Fin m → Ω → Fin n → ℝ) (K : ℝ), 1 ≤ K →
      iIndepFun X μ → (∀ i, CentredIsotropic μ (X i)) →
      (∀ i, SubGaussianMGF μ (X i) K) →
      ∀ t : ℝ, 0 ≤ t → TailBounds μ X c K t

/-- The improved quartet is asserted only for rows with `K = 1`. -/
def TheoremKLOne {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (m n : ℕ) [NeZero n], n ≤ m →
    ∀ (X : Fin m → Ω → Fin n → ℝ),
      iIndepFun X μ → (∀ i, CentredIsotropic μ (X i)) →
      (∀ i, SubGaussianMGF μ (X i) 1) →
      ∀ t : ℝ, 0 ≤ t → TailBounds μ X oneConstants 1 t

theorem lower_threshold_mono {c d : TailConstants} {m n : ℕ} {K t : ℝ}
    (hK : 1 ≤ K) (ht : 0 ≤ t) (ha : c.alpha ≤ d.alpha) (hb : c.beta ≤ d.beta) :
    LowerThreshold d m n K t ≤ LowerThreshold c m n K t := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hL : 0 ≤ logParameter K := zero_le_one.trans (one_le_logParameter hK)
  have h1 := mul_le_mul_of_nonneg_right ha (mul_nonneg hK0 hL)
  have h2 := mul_le_mul_of_nonneg_right hb
    (mul_nonneg (mul_nonneg hK0 (Real.sqrt_nonneg (logParameter K))) ht)
  dsimp [LowerThreshold]
  nlinarith

theorem upper_threshold_mono {c d : TailConstants} {m n : ℕ} {K t : ℝ}
    (hK : 1 ≤ K) (ht : 0 ≤ t) (hg : c.gamma ≤ d.gamma) (hd : c.delta ≤ d.delta) :
    UpperThreshold c m n K t ≤ UpperThreshold d m n K t := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hL : 0 ≤ logParameter K := zero_le_one.trans (one_le_logParameter hK)
  have h1 := mul_le_mul_of_nonneg_right hg (mul_nonneg hK0 hL)
  have h2 := mul_le_mul_of_nonneg_right hd
    (mul_nonneg (mul_nonneg hK0 (Real.sqrt_nonneg (logParameter K))) ht)
  dsimp [UpperThreshold]
  nlinarith

theorem tail_bounds_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m n : ℕ} [NeZero n]
    {X : Fin m → Ω → Fin n → ℝ} {c d : TailConstants} {K t : ℝ}
    (h : TailBounds μ X c K t) (hK : 1 ≤ K) (ht : 0 ≤ t)
    (ha : c.alpha ≤ d.alpha) (hb : c.beta ≤ d.beta)
    (hg : c.gamma ≤ d.gamma) (hd : c.delta ≤ d.delta) : TailBounds μ X d K t := by
  constructor
  · apply le_trans (measureReal_mono ?_) h.1
    intro ω hω
    exact hω.trans (lower_threshold_mono hK ht ha hb)
  · apply le_trans (measureReal_mono ?_) h.2
    intro ω hω
    exact (upper_threshold_mono hK ht hg hd).trans hω

theorem one_constants_dominate_general :
    oneConstants.alpha ≤ generalConstants.alpha ∧
      oneConstants.beta ≤ generalConstants.beta ∧
      oneConstants.gamma ≤ generalConstants.gamma ∧
      oneConstants.delta ≤ generalConstants.delta := by
  norm_num [oneConstants, generalConstants, Real.sqrt_le_iff]

theorem general_at_one_of_endpoint {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m n : ℕ} [NeZero n]
    {X : Fin m → Ω → Fin n → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (h : TailBounds μ X oneConstants 1 t) : TailBounds μ X generalConstants 1 t := by
  obtain ⟨ha, hb, hg, hd⟩ := one_constants_dominate_general
  exact tail_bounds_mono h (by norm_num) ht ha hb hg hd

section MatrixQuantities
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Explicit Euclidean Frobenius norm, not the default `Matrix` norm. -/
def frobenius (R : Matrix ι ι ℝ) : ℝ := Real.sqrt (∑ i, ∑ j, R i j ^ 2)

omit [DecidableEq ι] in
theorem frobenius_nonneg (R : Matrix ι ι ℝ) : 0 ≤ frobenius R := Real.sqrt_nonneg _

omit [DecidableEq ι] in
theorem frobenius_sq (R : Matrix ι ι ℝ) :
    frobenius R ^ 2 = ∑ i, ∑ j, R i j ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem trace_square_eq_sum_sq {R : Matrix ι ι ℝ} (hR : R.IsHermitian) :
    Matrix.trace (R ^ 2) = ∑ i, ∑ j, R i j ^ 2 := by
  have hs : Rᵀ = R := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.eq
  simp only [pow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hji : R j i = R i j := congrFun (congrFun hs i) j
  rw [hji]

theorem frobenius_eq_sqrt_trace_square {R : Matrix ι ι ℝ} (hR : R.IsHermitian) :
    frobenius R = Real.sqrt (Matrix.trace (R ^ 2)) := by
  rw [trace_square_eq_sum_sq hR]
  rfl

theorem frobenius_pos [Nonempty ι] {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    0 < frobenius R := by
  rw [frobenius_eq_sqrt_trace_square hR.isHermitian]
  exact Real.sqrt_pos.2 (trace_square_pos hR)

/-- The Euclidean operator norm of a PSD matrix in spectral form. -/
def spectralMaximum [Nonempty ι] (R : Matrix ι ι ℝ) (hR : R.IsHermitian) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty hR.eigenvalues

theorem eigenvalue_le_spectralMaximum [Nonempty ι] {R : Matrix ι ι ℝ}
    (hR : R.IsHermitian) (i : ι) : hR.eigenvalues i ≤ spectralMaximum R hR :=
  Finset.le_sup' _ (Finset.mem_univ i)

theorem spectralMaximum_le_frobenius [Nonempty ι] {R : Matrix ι ι ℝ}
    (hR : R.PosSemidef) : spectralMaximum R hR.isHermitian ≤ frobenius R := by
  apply Finset.sup'_le
  intro i _
  have hi : hR.isHermitian.eigenvalues i ^ 2 ≤ Matrix.trace (R ^ 2) := by
    rw [real_spectral_trace_square hR.isHermitian]
    exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hf := frobenius_sq R
  rw [← trace_square_eq_sum_sq hR.isHermitian] at hf
  nlinarith [frobenius_nonneg R, hR.eigenvalues_nonneg i]

def spectralRatio [Nonempty ι] (R : Matrix ι ι ℝ) (hR : R.PosDef) : ℝ :=
  spectralMaximum R hR.isHermitian / frobenius R

theorem spectralRatio_pos_le_one [Nonempty ι] {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    0 < spectralRatio R hR ∧ spectralRatio R hR ≤ 1 := by
  have hf := frobenius_pos hR
  have hm : 0 < spectralMaximum R hR.isHermitian :=
    (hR.eigenvalues_pos (Classical.arbitrary ι)).trans_le
      (eigenvalue_le_spectralMaximum hR.isHermitian _)
  exact ⟨div_pos hm hf, (div_le_one hf).2 (spectralMaximum_le_frobenius hR.posSemidef)⟩

/-- The common cap appearing in the transfer lemma. -/
def regularityCost (K w : ℝ) (R : Matrix ι ι ℝ) : ℝ :=
  K ^ 2 * Matrix.trace R + w * frobenius R

/-- Interface to be discharged by the lower one-row packages, with actual
exact shifts and both integrability and the MGF inequality explicit. -/
def LowerRowEstimate [Nonempty ι] {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ι → ℝ) (K w ν : ℝ) : Prop :=
  ∀ (R : Matrix ι ι ℝ) (hR : R.PosDef) (b : ℝ),
    regularityCost K w R ≤ b → 0 < b → ∀ ℓ : ℝ, 0 < ℓ →
      Integrable (fun ω => Real.exp (-ℓ * (1+b) * lowerShift R hR (X ω))) μ ∧
      (∫ ω, Real.exp (-ℓ * (1+b) * lowerShift R hR (X ω)) ∂μ) ≤
        Real.exp (-ℓ / (1+ν*ℓ))

def UpperRowEstimate [Nonempty ι] {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ι → ℝ) (K w ν : ℝ) : Prop :=
  ∀ (R : Matrix ι ι ℝ) (hR : R.PosDef) (b : ℝ),
    regularityCost K w R ≤ b → b < 1 → ∀ ℓ : ℝ, 0 < ℓ → ℓ < 1/ν →
      Integrable (fun ω => Real.exp (ℓ * (1-b) * upperShift R hR (X ω))) μ ∧
      (∫ ω, Real.exp (ℓ * (1-b) * upperShift R hR (X ω)) ∂μ) ≤
        Real.exp (ℓ / (1-ν*ℓ))

/-- The process package must supply its total outward correction budget.
This is an intermediate interface, never a premise of `TheoremKL`. -/
def CorrectionBudget (n : ℕ) (w b outward : ℝ) : Prop :=
  0 ≤ outward ∧ outward ≤ w * Real.sqrt n / b

theorem correction_total_cost {n : ℕ} {K w b outward : ℝ}
    (h : CorrectionBudget n w b outward) :
    (K^2*n+w*Real.sqrt n)/b + outward ≤ (K^2*n+2*w*Real.sqrt n)/b := by
  have he : (K^2*n+w*Real.sqrt n)/b + w*Real.sqrt n/b =
      (K^2*n+2*w*Real.sqrt n)/b := by rw [← add_div]; congr 1; ring
  rw [← he]
  exact add_le_add_right h.2 _

end MatrixQuantities
end
end SingularValueBounds.KL
