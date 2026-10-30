import Mathlib.Data.Complex.ExponentialBounds
import SingularValueBounds.KL.Weighted.Gaussian
import SingularValueBounds.KL.Lower.Laplace

/-!
# Lower fourth-moment refinement (supplementary S1.3)

The offset estimate `eq:app-low-fourth-offset` is obtained from the existing
cosh interpolation. The real-variable interval argument and the small scalar
comparisons are proved here. The trace-one quadratic consequences correspond
to `eq:app-low-Tmoment`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix NNReal

namespace SingularValueBounds.KL

noncomputable section

private theorem offset_log_first : Real.log (1996 / 99 : ℝ) < 751 / 250 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 1996 / 99)).2
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 751 / 250) 25
  have hn : (1996 / 99 : ℝ) <
      ∑ i ∈ Finset.range 25, (751 / 250 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hn.trans_le hs

private theorem offset_log_second : Real.log (499 / 20 : ℝ) < 259 / 80 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 499 / 20)).2
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 259 / 80) 25
  have hn : (499 / 20 : ℝ) <
      ∑ i ∈ Finset.range 25, (259 / 80 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hn.trans_le hs

private theorem offset_exp_three : Real.exp 3 < 21 := by
  have h := Real.exp_one_lt_d9
  have hpos := Real.exp_pos 1
  have he : Real.exp 3 = Real.exp 1 ^ 3 := by
    simpa using Real.exp_nat_mul (1 : ℝ) 3
  rw [he]
  nlinarith [sq_nonneg (Real.exp 1 - 2.7182818286),
    mul_nonneg (sub_nonneg.mpr h.le) (sq_nonneg (Real.exp 1)),
    mul_nonneg (sub_nonneg.mpr h.le) (show 0 ≤ (2.7182818286 : ℝ) * Real.exp 1 by positivity)]

/-- The real interval estimate in the offset fourth-moment argument. -/
theorem fourth_offset_base {K : ℝ} (hK : 1 ≤ K) :
    Real.log (2 * ((499 / 100 : ℝ) * K ^ 2 * logParameter K + 1 / 2)) <
      ((499 / 100 : ℝ) * K ^ 2 * logParameter K + 1 / 2) / (2 * K ^ 2) := by
  let L := logParameter K
  let C := (499 / 100 : ℝ) * K ^ 2 * L + 1 / 2
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hK2 : 0 < K ^ 2 := sq_pos_of_pos hK0
  have hL1 : 1 ≤ L := one_le_logParameter hK
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hC : 0 < C := by dsimp [C]; positivity
  have hlogK : Real.log K = L - 1 := by dsimp [L, logParameter]; ring
  have hlog : Real.log (2 * C) ≤
      Real.log ((499 / 50 : ℝ) * L) + 2 * Real.log K +
        1 / ((499 / 50 : ℝ) * K ^ 2 * L) := by
    have hid : 2 * C = ((499 / 50 : ℝ) * L) * K ^ 2 *
        (1 + 1 / ((499 / 50 : ℝ) * K ^ 2 * L)) := by
      dsimp [C]
      field_simp [hK0.ne', hL.ne']
      ring
    rw [hid, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have ht := Real.log_le_sub_one_of_pos
      (show 0 < 1 + 1 / ((499 / 50 : ℝ) * K ^ 2 * L) by positivity)
    linarith
  have hcoef : (7 / 50 : ℝ) ≤ 1 / 4 - 1 / ((499 / 50 : ℝ) * L) := by
    have hd : 0 < (499 / 50 : ℝ) * L := by positivity
    have hh : 1 / ((499 / 50 : ℝ) * L) ≤ 11 / 100 := by
      apply (div_le_iff₀ hd).2
      nlinarith
    linarith
  have hmain : 0 < (99 / 200 : ℝ) * L + 2 - Real.log ((499 / 50 : ℝ) * L) +
      (1 / K ^ 2) * (1 / 4 - 1 / ((499 / 50 : ℝ) * L)) := by
    by_cases hsmall : L ≤ 5 / 2
    · have hglobal : 3 - Real.log (1996 / 99 : ℝ) ≤
          (99 / 200 : ℝ) * L + 2 - Real.log ((499 / 50 : ℝ) * L) := by
        have hid : (499 / 50 : ℝ) * L = (1996 / 99) * ((99 / 200) * L) := by ring
        rw [hid, Real.log_mul (by norm_num) (by positivity)]
        have ht := Real.log_le_sub_one_of_pos (show 0 < (99 / 200 : ℝ) * L by positivity)
        linarith
      have hKbound : K ^ 2 < 21 := by
        have he : K ^ 2 = Real.exp (2 * Real.log K) := by
          rw [show (2 : ℝ) * Real.log K = Real.log K + Real.log K by ring,
            Real.exp_add, Real.exp_log hK0]
          ring
        rw [he]
        apply lt_of_le_of_lt (Real.exp_le_exp.mpr ?_) offset_exp_three
        rw [hlogK]
        linarith
      have hi : (1 / 21 : ℝ) < 1 / K ^ 2 :=
        (one_div_lt_one_div (by norm_num : (0 : ℝ) < 21) hK2).2 hKbound
      have hm := mul_le_mul_of_nonneg_left hcoef (show 0 ≤ 1 / K ^ 2 by positivity)
      nlinarith [offset_log_first]
    · have hlarge : (5 / 2 : ℝ) ≤ L := le_of_lt (lt_of_not_ge hsmall)
      have hid : (499 / 50 : ℝ) * L = (499 / 20) * (L / (5 / 2)) := by ring
      have ht := Real.log_le_sub_one_of_pos (show 0 < L / (5 / 2) by positivity)
      have hg : 0 < (99 / 200 : ℝ) * L + 2 - Real.log ((499 / 50 : ℝ) * L) := by
        rw [hid, Real.log_mul (by norm_num) (by positivity)]
        nlinarith [offset_log_second]
      have hm := mul_nonneg (show 0 ≤ 1 / K ^ 2 by positivity)
        (le_trans (by norm_num : (0 : ℝ) ≤ 7 / 50) hcoef)
      linarith
  have heq : C / (2 * K ^ 2) -
      (Real.log ((499 / 50 : ℝ) * L) + 2 * Real.log K +
        1 / ((499 / 50 : ℝ) * K ^ 2 * L)) =
      (99 / 200 : ℝ) * L + 2 - Real.log ((499 / 50 : ℝ) * L) +
        (1 / K ^ 2) * (1 / 4 - 1 / ((499 / 50 : ℝ) * L)) := by
    rw [hlogK]
    dsimp [C]
    field_simp [hK0.ne', hL.ne']
    ring
  change Real.log (2 * C) < C / (2 * K ^ 2)
  linarith

/-- Solving the implicit cosh bound with the offset threshold proves
`eq:app-low-fourth-offset`. -/
theorem fourth_implicit_offset {m K : ℝ} (hK : 1 ≤ K) (hm : 0 < m)
    (hi : m / (2 * K ^ 2) ≤ Real.log (2 * m)) :
    m ≤ (499 / 100 : ℝ) * K ^ 2 * logParameter K + 1 / 2 := by
  let C := (499 / 100 : ℝ) * K ^ 2 * logParameter K + 1 / 2
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hL := one_le_logParameter hK
  have hC : 0 < C := by dsimp [C]; positivity
  have hbase : Real.log (2 * C) < C / (2 * K ^ 2) := fourth_offset_base hK
  by_contra hmc
  have hmc' : C < m := lt_of_not_ge hmc
  let r := m / C
  have hr : 0 < r := div_pos hm hC
  have hr1 : 1 ≤ r := (le_div_iff₀ hC).2 (by simpa using hmc'.le)
  have hratio : 1 ≤ C / (2 * K ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * K ^ 2)).2
    dsimp [C]
    nlinarith [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hL)]
  have hprod : 2 * m = (2 * C) * r := by dsimp [r]; field_simp [hC.ne']; ring
  have hl : Real.log (2 * m) < m / (2 * K ^ 2) := by
    calc
      Real.log (2 * m) = Real.log (2 * C) + Real.log r := by
        rw [hprod, Real.log_mul (by positivity) hr.ne']
      _ ≤ Real.log (2 * C) + (r - 1) :=
        add_le_add_left (Real.log_le_sub_one_of_pos hr) _
      _ < C / (2 * K ^ 2) + (r - 1) := add_lt_add_right hbase _
      _ ≤ r * (C / (2 * K ^ 2)) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hratio)]
      _ = m / (2 * K ^ 2) := by dsimp [r]; field_simp [hC.ne']
  exact (not_lt_of_ge hi) hl

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The offset scalar fourth-moment estimate from the original MGF assumption. -/
theorem scalar_fourth_offset {Y : Ω → ℝ} {K : ℝ}
    (h : HasSubgaussianMGF Y ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hK : 1 ≤ K) (hmean : (∫ ω, Y ω ^ 2 ∂μ) = 1) :
    (∫ ω, Y ω ^ 4 ∂μ) ≤ (499 / 100 : ℝ) * K ^ 2 * logParameter K + 1 / 2 := by
  have hi : ∀ n : ℕ, Integrable (fun ω => Y ω ^ n) μ :=
    fun n => integrable_pow_of_integrable_exp_mul (by norm_num : (1 : ℝ) ≠ 0)
      (h.integrable_exp_mul 1) (h.integrable_exp_mul (-1)) n
  have hm := scalar_one_le_fourth_moment (hi 2) (hi 4) hmean
  exact fourth_implicit_offset hK (lt_of_lt_of_le zero_lt_one hm)
    (scalar_fourth_implicit h (lt_of_lt_of_le zero_lt_one hK) hmean)

/-- Homogeneous directional version, including the zero direction. -/
theorem directional_fourth_offset {X : Ω → ι → ℝ} {K : ℝ}
    (hsg : SubGaussianMGF μ X K) (hiso : CentredIsotropic μ X) (hK : 1 ≤ K)
    (u : ι → ℝ) :
    (∫ ω, (u ⬝ᵥ X ω) ^ 4 ∂μ) ≤
      ((499 / 100 : ℝ) * K ^ 2 * logParameter K + 1 / 2) * (u ⬝ᵥ u) ^ 2 := by
  by_cases hu : u = 0
  · simp [hu]
  have hu2 : 0 < u ⬝ᵥ u := by
    simpa only [star_trivial] using Matrix.dotProduct_star_self_pos_iff.mpr hu
  let r := Real.sqrt (u ⬝ᵥ u)
  have hr : 0 < r := Real.sqrt_pos.2 hu2
  have hr2 : r ^ 2 = u ⬝ᵥ u := Real.sq_sqrt hu2.le
  let v : ι → ℝ := r⁻¹ • u
  have hv : v ⬝ᵥ v = 1 := by
    simp only [v, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    calc
      r⁻¹ * (r⁻¹ * (u ⬝ᵥ u)) = (u ⬝ᵥ u) / r ^ 2 := by ring
      _ = 1 := by rw [hr2, div_self hu2.ne']
  have hs : HasSubgaussianMGF (fun ω => v ⬝ᵥ X ω) ⟨K ^ 2, sq_nonneg K⟩ μ := by
    simpa only [hv, mul_one] using hsg.directional v
  have hm : (∫ ω, (v ⬝ᵥ X ω) ^ 2 ∂μ) = 1 := (hiso.second_moment v).trans hv
  have hpoint (ω : Ω) : (u ⬝ᵥ X ω) ^ 4 = r ^ 4 * (v ⬝ᵥ X ω) ^ 4 := by
    simp only [v, smul_dotProduct, smul_eq_mul, mul_pow]
    field_simp [hr.ne']
  calc
    _ = r ^ 4 * (∫ ω, (v ⬝ᵥ X ω) ^ 4 ∂μ) := by
      simp_rw [hpoint]
      rw [integral_const_mul]
    _ ≤ r ^ 4 * ((499 / 100 : ℝ) * K ^ 2 * logParameter K + 1 / 2) :=
      mul_le_mul_of_nonneg_left (scalar_fourth_offset hs hK hm) (by positivity)
    _ = _ := by rw [← hr2]; ring

variable [DecidableEq ι]

/-- A positive-semidefinite trace-one matrix has square trace at most one. -/
theorem trace_square_le_one {P : Matrix ι ι ℝ} (hP : P.PosSemidef)
    (htrace : Matrix.trace P = 1) : Matrix.trace (P ^ 2) ≤ 1 := by
  have hs : Matrix.trace (P ^ 2) ≤ (Matrix.trace P) ^ 2 := by
    rw [real_spectral_trace hP.isHermitian, real_spectral_trace_square hP.isHermitian]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hP.eigenvalues_nonneg i)
  simpa [htrace] using hs

/-- The spectral second-moment estimate in `eq:app-low-Tmoment`. -/
theorem quadratic_second_lower_general_strong {X : Ω → ι → ℝ} {K : ℝ}
    (hsg : SubGaussianMGF μ X K) (hiso : CentredIsotropic μ X) (hK : 1 ≤ K)
    (P : Matrix ι ι ℝ) (hP : P.PosSemidef) (htrace : Matrix.trace P = 1) :
    (∫ ω, quadraticForm P X ω ^ 2 ∂μ) ≤
      (5 / 3 : ℝ) * K ^ 2 * logParameter K * (1 + 2 * Matrix.trace (P ^ 2)) := by
  have hh : ∀ u : ι → ℝ, (∫ ω, (u ⬝ᵥ X ω) ^ 4 ∂μ) ≤
      (5 * K ^ 2 * logParameter K) * (u ⬝ᵥ u) ^ 2 := by
    intro u
    have hd := directional_fourth hsg hiso hK u
    have hc : fourthMomentConstant K ≤ 5 * K ^ 2 * logParameter K := by
      unfold fourthMomentConstant
      split_ifs with hK1
      · subst K; norm_num [logParameter]
      · exact le_rfl
    exact hd.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _))
  have hL := one_le_logParameter hK
  have h := quadratic_second_trace_one_of_directional_fourth hsg hiso.measurable
    (by positivity : 0 ≤ 5 * K ^ 2 * logParameter K) hh P hP htrace
  nlinarith

/-- The offset second-moment estimate in `eq:app-low-Tmoment`. -/
theorem quadratic_second_lower_offset {X : Ω → ι → ℝ} {K : ℝ}
    (hsg : SubGaussianMGF μ X K) (hiso : CentredIsotropic μ X) (hK : 1 ≤ K)
    (P : Matrix ι ι ℝ) (hP : P.PosSemidef) (htrace : Matrix.trace P = 1) :
    (∫ ω, quadraticForm P X ω ^ 2 ∂μ) ≤
      (499 / 100 : ℝ) * K ^ 2 * logParameter K + 1 / 2 := by
  have hL := one_le_logParameter hK
  have hm : 0 ≤ (499 / 100 : ℝ) * K ^ 2 * logParameter K + 1 / 2 := by positivity
  have h := quadratic_second_trace_one_of_directional_fourth hsg hiso.measurable
    hm (directional_fourth_offset hsg hiso hK) P hP htrace
  have hs := trace_square_le_one hP htrace
  nlinarith [mul_nonneg hm (sub_nonneg.mpr hs)]

/-- The endpoint uses only the Gaussian fourth-moment bound. -/
theorem quadratic_second_lower_one {X : Ω → ι → ℝ}
    (hsg : SubGaussianMGF μ X 1) (hiso : CentredIsotropic μ X)
    (P : Matrix ι ι ℝ) (hP : P.PosSemidef) (htrace : Matrix.trace P = 1) :
    (∫ ω, quadraticForm P X ω ^ 2 ∂μ) ≤ 3 := by
  simpa [fourthMomentConstant, htrace] using quadratic_second_moment hsg hiso
    (by norm_num : (1 : ℝ) ≤ 1) P hP

/-- Specialization of the sharp Laplace bound to a trace-one quadratic form.
The MGF and isotropy hypotheses discharge all moment and product integrability
requirements; only the exact-shift comparison and its mixed-cost cap remain. -/
theorem quadratic_lower_laplace_general {X : Ω → ι → ℝ} {K : ℝ}
    (hsg : SubGaussianMGF μ X K) (hiso : CentredIsotropic μ X) (hK : 1 ≤ K)
    (P B : Matrix ι ι ℝ) (hP : P.PosSemidef) (hB : B.PosSemidef)
    (htrace : Matrix.trace P = 1) {Δ : Ω → ℝ} {b ℓ : ℝ}
    (hΔ : AEMeasurable Δ μ) (hΔ0 : ∀ ω, 0 ≤ Δ ω)
    (hcost : (∫ ω, quadraticForm P X ω * quadraticForm B X ω ∂μ) ≤ b)
    (hcomparison : ∀ ω, quadraticForm P X ω ≤ (1 + quadraticForm B X ω) * Δ ω)
    (hℓ : 0 ≤ ℓ) :
    Integrable (fun ω => Real.exp (-ℓ * (1 + b) * Δ ω)) μ ∧
      (∫ ω, Real.exp (-ℓ * (1 + b) * Δ ω) ∂μ) ≤
        Real.exp (-ℓ / (1 + ((499 / 100 : ℝ) * K ^ 2 * logParameter K) * ℓ)) := by
  have hTP := hsg.quadratic_memLp_two P
  have hQB := hsg.quadratic_memLp_two B
  have hh := lower_laplace (m2 := (499 / 100 : ℝ) * K ^ 2 * logParameter K + 1 / 2)
    (hTP.integrable (by norm_num)) hTP.integrable_sq (hTP.integrable_mul hQB)
    hQB.aestronglyMeasurable.aemeasurable hΔ (quadraticForm_nonneg hP X) (quadraticForm_nonneg hB X) hΔ0
    ((hiso.quadratic_mean P).trans htrace)
    (quadratic_second_lower_offset hsg hiso hK P hP htrace) hcost hcomparison hℓ
  simpa only [add_sub_cancel_right] using hh

/-- The endpoint version has the exact fluctuation coefficient `ν = 5/2`. -/
theorem quadratic_lower_laplace_one {X : Ω → ι → ℝ}
    (hsg : SubGaussianMGF μ X 1) (hiso : CentredIsotropic μ X)
    (P B : Matrix ι ι ℝ) (hP : P.PosSemidef) (hB : B.PosSemidef)
    (htrace : Matrix.trace P = 1) {Δ : Ω → ℝ} {b ℓ : ℝ}
    (hΔ : AEMeasurable Δ μ) (hΔ0 : ∀ ω, 0 ≤ Δ ω)
    (hcost : (∫ ω, quadraticForm P X ω * quadraticForm B X ω ∂μ) ≤ b)
    (hcomparison : ∀ ω, quadraticForm P X ω ≤ (1 + quadraticForm B X ω) * Δ ω)
    (hℓ : 0 ≤ ℓ) :
    Integrable (fun ω => Real.exp (-ℓ * (1 + b) * Δ ω)) μ ∧
      (∫ ω, Real.exp (-ℓ * (1 + b) * Δ ω) ∂μ) ≤
        Real.exp (-ℓ / (1 + (5 / 2 : ℝ) * ℓ)) := by
  have hTP := hsg.quadratic_memLp_two P
  have hQB := hsg.quadratic_memLp_two B
  have hh := lower_laplace (m2 := 3)
    (hTP.integrable (by norm_num)) hTP.integrable_sq (hTP.integrable_mul hQB)
    hQB.aestronglyMeasurable.aemeasurable hΔ (quadraticForm_nonneg hP X) (quadraticForm_nonneg hB X) hΔ0
    ((hiso.quadratic_mean P).trans htrace)
    (quadratic_second_lower_one hsg hiso P hP htrace) hcost hcomparison hℓ
  norm_num at hh ⊢
  exact hh

end
end SingularValueBounds.KL
