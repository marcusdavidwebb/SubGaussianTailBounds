import SingularValueBounds.Shifts.UpperDeterminant
import SingularValueBounds.QuadraticForms.GaussianComparison
import Mathlib.Probability.Moments.Basic

/-! # The upper-shift tail bound of Lemma 3.2 -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace SingularValueBounds

set_option maxHeartbeats 400000

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [Nonempty ι] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [DecidableEq ι] [Nonempty ι] in
private theorem prod_inv_sqrt_le {a : ι → ℝ} {c d : ℝ}
    (ha : ∀ i, 0 < a i) (hd : 0 < d)
    (hprod : Real.exp (-c) * d ≤ ∏ i, a i) :
    (∏ i, (Real.sqrt (a i))⁻¹) ≤ Real.exp (c / 2) / Real.sqrt d := by
  have hp0 : 0 < ∏ i, Real.sqrt (a i) := Finset.prod_pos (fun i _ => Real.sqrt_pos.2 (ha i))
  have hp2 : (∏ i, Real.sqrt (a i)) ^ 2 = ∏ i, a i := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun i _ => Real.sq_sqrt (ha i).le)
  have he2 : Real.exp (-(c / 2)) ^ 2 = Real.exp (-c) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hbase : Real.exp (-(c / 2)) * Real.sqrt d ≤ ∏ i, Real.sqrt (a i) := by
    nlinarith [Real.sq_sqrt hd.le, Real.sqrt_pos.2 hd, Real.exp_pos (-(c / 2))]
  rw [Finset.prod_inv_distrib]
  have hi := inv_le_inv₀ hp0 (mul_pos (Real.exp_pos (-(c / 2))) (Real.sqrt_pos.2 hd))
  have := hi.2 hbase
  convert this using 1
  rw [mul_inv, ← Real.exp_neg]
  simp only [neg_neg, div_eq_mul_inv]

/-- A direct Chernoff estimate for the exact upper shift. -/
theorem upperShift_tail_chernoff {X : Ω → ι → ℝ} {K h l : ℝ}
    (hsg : SubGaussianMGF μ X K) (hm : Measurable X) (hK : 0 < K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (hl : 0 < l) (hlh : 2 * K ^ 2 * l < h) :
    μ.real {ω | h < upperShift R hR (X ω)} ≤
      Real.exp (-l * (1 - K ^ 2 * Matrix.trace R)) /
        Real.sqrt (1 - 2 * K ^ 2 * l / h) := by
  let r := hR.isHermitian.eigenvalues
  let b := fun i => spectralUpperResolvent r h i +
    spectralUpperResolvent r h i ^ 2 / spectralUpperDrop r h
  have hr : ∀ i, 0 < r i := hR.eigenvalues_pos
  have ht : 0 < 2 * K ^ 2 * l := by positivity
  have hh : 0 < h := ht.trans hlh
  have hd := spectralUpperDrop_pos hr hh
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    exact add_nonneg (spectralUpperResolvent_pos hr hh.le i).le
      (div_nonneg (sq_nonneg _) hd.le)
  have hdet := upper_determinant_factor_bound hr ht hlh
  have hs : upperCriterion R h =
      (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) * Matrix.diagonal b *
        star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) := by
    simpa only [b, spectralUpperResolvent, spectralUpperDrop_eq hr hh.le] using
      upperCriterion_spectral hR hh.le
  have hmg := unitary_quadratic_exponential_bound hsg hm
    hR.isHermitian.eigenvectorUnitary b hb l hl.le hdet.1
  rw [← hs] at hmg
  have htrace : Matrix.trace R = ∑ i, r i := real_spectral_trace hR.isHermitian
  have htrace0 : 0 < Matrix.trace R := by
    rw [htrace]
    exact Finset.sum_pos (fun i _ => hr i) Finset.univ_nonempty
  have hdiff : 0 < 1 - 2 * K ^ 2 * l / h := by
    exact sub_pos.2 ((div_lt_one hh).2 hlh)
  have hp := prod_inv_sqrt_le (c := 2 * K ^ 2 * l * Matrix.trace R) hdet.1 hdiff
    (by simpa only [htrace] using hdet.2)
  have hmark := measure_ge_le_exp_mul_mgf (μ := μ) (X := quadraticForm (upperCriterion R h) X)
    1 hl.le hmg.1
  have hevent : μ.real {ω | h < upperShift R hR (X ω)} ≤
      μ.real {ω | 1 ≤ quadraticForm (upperCriterion R h) X ω} := by
    apply measureReal_mono
    · intro ω hω
      exact (upperShift_lt_iff hR (X ω) hh).1 hω |>.le
    · exact measure_ne_top _ _
  calc
    _ ≤ Real.exp (-l) * (∏ i, (Real.sqrt (1 - 2 * K ^ 2 * l * b i))⁻¹) := by
      refine hevent.trans (hmark.trans ?_)
      simpa only [mgf, mul_one] using mul_le_mul_of_nonneg_left hmg.2 (Real.exp_pos (-l)).le
    _ ≤ Real.exp (-l) * (Real.exp ((2 * K ^ 2 * l * Matrix.trace R) / 2) /
        Real.sqrt (1 - 2 * K ^ 2 * l / h)) :=
      mul_le_mul_of_nonneg_left hp (Real.exp_pos (-l)).le
    _ = _ := by
      rw [← mul_div_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The normalized upper-shift tail, with the original sub-Gaussian MGF
hypotheses. This is equation (5.1), valid for every `0 < τ < 1/2`. -/
theorem upperShift_tail {X : Ω → ι → ℝ} {K φ τ : ℝ}
    (hsg : SubGaussianMGF μ X K) (hm : Measurable X) (hK : 0 < K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (htr : Matrix.trace R ≤ φ) (hr : 0 < 1 - K ^ 2 * φ)
    (hτ : 0 < τ) (hτ1 : τ < 1 / 2) (y : ℝ) (hy : 0 ≤ y) :
    μ.real {ω | y < (1 - K ^ 2 * φ) * upperShift R hR (X ω)} ≤
      (Real.sqrt (1 - 2 * τ))⁻¹ * Real.exp (-(τ * y / K ^ 2)) := by
  have hsq : 0 < K ^ 2 := sq_pos_of_pos hK
  have hd : 0 < 1 - 2 * τ := by linarith
  rcases hy.eq_or_lt with hy | hy
  · subst y
    have hs : Real.sqrt (1 - 2 * τ) ≤ 1 := by
      exact (Real.sqrt_le_one).2 (by linarith)
    have hi : 1 ≤ (Real.sqrt (1 - 2 * τ))⁻¹ := by
      exact (one_le_inv₀ (Real.sqrt_pos.2 hd)).2 hs
    simpa using (measureReal_le_one (μ := μ)).trans hi
  · let h := y / (1 - K ^ 2 * φ)
    let l := τ * h / K ^ 2
    have hh : 0 < h := div_pos hy hr
    have hl : 0 < l := div_pos (mul_pos hτ hh) hsq
    have hid : 2 * K ^ 2 * l = 2 * τ * h := by
      dsimp [l]
      field_simp
      ring
    have hlt : 2 * K ^ 2 * l < h := by
      rw [hid]
      nlinarith only [mul_pos hh hd]
    have ht := upperShift_tail_chernoff hsg hm hK hR hl hlt
    have hevent : {ω | y < (1 - K ^ 2 * φ) * upperShift R hR (X ω)} =
        {ω | h < upperShift R hR (X ω)} := by
      ext ω
      change y < (1 - K ^ 2 * φ) * upperShift R hR (X ω) ↔
        y / (1 - K ^ 2 * φ) < upperShift R hR (X ω)
      rw [div_lt_iff₀ hr, mul_comm (upperShift R hR (X ω))]
    rw [hevent]
    have hden : 1 - 2 * K ^ 2 * l / h = 1 - 2 * τ := by
      rw [hid, mul_div_cancel_right₀ _ hh.ne']
    rw [hden] at ht
    have hexp : -l * (1 - K ^ 2 * Matrix.trace R) ≤ -(τ * y / K ^ 2) := by
      have hcomp : 1 - K ^ 2 * φ ≤ 1 - K ^ 2 * Matrix.trace R := by
        nlinarith [mul_le_mul_of_nonneg_left htr hsq.le]
      have hb := mul_le_mul_of_nonneg_left hcomp hl.le
      have heq : l * (1 - K ^ 2 * φ) = τ * y / K ^ 2 := by
        dsimp [l, h]
        field_simp
        ring
      linarith
    exact ht.trans (by
      simpa only [div_eq_mul_inv, mul_comm] using
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hexp) (inv_nonneg.2 (Real.sqrt_nonneg _)))

/-- The `τ = 1/3` specialization used in both upper-shift moment arguments. -/
theorem upperShift_tail_third {X : Ω → ι → ℝ} {K φ : ℝ}
    (hsg : SubGaussianMGF μ X K) (hm : Measurable X) (hK : 0 < K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (htr : Matrix.trace R ≤ φ) (hr : 0 < 1 - K ^ 2 * φ)
    (y : ℝ) (hy : 0 ≤ y) :
    μ.real {ω | y < (1 - K ^ 2 * φ) * upperShift R hR (X ω)} ≤
      Real.sqrt 3 * Real.exp (-(y / (3 * K ^ 2))) := by
  have h := upperShift_tail hsg hm hK hR htr hr
    (show (0 : ℝ) < 1 / 3 by norm_num) (by norm_num) y hy
  have hs : (Real.sqrt (1 - 2 * (1 / 3 : ℝ)))⁻¹ = Real.sqrt 3 := by
    rw [← Real.sqrt_inv]
    norm_num
  rw [hs] at h
  convert h using 1
  congr 2
  ring


end SingularValueBounds
