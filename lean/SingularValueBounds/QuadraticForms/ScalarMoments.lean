import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import SingularValueBounds.QuadraticForms.Basic

/-!
# Scalar moment inequalities for Lemma 4.2

The moment comparison below is the size-biased Jensen inequality expressed
using a pointwise Bernoulli tangent. It therefore requires no change of measure.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SingularValueBounds

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem scalar_one_le_fourth_moment [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (h2 : Integrable (fun ω => Y ω ^ 2) μ)
    (h4 : Integrable (fun ω => Y ω ^ 4) μ)
    (hmean : (∫ ω, Y ω ^ 2 ∂μ) = 1) : 1 ≤ ∫ ω, Y ω ^ 4 ∂μ := by
  have hi : 0 ≤ ∫ ω, Y ω ^ 4 - 2 * Y ω ^ 2 + 1 ∂μ :=
    integral_nonneg (fun ω => by
      change 0 ≤ Y ω ^ 4 - 2 * Y ω ^ 2 + 1
      nlinarith [sq_nonneg (Y ω ^ 2 - 1)])
  rw [integral_add (f := fun ω => Y ω ^ 4 - 2 * Y ω ^ 2)
    (h4.sub (h2.const_mul 2)) (integrable_const 1),
    integral_sub h4 (h2.const_mul 2), integral_const_mul, hmean] at hi
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hi
  linarith

/-- A polynomial tangent inequality obtained from Bernoulli's inequality. -/
theorem power_size_bias_tangent (m t : ℝ) (hm : 0 < m) (ht : 0 ≤ t) (n : ℕ) :
    m ^ n * (((n : ℝ) + 1) * t ^ 2 - (n : ℝ) * m * t) ≤ t ^ (n + 2) := by
  have hb := one_add_mul_sub_le_pow
    (show (-1 : ℝ) ≤ t / m by
      have := div_nonneg ht hm.le
      linarith) (n + 1)
  have hp := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ m ^ (n + 1) * t by positivity)
  calc
    _ = (1 + ((n + 1 : ℕ) : ℝ) * (t / m - 1)) * (m ^ (n + 1) * t) := by
      simp only [pow_succ, Nat.cast_add, Nat.cast_one]
      field_simp [hm.ne']
      ring
    _ ≤ (t / m) ^ (n + 1) * (m ^ (n + 1) * t) := hp
    _ = t ^ (n + 2) := by
      rw [div_pow]
      field_simp [hm.ne']
      ring

/-- If `E Y² = 1`, then `E Y^(2n+2) ≥ (E Y⁴)^n`. -/
theorem scalar_even_moment_lower [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hi : ∀ n : ℕ, Integrable (fun ω => Y ω ^ n) μ)
    (hmean : (∫ ω, Y ω ^ 2 ∂μ) = 1) (n : ℕ) :
    (∫ ω, Y ω ^ 4 ∂μ) ^ n ≤ ∫ ω, Y ω ^ (2 * (n + 1)) ∂μ := by
  let m := ∫ ω, Y ω ^ 4 ∂μ
  have hm1 : 1 ≤ m := scalar_one_le_fourth_moment (hi 2) (hi 4) hmean
  have hm : 0 < m := lt_of_lt_of_le zero_lt_one hm1
  cases n with
  | zero => simpa using hmean.ge
  | succ n =>
    have hpoly : Integrable (fun ω => m ^ n *
        (((n : ℝ) + 1) * Y ω ^ 4 - (n : ℝ) * m * Y ω ^ 2)) μ :=
      (((hi 4).const_mul ((n : ℝ) + 1)).sub ((hi 2).const_mul ((n : ℝ) * m))).const_mul _
    have hle := integral_mono hpoly (hi (2 * (n + 2))) (fun ω => by
      have hp := power_size_bias_tangent m (Y ω ^ 2) hm (sq_nonneg _) n
      simpa only [← pow_mul, show 2 * 2 = 4 by norm_num] using hp)
    rw [integral_const_mul, integral_sub ((hi 4).const_mul ((n : ℝ) + 1))
      ((hi 2).const_mul ((n : ℝ) * m)), integral_const_mul, integral_const_mul, hmean] at hle
    change m ^ (n + 1) ≤ _
    calc
      m ^ (n + 1) = m ^ n * (((n : ℝ) + 1) * m - (n : ℝ) * m * 1) := by ring
      _ ≤ _ := hle

theorem scalar_cosh_integrable {Y : Ω → ℝ}
    (he : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Y ω)) μ) (t : ℝ) :
    Integrable (fun ω => Real.cosh (t * Y ω)) μ := by
  simpa only [Real.cosh_eq, neg_mul] using! ((he t).add (he (-t))).div_const 2

/-- The cosh moment comparison behind the isotropy-improved fourth moment.
Only finite partial sums are integrated; their bound passes to the series. -/
theorem scalar_cosh_fourth_lower [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hi : ∀ n : ℕ, Integrable (fun ω => Y ω ^ n) μ)
    (he : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Y ω)) μ)
    (hmean : (∫ ω, Y ω ^ 2 ∂μ) = 1) (t : ℝ) :
    Real.cosh (t * Real.sqrt (∫ ω, Y ω ^ 4 ∂μ)) ≤
      (∫ ω, Y ω ^ 4 ∂μ) * (∫ ω, Real.cosh (t * Y ω) ∂μ) := by
  let m := ∫ ω, Y ω ^ 4 ∂μ
  have hm1 : 1 ≤ m := scalar_one_le_fourth_moment (hi 2) (hi 4) hmean
  have hm : 0 ≤ m := zero_le_one.trans hm1
  have hmom : ∀ n : ℕ, m ^ n ≤ m * (∫ ω, Y ω ^ (2 * n) ∂μ) := by
    intro n
    cases n with
    | zero => simpa using hm1
    | succ n =>
      have hh := mul_le_mul_of_nonneg_left (scalar_even_moment_lower hi hmean n) hm
      change m ^ (n + 1) ≤ _
      rw [pow_succ']
      exact hh
  have hiterm : ∀ n : ℕ, Integrable
      (fun ω => (t * Y ω) ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) μ := by
    intro n
    simpa only [mul_pow] using ((hi (2 * n)).const_mul (t ^ (2 * n))).div_const _
  have hpos : ∀ (x : ℝ) (n : ℕ), 0 ≤ x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) := by
    intro x n
    rw [pow_mul]
    positivity
  have hseries := Real.hasSum_cosh (t * Real.sqrt m)
  rw [← hseries.tsum_eq]
  apply hseries.summable.tsum_le_of_sum_range_le
  intro N
  calc
    (∑ n ∈ Finset.range N, (t * Real.sqrt m) ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) ≤
        m * ∑ n ∈ Finset.range N,
          (∫ ω, (t * Y ω) ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) ∂μ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n _
      rw [mul_pow, pow_mul (Real.sqrt m), Real.sq_sqrt hm]
      simp_rw [mul_pow]
      rw [integral_div, integral_const_mul]
      have ht : 0 ≤ t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) := hpos t n
      have hh := mul_le_mul_of_nonneg_left (hmom n) ht
      convert! hh using 1 <;> ring
    _ = m * ∫ ω, ∑ n ∈ Finset.range N,
        (t * Y ω) ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) ∂μ := by
      rw [integral_finset_sum _ (fun n _ => hiterm n)]
    _ ≤ m * (∫ ω, Real.cosh (t * Y ω) ∂μ) := by
      apply mul_le_mul_of_nonneg_left _ hm
      apply integral_mono (integrable_finset_sum _ (fun n _ => hiterm n))
        (scalar_cosh_integrable he t)
      intro ω
      have hs := (Real.hasSum_cosh (t * Y ω)).summable.sum_le_tsum
        (Finset.range N) (fun n _ => hpos (t * Y ω) n)
      simpa only [← Real.cosh_eq_tsum] using hs

/-- Averaging the bounds at `t` and `-t` bounds the hyperbolic cosine. -/
theorem scalar_cosh_upper {Y : Ω → ℝ} {K : ℝ}
    (h : HasSubgaussianMGF Y ⟨K ^ 2, sq_nonneg K⟩ μ) (t : ℝ) :
    (∫ ω, Real.cosh (t * Y ω) ∂μ) ≤ Real.exp (K ^ 2 * t ^ 2 / 2) := by
  have hp := h.mgf_le t
  have hn := h.mgf_le (-t)
  simp only [mgf, NNReal.toReal, neg_sq] at hp hn
  calc
    (∫ ω, Real.cosh (t * Y ω) ∂μ) =
        ((∫ ω, Real.exp (t * Y ω) ∂μ) + (∫ ω, Real.exp (-t * Y ω) ∂μ)) / 2 := by
      simp_rw [Real.cosh_eq, ← neg_mul]
      rw [integral_div, integral_add (h.integrable_exp_mul t) (h.integrable_exp_mul (-t))]
    _ ≤ _ := by linarith

/-- The implicit fourth-moment inequality used in the proof of Lemma 4.2. -/
theorem scalar_fourth_implicit [IsProbabilityMeasure μ] {Y : Ω → ℝ} {K : ℝ}
    (h : HasSubgaussianMGF Y ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hK : 0 < K) (hmean : (∫ ω, Y ω ^ 2 ∂μ) = 1) :
    (∫ ω, Y ω ^ 4 ∂μ) / (2 * K ^ 2) ≤ Real.log (2 * (∫ ω, Y ω ^ 4 ∂μ)) := by
  have hi : ∀ n : ℕ, Integrable (fun ω => Y ω ^ n) μ :=
    fun n => integrable_pow_of_integrable_exp_mul (by norm_num : (1 : ℝ) ≠ 0)
      (h.integrable_exp_mul 1) (h.integrable_exp_mul (-1)) n
  let m := ∫ ω, Y ω ^ 4 ∂μ
  let t := Real.sqrt m / K ^ 2
  have hm1 : 1 ≤ m := scalar_one_le_fourth_moment (hi 2) (hi 4) hmean
  have hm : 0 < m := lt_of_lt_of_le zero_lt_one hm1
  have hc := (scalar_cosh_fourth_lower hi h.integrable_exp_mul hmean t).trans
    (mul_le_mul_of_nonneg_left (scalar_cosh_upper h t) hm.le)
  have he : Real.exp (t * Real.sqrt m) ≤ 2 * m * Real.exp (K ^ 2 * t ^ 2 / 2) := by
    rw [Real.cosh_eq] at hc
    have hn := Real.exp_pos (-(t * Real.sqrt m))
    linarith
  have hl := Real.log_le_log (Real.exp_pos (t * Real.sqrt m)) he
  rw [Real.log_exp, Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at hl
  have ht : t * Real.sqrt m - K ^ 2 * t ^ 2 / 2 = m / (2 * K ^ 2) := by
    dsimp [t]
    field_simp [hK.ne']
    nlinarith [Real.sq_sqrt hm.le]
  change m / (2 * K ^ 2) ≤ Real.log (2 * m)
  linarith

private theorem log_twenty_lt_three : Real.log 20 < 3 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 20)).2
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 9
  have hn : (20 : ℝ) < ∑ i ∈ Finset.range 9, (3 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hn.trans_le hs

/-- Solving the implicit fourth-moment inequality gives the paper's explicit
constant `5 K² log(eK)`. -/
theorem fourth_implicit_bound {m K : ℝ} (hK : 1 ≤ K) (hm : 0 < m)
    (hi : m / (2 * K ^ 2) ≤ Real.log (2 * m)) :
    m ≤ 5 * K ^ 2 * logParameter K := by
  let L := logParameter K
  let C := 5 * K ^ 2 * L
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hL1 : 1 ≤ L := one_le_logParameter hK
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hC : 0 < C := by dsimp [C]; positivity
  have hlogK : Real.log K = L - 1 := by dsimp [L, logParameter]; ring
  have hlog : Real.log (10 * K ^ 2 * L) < (5 / 2 : ℝ) * L := by
    have hid : Real.log (10 * K ^ 2 * L) =
        Real.log 20 + 2 * Real.log K + Real.log (L / 2) := by
      rw [show 10 * K ^ 2 * L = 20 * K ^ 2 * (L / 2) by ring,
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (pow_ne_zero 2 hK0.ne'), Real.log_pow]
      norm_num
    have hj := Real.log_le_sub_one_of_pos (show 0 < L / 2 by positivity)
    rw [hid, hlogK]
    linarith [log_twenty_lt_three]
  have hbase : Real.log (2 * C) < C / (2 * K ^ 2) := by
    have heq : C / (2 * K ^ 2) = (5 / 2 : ℝ) * L := by
      dsimp [C]
      field_simp [hK0.ne']
    rw [heq]
    simpa only [C, show 2 * (5 * K ^ 2 * L) = 10 * K ^ 2 * L by ring] using hlog
  by_contra hmc
  have hmc' : C < m := lt_of_not_ge hmc
  let r := m / C
  have hr : 0 < r := div_pos hm hC
  have hr1 : 1 ≤ r := (le_div_iff₀ hC).2 (by linarith)
  have hratio : 1 ≤ C / (2 * K ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * K ^ 2)).2
    dsimp [C]
    nlinarith [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hL1)]
  have hprod : 2 * m = (2 * C) * r := by dsimp [r]; field_simp [hC.ne']
  have hl : Real.log (2 * m) < m / (2 * K ^ 2) := by
    calc
      Real.log (2 * m) = Real.log (2 * C) + Real.log r := by
        rw [hprod, Real.log_mul (by positivity) hr.ne']
      _ ≤ Real.log (2 * C) + (r - 1) :=
        add_le_add_right (Real.log_le_sub_one_of_pos hr) _
      _ < C / (2 * K ^ 2) + (r - 1) := add_lt_add_left hbase _
      _ ≤ r * (C / (2 * K ^ 2)) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hratio)]
      _ = m / (2 * K ^ 2) := by dsimp [r]; field_simp [hC.ne']
  exact (not_lt_of_ge hi) hl

/-- The sharp-in-`K` scalar fourth-moment estimate for unit-variance
sub-Gaussian random variables. -/
theorem scalar_fourth_general [IsProbabilityMeasure μ] {Y : Ω → ℝ} {K : ℝ}
    (h : HasSubgaussianMGF Y ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hK : 1 ≤ K) (hmean : (∫ ω, Y ω ^ 2 ∂μ) = 1) :
    (∫ ω, Y ω ^ 4 ∂μ) ≤ 5 * K ^ 2 * logParameter K := by
  have hi : ∀ n : ℕ, Integrable (fun ω => Y ω ^ n) μ :=
    fun n => integrable_pow_of_integrable_exp_mul (by norm_num : (1 : ℝ) ≠ 0)
      (h.integrable_exp_mul 1) (h.integrable_exp_mul (-1)) n
  have hm := scalar_one_le_fourth_moment (hi 2) (hi 4) hmean
  exact fourth_implicit_bound hK (lt_of_lt_of_le zero_lt_one hm)
    (scalar_fourth_implicit h (lt_of_lt_of_le zero_lt_one hK) hmean)

/-- Finite Taylor sums for `cosh` can be integrated term by term. -/
theorem scalar_cosh_partial_lower {Y : Ω → ℝ}
    (hi : ∀ n : ℕ, Integrable (fun ω => Y ω ^ n) μ)
    (he : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Y ω)) μ) (t : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, t ^ (2 * n) * (∫ ω, Y ω ^ (2 * n) ∂μ) /
      (Nat.factorial (2 * n) : ℝ)) ≤ ∫ ω, Real.cosh (t * Y ω) ∂μ := by
  have hiterm : ∀ n : ℕ, Integrable
      (fun ω => (t * Y ω) ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) μ := by
    intro n
    simpa only [mul_pow] using ((hi (2 * n)).const_mul (t ^ (2 * n))).div_const _
  have hp := integral_mono (integrable_finset_sum (Finset.range N) (fun n _ => hiterm n))
    (scalar_cosh_integrable he t) (fun ω => by
      have hs := (Real.hasSum_cosh (t * Y ω)).summable.sum_le_tsum
        (Finset.range N) (fun n _ => by rw [pow_mul]; positivity)
      simpa only [← Real.cosh_eq_tsum] using hs)
  rw [integral_finset_sum _ (fun n _ => hiterm n)] at hp
  simpa only [mul_pow, integral_div, integral_const_mul] using hp

/-- At the unit sub-Gaussian endpoint the equal quadratic Taylor coefficients
force the Gaussian fourth-moment bound `3`. -/
theorem scalar_fourth_unit [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (h : HasSubgaussianMGF Y 1 μ) (hmean : (∫ ω, Y ω ^ 2 ∂μ) = 1) :
    (∫ ω, Y ω ^ 4 ∂μ) ≤ 3 := by
  have hi : ∀ n : ℕ, Integrable (fun ω => Y ω ^ n) μ :=
    fun n => integrable_pow_of_integrable_exp_mul (by norm_num : (1 : ℝ) ≠ 0)
      (h.integrable_exp_mul 1) (h.integrable_exp_mul (-1)) n
  have hsg : HasSubgaussianMGF Y ⟨(1 : ℝ) ^ 2, sq_nonneg 1⟩ μ := by
    change HasSubgaussianMGF Y (NNReal.mk ((1 : ℝ) ^ 2) _) μ
    simpa using h
  let m := ∫ ω, Y ω ^ 4 ∂μ
  have hlow : ∀ t : ℝ, 1 + t ^ 2 / 2 + t ^ 4 * m / 24 ≤ Real.exp (t ^ 2 / 2) := by
    intro t
    have hp := (scalar_cosh_partial_lower hi h.integrable_exp_mul t 3).trans
      (scalar_cosh_upper hsg t)
    norm_num [Finset.sum_range_succ, Nat.factorial, hmean] at hp
    exact hp
  have hlim : Filter.Tendsto
      (fun s : ℝ => (Real.exp s - (1 + s + s ^ 2 / 2)) / s ^ 2)
      (nhds 0) (nhds 0) := by
    convert! (Real.exp_sub_sum_range_succ_isLittleO_pow 2).tendsto_div_nhds_zero using 1
    funext s
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hbound : m / 6 - 1 / 2 ≤ (0 : ℝ) := by
    apply ge_of_tendsto (x := nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (hlim.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))] with s hs
    have hs0 : 0 < s := hs
    have hp := hlow (Real.sqrt (2 * s))
    have hsq := Real.sq_sqrt (show 0 ≤ 2 * s by positivity)
    have hfour : Real.sqrt (2 * s) ^ 4 = 4 * s ^ 2 := by nlinarith [sq_nonneg s]
    rw [hsq, hfour, show 2 * s / 2 = s by ring] at hp
    apply (le_div_iff₀ (sq_pos_of_pos hs0)).2
    nlinarith
  change m ≤ 3
  linarith

end
end SingularValueBounds
