import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Analytic rules for rational enclosures

The Taylor bounds, argument reductions and rounding lemmas below connect finite
rational inequalities to real exponential and logarithm bounds. The certificate
structures and pilot implications are conditional lemmas; the concrete finite
obligations used by the canonical results are proved separately in Lean.
-/

open Finset

noncomputable section

namespace SingularValueBounds.KL.Certificates

/-- The exponential Taylor sum, including both endpoints. -/
def expTaylor (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (N + 1), x ^ j / (j.factorial : ℝ)

/-- The exponential Taylor upper value before rounding. -/
def expTaylorUpper (N : ℕ) (x : ℝ) : ℝ :=
  expTaylor N x + x ^ (N + 1) / ((N + 1).factorial : ℝ) / (1 - x / (N + 2))

/-- The odd-power logarithm sum. -/
def logTaylor (N : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ range N, 2 * (1 / (2 * (j : ℝ) + 1)) * z ^ (2 * j + 1)

/-- The logarithm Taylor upper value before rounding. -/
def logTaylorUpper (N : ℕ) (z : ℝ) : ℝ :=
  logTaylor N z + 2 * z ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - z ^ 2))

private theorem hasSum_exp (x : ℝ) :
    HasSum (fun j : ℕ => x ^ j / (j.factorial : ℝ)) (Real.exp x) := by
  simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x

/-- Nonnegative Taylor terms give the lower half of (S1.2). -/
theorem expTaylor_le_exp (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    expTaylor N x ≤ Real.exp x :=
  Real.sum_le_exp_of_nonneg hx (N + 1)

/-- Geometric domination of a convergent nonnegative tail. -/
private theorem hasSum_le_geometric {f : ℕ → ℝ} {s c r : ℝ}
    (hs : HasSum f s) (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hdom : ∀ j, f j ≤ c * r ^ j) : s ≤ c / (1 - r) := by
  have hg := (hasSum_geometric_of_lt_one hr₀ hr₁).mul_left c
  simpa only [div_eq_mul_inv] using hasSum_le hdom hs hg

/-- The exponential upper bound with a geometric remainder. -/
theorem exp_le_expTaylorUpper (N : ℕ) {x : ℝ} (hx₀ : 0 ≤ x)
    (hx₁ : x < N + 2) : Real.exp x ≤ expTaylorUpper N x := by
  let n := N + 1
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hr₀ : 0 ≤ x / (n + 1) := div_nonneg hx₀ hn.le
  have hr₁ : x / (n + 1) < 1 := (div_lt_one hn).2 (by dsimp [n]; push_cast; linarith)
  have hs : HasSum (fun j : ℕ => x ^ (j + n) / ((j + n).factorial : ℝ))
      (Real.exp x - expTaylor N x) := by
    exact (hasSum_nat_add_iff' n).2 (hasSum_exp x)
  have hb := hasSum_le_geometric hs hr₀ hr₁ (c := x ^ n / (n.factorial : ℝ)) ?_
  · simpa [expTaylorUpper, n, Nat.cast_add, Nat.cast_one, show (1 : ℝ) + 1 = 2 by norm_num,
      add_assoc] using (sub_le_iff_le_add'.1 hb)
  intro j
  have hf : (n.factorial : ℝ) * (n + 1) ^ j ≤ ((j + n).factorial : ℝ) := by
    have hnat : n.factorial * (n + 1) ^ j ≤ (n + j).factorial :=
      Nat.factorial_mul_pow_le_factorial
    simpa [Nat.add_comm] using (show (n.factorial : ℝ) * ((n : ℝ) + 1) ^ j ≤
      ((n + j).factorial : ℝ) by exact_mod_cast hnat)
  calc
    x ^ (j + n) / ((j + n).factorial : ℝ)
        ≤ x ^ (j + n) / ((n.factorial : ℝ) * (n + 1) ^ j) := by
          exact div_le_div_of_nonneg_left (pow_nonneg hx₀ _) (by positivity) hf
    _ = x ^ n / (n.factorial : ℝ) * (x / (n + 1)) ^ j := by
      rw [pow_add, div_pow]
      ring

/-- The odd logarithm series, in the quotient notation used by S1.2. -/
theorem hasSum_log_ratio {z : ℝ} (hz₀ : 0 ≤ z) (hz₁ : z < 1) :
    HasSum (fun j : ℕ => 2 * (1 / (2 * (j : ℝ) + 1)) * z ^ (2 * j + 1))
      (Real.log ((1 + z) / (1 - z))) := by
  rw [Real.log_div (by linarith : 1 + z ≠ 0) (by linarith : 1 - z ≠ 0)]
  exact Real.hasSum_log_sub_log_of_abs_lt_one (by rwa [abs_of_nonneg hz₀])

/-- Lower logarithm enclosure used by `_log_unit` before rounding down. -/
theorem logTaylor_le_log_ratio (N : ℕ) {z : ℝ} (hz₀ : 0 ≤ z) (hz₁ : z < 1) :
    logTaylor N z ≤ Real.log ((1 + z) / (1 - z)) := by
  exact sum_le_hasSum (range N) (by intros; positivity) (hasSum_log_ratio hz₀ hz₁)

/-- Geometric logarithm remainder used by `_log_unit` and `log_up` at every order. -/
theorem log_ratio_le_logTaylorUpper (N : ℕ) {z : ℝ} (hz₀ : 0 ≤ z) (hz₁ : z < 1) :
    Real.log ((1 + z) / (1 - z)) ≤ logTaylorUpper N z := by
  have hz₂ : z ^ 2 < 1 := by nlinarith
  have hs : HasSum
      (fun j : ℕ => 2 * (1 / (2 * ((j + N : ℕ) : ℝ) + 1)) * z ^ (2 * (j + N) + 1))
      (Real.log ((1 + z) / (1 - z)) - logTaylor N z) :=
    (hasSum_nat_add_iff' N).2 (hasSum_log_ratio hz₀ hz₁)
  have hb := hasSum_le_geometric hs (sq_nonneg z) hz₂
      (c := 2 * z ^ (2 * N + 1) / (2 * (N : ℝ) + 1)) ?_
  · have heq : (2 * z ^ (2 * N + 1) / (2 * (N : ℝ) + 1)) / (1 - z ^ 2) =
        2 * z ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - z ^ 2)) := by rw [div_div]
    rw [heq] at hb
    exact sub_le_iff_le_add'.1 hb
  intro j
  calc
    2 * (1 / (2 * ((j + N : ℕ) : ℝ) + 1)) * z ^ (2 * (j + N) + 1)
        = 2 * z ^ (2 * (j + N) + 1) / (2 * ((j + N : ℕ) : ℝ) + 1) := by ring
    _ ≤ 2 * z ^ (2 * (j + N) + 1) / (2 * (N : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      push_cast
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    _ = 2 * z ^ (2 * N + 1) / (2 * (N : ℝ) + 1) * (z ^ 2) ^ j := by
      rw [show 2 * (j + N) + 1 = (2 * N + 1) + 2 * j by omega, pow_add, pow_mul]
      ring

/-- The logarithm substitution maps `[1,∞)` to `[0,1)`. -/
theorem log_argument_transform {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ (x - 1) / (x + 1) ∧ (x - 1) / (x + 1) < 1 ∧
      (1 + (x - 1) / (x + 1)) / (1 - (x - 1) / (x + 1)) = x := by
  have hd : 0 < x + 1 := by linarith
  refine ⟨div_nonneg (by linarith) hd.le, (div_lt_one hd).2 (by linarith), ?_⟩
  field_simp
  ring

/-- Powers-of-two reduction for the logarithm. -/
theorem log_pow_two_mul (k : ℕ) {u : ℝ} (hu : 0 < u) :
    Real.log ((2 : ℝ) ^ k * u) = Real.log u + (k : ℝ) * Real.log 2 := by
  rw [Real.log_mul (pow_ne_zero _ (by norm_num)) hu.ne', Real.log_pow]
  ring

/-- Reciprocal argument rule for the logarithm. -/
theorem log_reciprocal (x : ℝ) : Real.log (1 / x) = -Real.log x := by
  simp

/-- Positive reciprocal enclosures reverse the endpoints. -/
theorem reciprocal_enclosure {y lo hi : ℝ} (hlo : 0 < lo)
    (hl : lo ≤ y) (hu : y ≤ hi) : 1 / hi ≤ 1 / y ∧ 1 / y ≤ 1 / lo := by
  have hy : 0 < y := hlo.trans_le hl
  exact ⟨one_div_le_one_div_of_le hy hu, one_div_le_one_div_of_le hlo hl⟩

/-- For a negative argument, the lower positive Taylor sum yields an upper bound. -/
theorem exp_neg_le_reciprocal {x lo : ℝ} (hlo : 0 < lo) (hl : lo ≤ Real.exp x) :
    Real.exp (-x) ≤ 1 / lo := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le hlo hl

/-- Outward rounding can only enlarge an already valid interval. -/
theorem outward_rounding {y lo hi roundedLo roundedHi : ℝ}
    (hl : lo ≤ y) (hu : y ≤ hi) (hdl : roundedLo ≤ lo) (huh : hi ≤ roundedHi) :
    roundedLo ≤ y ∧ y ≤ roundedHi := ⟨hdl.trans hl, hu.trans huh⟩

/-- Exact integer floor/ceiling rule at positive scale. -/
theorem scaled_floor_ceil_enclosure (y : ℝ) {scale : ℝ} (hscale : 0 < scale) :
    (⌊scale * y⌋ : ℝ) / scale ≤ y ∧ y ≤ (⌈scale * y⌉ : ℝ) / scale := by
  constructor
  · apply (div_le_iff₀ hscale).2
    simpa [mul_comm] using Int.floor_le (scale * y)
  · apply (le_div_iff₀ hscale).2
    simpa [mul_comm] using Int.le_ceil (scale * y)

/-- Nonnegative interval multiplication, used in the rounded term recurrences of `expi`.
Repeated application also handles `_log_unit`'s powers of `z²`. -/
theorem mul_enclosure_nonneg {a b al au bl bu : ℝ}
    (hal : 0 ≤ al) (hbl : 0 ≤ bl)
    (ha : al ≤ a ∧ a ≤ au) (hb : bl ≤ b ∧ b ≤ bu) :
    al * bl ≤ a * b ∧ a * b ≤ au * bu := by
  constructor
  · exact mul_le_mul ha.1 hb.1 hbl (hal.trans ha.1)
  · exact mul_le_mul ha.2 hb.2 (hbl.trans hb.1) (hal.trans (ha.1.trans ha.2))

/-- Interval addition for accumulated Taylor terms and the `logi` reduction sum. -/
theorem add_enclosure {a b al au bl bu : ℝ}
    (ha : al ≤ a ∧ a ≤ au) (hb : bl ≤ b ∧ b ≤ bu) :
    al + bl ≤ a + b ∧ a + b ≤ au + bu :=
  ⟨add_le_add ha.1 hb.1, add_le_add ha.2 hb.2⟩

/-- Negation reverses the endpoints of an enclosure. -/
theorem neg_enclosure {a lo hi : ℝ} (h : lo ≤ a ∧ a ≤ hi) :
    -hi ≤ -a ∧ -a ≤ -lo := ⟨neg_le_neg h.2, neg_le_neg h.1⟩

/-- Division of a rounded Taylor term by its positive recurrence denominator. -/
theorem div_enclosure_pos {a lo hi d : ℝ} (h : lo ≤ a ∧ a ≤ hi) (hd : 0 < d) :
    lo / d ≤ a / d ∧ a / d ≤ hi / d :=
  ⟨div_le_div_of_nonneg_right h.1 hd.le, div_le_div_of_nonneg_right h.2 hd.le⟩

namespace NumericalCertificateConditions

/-- Finite rational counterpart of `expTaylor`. -/
def expTaylorQ (N : ℕ) (x : ℚ) : ℚ :=
  ∑ j ∈ range (N + 1), x ^ j / (j.factorial : ℚ)

def expTaylorUpperQ (N : ℕ) (x : ℚ) : ℚ :=
  expTaylorQ N x + x ^ (N + 1) / ((N + 1).factorial : ℚ) / (1 - x / (N + 2))

/-- Finite rational counterpart of the odd logarithm sum. -/
def logTaylorQ (N : ℕ) (z : ℚ) : ℚ :=
  ∑ j ∈ range N, 2 * (1 / (2 * (j : ℚ) + 1)) * z ^ (2 * j + 1)

def logTaylorUpperQ (N : ℕ) (z : ℚ) : ℚ :=
  logTaylorQ N z + 2 * z ^ (2 * N + 1) / ((2 * (N : ℚ) + 1) * (1 - z ^ 2))

/-- Finite hypotheses for an exponential enclosure. -/
structure ExpCertificate (N : ℕ) (x lo hi : ℚ) : Prop where
  nonneg : 0 ≤ x
  domain : x < N + 2
  lower : lo ≤ expTaylorQ N x
  upper : expTaylorUpperQ N x ≤ hi

/-- Finite hypotheses for a logarithm enclosure. -/
structure LogCertificate (N : ℕ) (z lo hi : ℚ) : Prop where
  nonneg : 0 ≤ z
  domain : z < 1
  lower : lo ≤ logTaylorQ N z
  upper : logTaylorUpperQ N z ≤ hi

/-- A concrete exponential enclosure predicate. -/
def expHalfPilot : Prop :=
  ExpCertificate 24 (1 / 2) (1648721270700 / 10^12) (1648721270701 / 10^12)

/-- A concrete logarithm enclosure predicate, with `z=1/3` representing `log 2`. -/
def logTwoPilot : Prop :=
  LogCertificate 18 (1 / 3) (693147180559 / 10^12) (693147180560 / 10^12)

end NumericalCertificateConditions

open NumericalCertificateConditions

@[simp] theorem cast_expTaylorQ (N : ℕ) (x : ℚ) :
    (expTaylorQ N x : ℝ) = expTaylor N (x : ℝ) := by
  simp [expTaylorQ, expTaylor]

@[simp] theorem cast_expTaylorUpperQ (N : ℕ) (x : ℚ) :
    (expTaylorUpperQ N x : ℝ) = expTaylorUpper N (x : ℝ) := by
  simp [expTaylorUpperQ, expTaylorUpper]

@[simp] theorem cast_logTaylorQ (N : ℕ) (z : ℚ) :
    (logTaylorQ N z : ℝ) = logTaylor N (z : ℝ) := by
  simp [logTaylorQ, logTaylor]

@[simp] theorem cast_logTaylorUpperQ (N : ℕ) (z : ℚ) :
    (logTaylorUpperQ N z : ℝ) = logTaylorUpper N (z : ℝ) := by
  simp [logTaylorUpperQ, logTaylorUpper]

/-- Analytic consequence of a finite exp certificate, without any analytic premise in it. -/
theorem exp_enclosure_of_certificate {N : ℕ} {x lo hi : ℚ} (h : ExpCertificate N x lo hi) :
    (lo : ℝ) ≤ Real.exp (x : ℝ) ∧ Real.exp (x : ℝ) ≤ (hi : ℝ) := by
  have hx₀ : (0 : ℝ) ≤ x := by exact_mod_cast h.nonneg
  have hx₁ : (x : ℝ) < N + 2 := by exact_mod_cast h.domain
  have hl : (lo : ℝ) ≤ expTaylor N (x : ℝ) := by
    rw [← cast_expTaylorQ]
    exact_mod_cast h.lower
  have hu : expTaylorUpper N (x : ℝ) ≤ (hi : ℝ) := by
    rw [← cast_expTaylorUpperQ]
    exact_mod_cast h.upper
  exact ⟨hl.trans (expTaylor_le_exp N hx₀), (exp_le_expTaylorUpper N hx₀ hx₁).trans hu⟩

/-- Analytic consequence of a finite log certificate. -/
theorem log_enclosure_of_certificate {N : ℕ} {z lo hi : ℚ} (h : LogCertificate N z lo hi) :
    (lo : ℝ) ≤ Real.log ((1 + (z : ℝ)) / (1 - (z : ℝ))) ∧
      Real.log ((1 + (z : ℝ)) / (1 - (z : ℝ))) ≤ (hi : ℝ) := by
  have hz₀ : (0 : ℝ) ≤ z := by exact_mod_cast h.nonneg
  have hz₁ : (z : ℝ) < 1 := by exact_mod_cast h.domain
  have hl : (lo : ℝ) ≤ logTaylor N (z : ℝ) := by
    rw [← cast_logTaylorQ]
    exact_mod_cast h.lower
  have hu : logTaylorUpper N (z : ℝ) ≤ (hi : ℝ) := by
    rw [← cast_logTaylorUpperQ]
    exact_mod_cast h.upper
  exact ⟨hl.trans (logTaylor_le_log_ratio N hz₀ hz₁),
    (log_ratio_le_logTaylorUpper N hz₀ hz₁).trans hu⟩

/-- The exponential pilot has this consequence when its finite predicate is proved. -/
theorem exp_half_of_pilot (h : expHalfPilot) :
    (1648721270700 : ℝ) / 10^12 ≤ Real.exp (1 / 2) ∧
      Real.exp (1 / 2) ≤ (1648721270701 : ℝ) / 10^12 := by
  have hb := exp_enclosure_of_certificate h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at hb
  convert hb using 1 <;> norm_num

/-- The logarithm pilot has this consequence when its finite predicate is proved. -/
theorem log_two_of_pilot (h : logTwoPilot) :
    (693147180559 : ℝ) / 10^12 ≤ Real.log 2 ∧
      Real.log 2 ≤ (693147180560 : ℝ) / 10^12 := by
  have hb := log_enclosure_of_certificate h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at hb
  convert hb using 1 <;> norm_num

end SingularValueBounds.KL.Certificates
