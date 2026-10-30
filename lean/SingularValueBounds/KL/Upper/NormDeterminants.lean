import SingularValueBounds.KL.Upper.ComparisonNorms
import SingularValueBounds.KL.Upper.TailExtension

/-! # The two norm-based determinant bounds J₀ and J₁ (P17)

Supplement equations `eq:app-up-comparison-norms` and
`eq:general-high-kappa-J`. The logarithmic rescaling argument is analytic;
only the two displayed finite Taylor comparisons enter the numerical premise.
-/
open Set
open scoped BigOperators
namespace SingularValueBounds.KL
open Certificates
noncomputable section

def logdetExcess (c : ℝ) : ℝ := -Real.log (1-2*c)-2*c

theorem logdetExcess_quadratic {M c : ℝ} (hM : 0 < M) (hM1 : M < 1/2)
    (hc : 0 ≤ c) (hcM : c ≤ M) :
    logdetExcess c ≤ (c/M)^2*logdetExcess M := by
  let f1 := fun t : ℝ => 2/(1-2*t)-2
  let f2 := fun t : ℝ => 4/(1-2*t)^2
  let f3 := fun t : ℝ => 16/(1-2*t)^3
  have hd (t : ℝ) (ht : t ∈ Icc 0 M) : 0 < 1-2*t := by linarith [ht.2]
  apply quadratic_rescaling_of_third_deriv (f1 := f1) (f2 := f2) (f3 := f3)
    hM hc hcM (by simp [logdetExcess]) (by norm_num [f1])
  · intro t ht
    have hn := (hd t ht).ne'
    have hlin := (hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).const_mul 2)
    convert! ((hlin.log (hd t ht).ne').neg).sub ((hasDerivAt_id t).const_mul 2) using 1 <;>
      (try ext x) <;> simp [logdetExcess,f1,Pi.sub_apply,Pi.neg_apply]
    <;> ring
  · intro t ht
    have hn := (hd t ht).ne'
    have hlin := (hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).const_mul 2)
    convert! (((hasDerivAt_const t (2:ℝ)).div hlin (hd t ht).ne').sub_const 2) using 1 <;>
      (try ext x) <;> simp only [f1,f2,Pi.div_apply,Pi.sub_apply,id_eq]
    <;> field_simp [hn] <;> ring
  · intro t ht
    have hn := (hd t ht).ne'
    have hlin := (hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).const_mul 2)
    convert! (hasDerivAt_const t (4:ℝ)).div (hlin.pow 2) (pow_ne_zero 2 (hd t ht).ne') using 1 <;>
      (try ext x) <;> simp only [f2,f3,Pi.div_apply,Pi.pow_apply,Pi.sub_apply,id_eq]
    <;> field_simp [hn] <;> ring
  · intro t ht
    dsimp [f3]
    exact div_nonneg (by norm_num) (pow_nonneg (hd t ht).le _)

theorem logdetExcess_bound_from_taylor {N : ℕ} {M B : ℚ}
    (hM : 0 < M) (hM1 : M < 1/2) (hB : 0 ≤ B)
    (hfinite : 1/(1-2*M) ≤
      Certificates.NumericalCertificateConditions.expTaylorQ N (2*M+B*M^2)) :
    logdetExcess (M : ℝ) ≤ B*(M:ℝ)^2 := by
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have hM1' : (M:ℝ) < 1/2 := by
    have h : (M:ℝ) < ((1/2:ℚ):ℝ) := by exact_mod_cast hM1
    norm_num at h ⊢
    exact h
  have hB' : (0:ℝ) ≤ B := by exact_mod_cast hB
  have hx : (0:ℝ) ≤ 2*M+B*(M:ℝ)^2 := by positivity
  have hn : (0:ℝ) < 1-2*M := by linarith
  have ht : 1/(1-2*(M:ℝ)) ≤ Certificates.expTaylor N (2*M+B*(M:ℝ)^2) := by
    have h : (((1/(1-2*M)):ℚ):ℝ) ≤
        (Certificates.NumericalCertificateConditions.expTaylorQ N (2*M+B*M^2):ℝ) := by
      exact_mod_cast hfinite
    simpa only [Certificates.cast_expTaylorQ, Rat.cast_div, Rat.cast_one, Rat.cast_sub,
      Rat.cast_mul, Rat.cast_ofNat, Rat.cast_add, Rat.cast_pow] using h
  have he := ht.trans (Certificates.expTaylor_le_exp N hx)
  have hl := Real.log_le_log (one_div_pos.mpr hn) he
  rw [Real.log_div (by norm_num) hn.ne', Real.log_one, Real.log_exp, zero_sub] at hl
  unfold logdetExcess
  linarith

def NormDeterminantCertificateConditions : Prop :=
  (1/(1-2*(223/500:ℚ)) ≤
    Certificates.NumericalCertificateConditions.expTaylorQ 8
      (2*(223/500)+(671/100)*(223/500)^2)) ∧
  (1/(1-2*(21/50:ℚ)) ≤
    Certificates.NumericalCertificateConditions.expTaylorQ 24
      (2*(21/50)+(563/100)*(21/50)^2))

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem normalized_upper_eigenvalue_nonneg {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (i : ι) : 0 ≤ normalizedUpperEigenvalue x i := by
  have ha : x i^3 ≤ normalizedUpperMean x :=
    Finset.single_le_sum (fun j _ => pow_nonneg (hx j) _) (Finset.mem_univ i)
  have hh := mul_nonneg (sq_nonneg (x i)) (sub_nonneg.mpr ha)
  have hs := mul_nonneg (hx i) (sq_nonneg (1-x i^2))
  dsimp [normalizedUpperEigenvalue]
  nlinarith

theorem normalized_upper_eigenvalue_sum {x : ι → ℝ} (h2 : ∑ i, x i^2 = 1) :
    ∑ i, normalizedUpperEigenvalue x i = (∑ i,x i)-normalizedUpperMean x := by
  simp only [normalizedUpperEigenvalue, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, h2, mul_one, normalizedUpperMean]
  ring

def normalizedLogdet (x : ι → ℝ) : ℝ :=
  (∑ i, -Real.log (1-2*normalizedUpperEigenvalue x i))-2*(∑ i,x i)

theorem normalized_logdet_bound {x : ι → ℝ} {M B : ℝ}
    (hx : ∀ i, 0 ≤ x i) (h2 : ∑ i,x i^2 = 1)
    (hM : 0 < M) (hM1 : M < 1/2) (hB : 0 ≤ B)
    (hcM : ∀ i, normalizedUpperEigenvalue x i ≤ M)
    (hcoef : logdetExcess M ≤ B*M^2) :
    normalizedLogdet x ≤ -2*normalizedUpperMean x+
      B*(1-normalizedUpperMean x^2-normalizedUpperMean x^2*(1-normalizedUpperMean x)^2) := by
  have hp (i : ι) : -Real.log (1-2*normalizedUpperEigenvalue x i) ≤
      2*normalizedUpperEigenvalue x i+B*normalizedUpperEigenvalue x i^2 := by
    have hq := logdetExcess_quadratic hM hM1
      (normalized_upper_eigenvalue_nonneg hx i) (hcM i)
    have hm := mul_le_mul_of_nonneg_left hcoef (sq_nonneg (normalizedUpperEigenvalue x i/M))
    have he : (normalizedUpperEigenvalue x i/M)^2*(B*M^2) =
        B*normalizedUpperEigenvalue x i^2 := by field_simp
    rw [he] at hm
    have hh := hq.trans hm
    dsimp [logdetExcess] at hh
    linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    normalized_upper_eigenvalue_sum h2] at hs
  have hn := mul_le_mul_of_nonneg_left (normalized_upper_frobenius_bound hx h2) hB
  dsimp [normalizedLogdet]
  linarith

theorem normalized_logdet_J0 (h : NormDeterminantCertificateConditions) {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (h2 : ∑ i,x i^2 = 1) :
    normalizedLogdet x ≤ -2*normalizedUpperMean x+
      (671/100)*(1-normalizedUpperMean x^2-normalizedUpperMean x^2*(1-normalizedUpperMean x)^2) := by
  apply normalized_logdet_bound hx h2 (M := 223/500) (by norm_num) (by norm_num) (by norm_num)
  · intro i
    exact (normalized_upper_eigenvalue_lt hx h2 i).le
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using
      logdetExcess_bound_from_taylor (by norm_num) (by norm_num) (by norm_num) h.1

theorem normalized_logdet_J1 (h : NormDeterminantCertificateConditions) {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (h2 : ∑ i,x i^2 = 1) {k : ι} (hk : (37:ℝ)/40 ≤ x k) :
    normalizedLogdet x ≤ -2*normalizedUpperMean x+
      (563/100)*(1-normalizedUpperMean x^2-normalizedUpperMean x^2*(1-normalizedUpperMean x)^2) := by
  apply normalized_logdet_bound hx h2 (M := 21/50) (by norm_num) (by norm_num) (by norm_num)
  · exact fun i => normalized_upper_eigenvalue_le_of_concentrated hx h2 hk i
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using
      logdetExcess_bound_from_taylor (by norm_num) (by norm_num) (by norm_num) h.2

end
end SingularValueBounds.KL
