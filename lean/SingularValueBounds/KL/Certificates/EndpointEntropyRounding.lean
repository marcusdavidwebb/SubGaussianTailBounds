import SingularValueBounds.KL.Upper.EntropyGrid

/-! Uniform allowance for upward rounding in the small-range quadrature. -/
namespace SingularValueBounds.KL.Certificates
open scoped BigOperators

theorem entropyGridBoundQ_rounding_allowance (j0 : ℕ) (B A : ℕ → ℚ) (decay : ℚ)
    (_hj0 : 0 < j0) (_hjEnd : j0 ≤ 8000)
    (hBA : ∀ j ∈ Finset.Ico j0 8000, B j ≤ A j + 1 / roundingScale)
    (hK : ∀ j ∈ Finset.Ico j0 8000, 0 ≤ entropyGridKernelQ j0 j ∧
      entropyGridKernelQ j0 j ≤ 11) :
    entropyGridBoundQ j0 B decay ≤ entropyGridBoundQ j0 A decay + 440 / roundingScale := by
  have hS : (0 : ℚ) < roundingScale := by norm_num [roundingScale]
  have hterm : ∀ j ∈ Finset.Ico j0 8000,
      entropyGridKernelQ j0 j * B j / 200 ≤
        entropyGridKernelQ j0 j * A j / 200 + (11 / roundingScale) / 200 := by
    intro j hj
    have h := mul_le_mul_of_nonneg_left (hBA j hj) (hK j hj).1
    have h' := div_le_div_of_nonneg_right (hK j hj).2 hS.le
    have he : entropyGridKernelQ j0 j * (1 / roundingScale) =
        entropyGridKernelQ j0 j / roundingScale := by ring
    rw [mul_add, he] at h
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hsum
  have hn : ((8000-j0:ℕ):ℚ) ≤ 8000 := by exact_mod_cast (Nat.sub_le 8000 j0)
  have herror : ((8000-j0:ℕ):ℚ) * ((11 / roundingScale) / 200) ≤ 440 / roundingScale := by
    have h := mul_le_mul_of_nonneg_right hn (show (0:ℚ) ≤ (11 / roundingScale) / 200 by positivity)
    convert h using 1 <;> ring
  unfold entropyGridBoundQ
  linarith

end SingularValueBounds.KL.Certificates
