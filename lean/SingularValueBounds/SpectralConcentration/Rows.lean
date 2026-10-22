import SingularValueBounds.Spectral.Basic
import SingularValueBounds.Main.SpectralBounds

/-! # Centred Gram matrices and independence of the next row -/

open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

namespace SingularValueBounds

noncomputable section

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
variable {m n : ℕ}

/-- Extend a finite family of rows by zero; only indices below `m` are used. -/
def spectralRow (X : Fin m → Ω → Fin n → ℝ) (i : ℕ) (ω : Ω) : Fin n → ℝ :=
  if hi : i < m then X ⟨i, hi⟩ ω else 0

/-- The actual centred Gram matrix `∑ⱼ<i (XⱼXⱼᵀ − I)`. -/
def centeredGram (X : Fin m → Ω → Fin n → ℝ) : ℕ → Ω → SymmetricMatrix (Fin n)
  | 0, _ => SymmetricMatrix.zero
  | i + 1, ω => SymmetricMatrix.translate
      (SymmetricMatrix.addOuter (centeredGram X i ω) (spectralRow X i ω)) (-1)

omit mΩ in
@[simp] theorem centeredGram_zero (X : Fin m → Ω → Fin n → ℝ) (ω : Ω) :
    centeredGram X 0 ω = SymmetricMatrix.zero := rfl

omit mΩ in
theorem centeredGram_eq_sum (X : Fin m → Ω → Fin n → ℝ) (i : ℕ) (ω : Ω) :
    (centeredGram X i ω).1 =
      (∑ j ∈ Finset.range i, Matrix.vecMulVec (spectralRow X j ω) (spectralRow X j ω)) -
        (i : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  induction i with
  | zero => simp [centeredGram, SymmetricMatrix.zero]
  | succ i ih =>
    simp only [centeredGram, SymmetricMatrix.translate, SymmetricMatrix.addOuter,
      ih, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one, add_smul, one_smul,
      neg_smul, one_smul]
    abel

omit mΩ in
theorem centeredGram_final (X : Fin m → Ω → Fin n → ℝ) (ω : Ω) :
    (centeredGram X m ω).1 =
      (rowMatrix X ω)ᴴ * rowMatrix X ω - (m : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [centeredGram_eq_sum, ← Fin.sum_univ_eq_sum_range, gram_eq_sum_outer]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [spectralRow, dif_pos i.isLt]
  rfl

private def spectralPast (X : Fin m → Ω → Fin n → ℝ) (i : ℕ) : MeasurableSpace Ω :=
  ⨆ j : Fin m, ⨆ (_ : j.val < i),
    (inferInstance : MeasurableSpace (Fin n → ℝ)).comap (X j)

private theorem spectralPast_le (X : Fin m → Ω → Fin n → ℝ)
    (hX : ∀ i, Measurable (X i)) (i : ℕ) : spectralPast X i ≤ mΩ :=
  iSup_le fun j => iSup_le fun _ => (hX j).comap_le

omit mΩ in
private theorem measurable_spectralRow_past (X : Fin m → Ω → Fin n → ℝ)
    {i j : ℕ} (hj : j < i) :
    @Measurable Ω (Fin n → ℝ) (spectralPast X i) _ (spectralRow X j) := by
  change @Measurable Ω (Fin n → ℝ) (spectralPast X i) _
    (fun ω => spectralRow X j ω)
  by_cases hjm : j < m
  · simp only [spectralRow, dif_pos hjm]
    apply Measurable.of_comap_le
    exact le_iSup_of_le ⟨j, hjm⟩ (le_iSup_of_le hj le_rfl)
  · simp only [spectralRow, dif_neg hjm]
    exact measurable_const

private theorem spectral_next_row_independent (X : Fin m → Ω → Fin n → ℝ)
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ) (i : Fin m) :
    Indep (spectralPast X i.val)
      ((inferInstance : MeasurableSpace (Fin n → ℝ)).comap (X i)) μ := by
  have hd : Disjoint {j : Fin m | j.val < i.val} ({i} : Set (Fin m)) := by
    apply Set.disjoint_left.mpr
    intro j hj hji
    have heq : j = i := hji
    subst j
    exact (Nat.lt_irrefl i.val) hj
  have h := indep_iSup_of_disjoint
    (m := fun j : Fin m => (inferInstance : MeasurableSpace (Fin n → ℝ)).comap (X j))
    (μ := μ) (fun j => (hX j).comap_le) hindep.iIndep hd
  simpa only [spectralPast, Set.mem_setOf_eq, iSup_singleton] using h

omit mΩ in
private theorem measurable_centeredGram_past (X : Fin m → Ω → Fin n → ℝ) (i : ℕ) :
    @Measurable Ω (SymmetricMatrix (Fin n)) (spectralPast X i) _
      (centeredGram X i) := by
  apply Measurable.subtype_mk
  change @Measurable Ω (Matrix (Fin n) (Fin n) ℝ) (spectralPast X i) _
    (fun ω => (centeredGram X i ω).1)
  simp only [centeredGram_eq_sum]
  letI := spectralPast X i
  apply Measurable.sub _ measurable_const
  apply Finset.measurable_sum
  intro j hj
  have hrow := measurable_spectralRow_past X (Finset.mem_range.mp hj)
  apply measurable_pi_lambda
  intro k
  apply measurable_pi_lambda
  intro l
  exact ((measurable_pi_apply k).comp hrow).mul ((measurable_pi_apply l).comp hrow)

/-- The accumulated Gram matrix is measurable and independent of the next row. -/
theorem centeredGram_independent (X : Fin m → Ω → Fin n → ℝ)
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ) (i : Fin m) :
    Measurable (centeredGram X i.val) ∧ IndepFun (centeredGram X i.val) (X i) μ := by
  have hmeas := measurable_centeredGram_past X i.val
  exact ⟨hmeas.mono (spectralPast_le X hX i.val) le_rfl,
    indep_of_indep_of_le_left (spectral_next_row_independent X hX hindep i) hmeas.comap_le⟩

end
end SingularValueBounds
