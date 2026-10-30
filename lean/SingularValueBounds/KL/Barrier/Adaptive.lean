import SingularValueBounds.Concentration.IndependentAveraging
import SingularValueBounds.SpectralConcentration.Rows

/-! # Measurable histories and independent-row iteration
The past sigma algebra contains the entire adaptive state, not only the
Gram matrix. Fubini supplies integrability together with each MGF step. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SingularValueBounds.KL
noncomputable section
variable {Ω S β : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace β]
variable {μ : Measure Ω} {m : ℕ}

def rowPast (X : Fin m → Ω → β) (i : ℕ) : MeasurableSpace Ω :=
  ⨆ j : Fin m, ⨆ (_ : j.val < i), (inferInstance : MeasurableSpace β).comap (X j)

lemma rowPast_le (X : Fin m → Ω → β) (hX : ∀ j, Measurable (X j)) (i : ℕ) :
    rowPast X i ≤ mΩ := iSup_le fun j => iSup_le fun _ => (hX j).comap_le

lemma rowPast_mono (X : Fin m → Ω → β) {i j : ℕ} (hij : i ≤ j) :
    rowPast X i ≤ rowPast X j := by
  apply iSup_le
  intro k
  apply iSup_le
  intro hk
  exact le_iSup_of_le k (le_iSup_of_le (hk.trans_le hij) le_rfl)

lemma measurable_row_past (X : Fin m → Ω → β) (j : Fin m) {i : ℕ} (hj : j.val < i) :
    @Measurable Ω β (rowPast X i) _ (X j) :=
  Measurable.of_comap_le (le_iSup_of_le j (le_iSup_of_le hj le_rfl))

/-- Any state measurable with respect to the past is independent of the next row. -/
theorem past_state_independent (X : Fin m → Ω → β) (hX : ∀ j, Measurable (X j))
    (hind : iIndepFun X μ) (i : Fin m) (P : Ω → S)
    (hP : @Measurable Ω S (rowPast X i.val) _ P) :
    Measurable P ∧ IndepFun P (X i) μ := by
  have hd : Disjoint {j : Fin m | j.val < i.val} ({i} : Set (Fin m)) := by
    apply Set.disjoint_left.mpr
    intro j hj hji
    have heq : j = i := hji
    subst j
    exact (Nat.lt_irrefl i.val) hj
  have hi := indep_iSup_of_disjoint
    (m := fun j : Fin m => (inferInstance : MeasurableSpace β).comap (X j))
    (μ := μ) (fun j => (hX j).comap_le) hind.iIndep hd
  have hnext : Indep (rowPast X i.val) ((inferInstance : MeasurableSpace β).comap (X i)) μ := by
    simpa only [rowPast, Set.mem_setOf_eq, iSup_singleton] using hi
  exact ⟨hP.mono (rowPast_le X hX i.val) le_rfl,
    indep_of_indep_of_le_left hnext hP.comap_le⟩

/-- Generic adapted state recursion for a finite row family. -/
def adaptiveState (step : ℕ → S × β → S) (initial : S) (fallback : β)
    (X : Fin m → Ω → β) : ℕ → Ω → S
  | 0, _ => initial
  | i+1, ω => step i (adaptiveState step initial fallback X i ω,
      if hi : i < m then X ⟨i, hi⟩ ω else fallback)

lemma measurable_adaptiveState_past (step : ℕ → S × β → S)
    (hs : ∀ i, Measurable (step i)) (initial : S) (fallback : β)
    (X : Fin m → Ω → β) (i : ℕ) :
    @Measurable Ω S (rowPast X i) _ (adaptiveState step initial fallback X i) := by
  induction i with
  | zero => exact measurable_const
  | succ i ih =>
    have hp : @Measurable Ω S (rowPast X (i+1)) _ (adaptiveState step initial fallback X i) :=
      ih.mono (rowPast_mono X (Nat.le_succ i)) le_rfl
    have hx : @Measurable Ω β (rowPast X (i+1)) _
        (fun ω => if hi : i < m then X ⟨i, hi⟩ ω else fallback) := by
      by_cases hi : i < m
      · simp only [dif_pos hi]
        exact measurable_row_past X ⟨i, hi⟩ (Nat.lt_succ_self i)
      · simp only [dif_neg hi]
        exact measurable_const
    exact (hs i).comp (hp.prodMk hx)

/-- Iterating any nonnegative multiplicative weight over an adaptive history.
The state-dependent factor is averaged against the unchanged next-row law. -/
theorem adaptive_weighted_iteration [IsProbabilityMeasure μ]
    (X : Fin m → Ω → β) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (step : ℕ → S × β → S) (hs : ∀ i, Measurable (step i))
    (initial : S) (fallback : β) (w : S → ℝ) (hw : Measurable w)
    (hw0 : ∀ s, 0 ≤ w s) (hwinit : w initial = 1)
    (g : ℕ → S × β → ℝ) (hg : ∀ i, Measurable (g i))
    (hg0 : ∀ i z, 0 ≤ g i z) (C : ℝ) (hC : 0 ≤ C)
    (hstep : ∀ i s x, w (step i (s,x)) = w s * g i (s,x))
    (hgi : ∀ i : Fin m, ∀ s, Integrable (fun x => g i.val (s,x)) (μ.map (X i)))
    (hgb : ∀ i : Fin m, ∀ s, (∫ x, g i.val (s,x) ∂μ.map (X i)) ≤ C) :
    Integrable (fun ω => w (adaptiveState step initial fallback X m ω)) μ ∧
      (∫ ω, w (adaptiveState step initial fallback X m ω) ∂μ) ≤ C^m := by
  have hmain : ∀ i ≤ m,
      Integrable (fun ω => w (adaptiveState step initial fallback X i ω)) μ ∧
      (∫ ω, w (adaptiveState step initial fallback X i ω) ∂μ) ≤ C^i := by
    intro i
    induction i with
    | zero =>
      intro _
      simpa only [adaptiveState, hwinit, pow_zero, integral_const, probReal_univ,
        smul_eq_mul, one_mul] using (show Integrable (fun _ : Ω => (1 : ℝ)) μ ∧
          (∫ _ : Ω, (1 : ℝ) ∂μ) ≤ 1 from ⟨integrable_const 1, by simp⟩)
    | succ i ih =>
      intro hi
      obtain ⟨hwi, hwb⟩ := ih (by omega)
      let P := adaptiveState step initial fallback X i
      have hpast := measurable_adaptiveState_past step hs initial fallback X i
      obtain ⟨hP, hPX⟩ := past_state_independent X hX hind ⟨i, by omega⟩ P hpast
      have ha := independent_weighted_average hP (hX ⟨i, by omega⟩) hPX hw hw0 hwi
        (hg i) (hg0 i) (hgi ⟨i, by omega⟩) (hgb ⟨i, by omega⟩)
      have heq : (fun ω => w (adaptiveState step initial fallback X (i+1) ω)) =
          (fun ω => w (P ω) * g i (P ω, X ⟨i, by omega⟩ ω)) := by
        funext ω
        simp only [adaptiveState, dif_pos (show i < m by omega), hstep, P]
      rw [heq]
      have hCm : C * (∫ ω, w (P ω) ∂μ) ≤ C^(i+1) := by
        simpa only [pow_succ, mul_comm C] using mul_le_mul_of_nonneg_left hwb hC
      exact ⟨ha.1, ha.2.trans hCm⟩
  exact hmain m le_rfl

end
end SingularValueBounds.KL
