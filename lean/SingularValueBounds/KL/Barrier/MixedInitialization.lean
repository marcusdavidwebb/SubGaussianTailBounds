import SingularValueBounds.KL.Barrier.MixedCorrections

/-! # Exact scalar initialization for a mixed cap -/
open Set MeasureTheory
open scoped BigOperators Matrix
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1500000

/-- The scalar starting distance dictated by the actual profile at flat shape. -/
def mixedInitialDistance (n : ℕ) (a : ℝ) (h : ℝ → ℝ) (b : ℝ) : ℝ :=
  (a*n+Real.sqrt n*h (1/Real.sqrt n))/b

lemma mixedInitialShape_mem {n : ℕ} (hn : 0 < n) :
    1/Real.sqrt (n:ℝ) ∈ Ioc (0:ℝ) 1 := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hs := Real.sqrt_le_sqrt hn1
  norm_num at hs
  exact ⟨one_div_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)),
    (div_le_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))).mpr (by simpa using hs)⟩

lemma mixedInitialDistance_pos {n : ℕ} (hn : 0 < n) {a b : ℝ} (ha : 0 ≤ a)
    {h : ℝ → ℝ} (hh : ∀ k ∈ Ioc (0:ℝ) 1, 0 < h k) (hb : 0 < b) :
    0 < mixedInitialDistance n a h b := by
  unfold mixedInitialDistance
  apply div_pos _ hb
  exact add_pos_of_nonneg_of_pos (mul_nonneg ha (Nat.cast_nonneg _))
    (mul_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)) (hh _ (mixedInitialShape_mem hn)))

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma scalarResolvent_spectralMaximum (u : ℝ) (hu : 0 < u) :
    spectralMaximum (scalarResolvent (ι := ι) u hu).1 (scalarResolvent u hu).2.isHermitian = u⁻¹ := by
  have he := spectralMaximum_conjugate_diagonal (1 : Matrix.unitaryGroup ι ℝ)
    (fun _ : ι => u⁻¹) (scalarResolvent (ι := ι) u hu).2.isHermitian
    (show (scalarResolvent (ι := ι) u hu).1 =
      ((1 : Matrix.unitaryGroup ι ℝ) : Matrix ι ι ℝ)*Matrix.diagonal (fun _ : ι => u⁻¹)*
        star ((1 : Matrix.unitaryGroup ι ℝ) : Matrix ι ι ℝ) by simp [scalarResolvent])
  simpa using he

lemma scalarResolvent_spectralRatio (u : ℝ) (hu : 0 < u) :
    spectralRatio (scalarResolvent (ι := ι) u hu).1 (scalarResolvent u hu).2 =
      1/Real.sqrt (Fintype.card ι:ℝ) := by
  rw [spectralRatio,scalarResolvent_spectralMaximum,scalarResolvent_frobenius]
  have hs := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Fintype.card_pos (α := ι)))
  field_simp

/-- The initial scalar state meets the mixed cap exactly. -/
lemma mixed_scalar_initial_cap {a b : ℝ} (ha : 0 ≤ a)
    {h : ℝ → ℝ} (hh : ∀ k ∈ Ioc (0:ℝ) 1, 0 < h k) (hb : 0 < b) :
    mixedCost a h (scalarResolvent (ι := ι) (mixedInitialDistance (Fintype.card ι) a h b)
      (mixedInitialDistance_pos Fintype.card_pos ha hh hb)) = b := by
  rw [mixedCost,scalarResolvent_trace,scalarResolvent_frobenius,scalarResolvent_spectralRatio]
  have hp := mixedInitialDistance_pos (n := Fintype.card ι) Fintype.card_pos ha hh hb
  unfold mixedInitialDistance at hp ⊢
  have hn : 0 < a*(Fintype.card ι:ℝ)+Real.sqrt (Fintype.card ι)*h (1/Real.sqrt (Fintype.card ι)) :=
    add_pos_of_nonneg_of_pos (mul_nonneg ha (Nat.cast_nonneg _))
      (mul_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
        (hh _ (mixedInitialShape_mem Fintype.card_pos)))
  field_simp [hb.ne',hn.ne']
  ring

/-- Its initial trace is the reciprocal of the profile cap's flat-shape value. -/
lemma mixed_scalar_initial_trace {a b : ℝ} (ha : 0 ≤ a)
    {h : ℝ → ℝ} (hh : ∀ k ∈ Ioc (0:ℝ) 1, 0 < h k) (hb : 0 < b) :
    Matrix.trace (scalarResolvent (ι := ι) (mixedInitialDistance (Fintype.card ι) a h b)
      (mixedInitialDistance_pos Fintype.card_pos ha hh hb)).1 =
      b/(a+(1/Real.sqrt (Fintype.card ι))*h (1/Real.sqrt (Fintype.card ι))) := by
  rw [scalarResolvent_trace]
  have hn : 0 < (Fintype.card ι:ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hs : 0 < Real.sqrt (Fintype.card ι:ℝ) := Real.sqrt_pos.mpr hn
  have hsq : Real.sqrt (Fintype.card ι:ℝ)^2=Fintype.card ι := Real.sq_sqrt hn.le
  have hp : 0 < h (1/Real.sqrt (Fintype.card ι:ℝ)) := hh _ (mixedInitialShape_mem Fintype.card_pos)
  have hd : 0 < a+(1/Real.sqrt (Fintype.card ι:ℝ))*h (1/Real.sqrt (Fintype.card ι:ℝ)) := by positivity
  have hnum : 0 < a*(Fintype.card ι:ℝ)+Real.sqrt (Fintype.card ι)*h (1/Real.sqrt (Fintype.card ι)) := by positivity
  unfold mixedInitialDistance
  field_simp [hb.ne',hn.ne',hs.ne',hd.ne',hnum.ne']
  have heq := congrArg (fun z : ℝ => b*h (1/Real.sqrt (Fintype.card ι))*z) hsq
  nlinarith only [heq]

lemma mixed_scalar_initial_trace_lt {a b : ℝ} (ha : 0 ≤ a)
    {h : ℝ → ℝ} (hh : ∀ k ∈ Ioc (0:ℝ) 1, 0 < h k) (hb : 0 < b) :
    a*Matrix.trace (scalarResolvent (ι := ι) (mixedInitialDistance (Fintype.card ι) a h b)
      (mixedInitialDistance_pos Fintype.card_pos ha hh hb)).1 < b := by
  have he := mixed_scalar_initial_cap (ι := ι) ha hh hb
  have hp := hh _ (mixedInitialShape_mem (Fintype.card_pos (α := ι)))
  rw [mixedCost,scalarResolvent_spectralRatio] at he
  have hf := frobenius_pos (scalarResolvent (ι := ι) (mixedInitialDistance (Fintype.card ι) a h b)
    (mixedInitialDistance_pos Fintype.card_pos ha hh hb)).2
  linarith [mul_pos hf hp]

end
end SingularValueBounds.KL
