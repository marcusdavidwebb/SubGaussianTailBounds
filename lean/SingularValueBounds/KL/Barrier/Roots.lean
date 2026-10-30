import Mathlib.Topology.Metrizable.Basic
import SingularValueBounds.Spectral.Continuity
import SingularValueBounds.Shifts.UpperMatrixUpdate

/-! # Exact barrier roots

The exact lower and upper roots used in supplementary S1.3 and S1.6.
The lower construction applies the reciprocal-trace root to the negative
updated inverse resolvent. Joint measurability allows both matrix and target
to vary, without selecting eigenvectors continuously.
-/

open Set Filter
open scoped BigOperators Matrix Topology

namespace SingularValueBounds.KL
noncomputable section

instance positiveTargetBorelSpace : BorelSpace {c : ℝ // 0 < c} :=
  inferInstanceAs (BorelSpace (Ioi (0 : ℝ)))

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Joint continuity, including the inverse-trace target. -/
theorem continuous_resolventRoot_joint {p : ℕ} (hp : p ≠ 0) :
    Continuous (fun q : SymmetricMatrix ι × {c : ℝ // 0 < c} =>
      resolventRoot q.1.2.eigenvalues p hp q.2.1 q.2.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨H, c, hc⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let e := Finset.univ.sup' Finset.univ_nonempty H.2.eigenvalues
    have he : e < resolventRoot H.2.eigenvalues p hp c hc :=
      (Finset.sup'_lt_iff Finset.univ_nonempty).mpr
        (fun i _ => resolventRoot_above H.2.eigenvalues hp hc i)
    obtain ⟨b, hb, hbr⟩ := exists_between (max_lt ha he)
    have hab : a < b := (le_max_left _ _).trans_lt hb
    have heb : e < b := (le_max_right _ _).trans_lt hb
    have hbabove : b ∈ aboveSpectrum H.2.eigenvalues := fun i =>
      (Finset.le_sup' H.2.eigenvalues (Finset.mem_univ i)).trans_lt heb
    have hgap := (H.gap_posDef_iff b).mpr hbabove
    have htrace : c < Matrix.trace (H.resolvent b ^ p) := by
      rw [H.resolvent_powerTrace hgap p, ← resolventRoot_eq H.2.eigenvalues hp hc]
      exact reciprocalTrace_strictAnti H.2.eigenvalues hp hbabove
        (resolventRoot_above H.2.eigenvalues hp hc) hbr
    have hct : ContinuousAt (fun q : SymmetricMatrix ι × {c : ℝ // 0 < c} =>
        Matrix.trace (q.1.resolvent b ^ p) - q.2.1) (H, ⟨c, hc⟩) :=
      by
        have hfst : ContinuousAt (fun q : SymmetricMatrix ι × {c : ℝ // 0 < c} => q.1)
            (H, ⟨c, hc⟩) := continuous_fst.continuousAt
        have htr := (continuousAt_resolvent_powerTrace H hgap p).comp hfst
        exact htr.sub (continuous_subtype_val.comp continuous_snd).continuousAt
    have hev := hct.eventually (Ioi_mem_nhds (sub_pos.mpr htrace))
    have hevg : ∀ᶠ q : SymmetricMatrix ι × {c : ℝ // 0 < c} in 𝓝 (H, ⟨c, hc⟩),
        (q.1.gap b).PosDef := by
      have hfst : ContinuousAt (fun q : SymmetricMatrix ι × {c : ℝ // 0 < c} => q.1)
          (H, ⟨c, hc⟩) := continuous_fst.continuousAt
      exact hfst.eventually (eventually_gap_posDef H hgap)
    filter_upwards [hev, hevg] with q hq hgapq
    have hbrq : b < resolventRoot q.1.2.eigenvalues p hp q.2.1 q.2.2 := by
      apply lt_of_not_ge
      intro hle
      have ht := ((resolventRoot_le_iff q.1.2.eigenvalues hp q.2.2).mp hle).2
      rw [← q.1.resolvent_powerTrace hgapq p] at ht
      linarith
    exact hab.trans hbrq
  · intro a ha
    obtain ⟨b, hbr, hba⟩ := exists_between ha
    have hbabove : b ∈ aboveSpectrum H.2.eigenvalues := fun i =>
      (resolventRoot_above H.2.eigenvalues hp hc i).trans hbr
    have hgap := (H.gap_posDef_iff b).mpr hbabove
    have htrace : Matrix.trace (H.resolvent b ^ p) < c := by
      rw [H.resolvent_powerTrace hgap p, ← resolventRoot_eq H.2.eigenvalues hp hc]
      exact reciprocalTrace_strictAnti H.2.eigenvalues hp
        (resolventRoot_above H.2.eigenvalues hp hc) hbabove hbr
    have hct : ContinuousAt (fun q : SymmetricMatrix ι × {c : ℝ // 0 < c} =>
        Matrix.trace (q.1.resolvent b ^ p) - q.2.1) (H, ⟨c, hc⟩) :=
      by
        have hfst : ContinuousAt (fun q : SymmetricMatrix ι × {c : ℝ // 0 < c} => q.1)
            (H, ⟨c, hc⟩) := continuous_fst.continuousAt
        have htr := (continuousAt_resolvent_powerTrace H hgap p).comp hfst
        exact htr.sub (continuous_subtype_val.comp continuous_snd).continuousAt
    have hev := hct.eventually (Iio_mem_nhds (sub_neg.mpr htrace))
    have hevg : ∀ᶠ q : SymmetricMatrix ι × {c : ℝ // 0 < c} in 𝓝 (H, ⟨c, hc⟩),
        (q.1.gap b).PosDef := by
      have hfst : ContinuousAt (fun q : SymmetricMatrix ι × {c : ℝ // 0 < c} => q.1)
          (H, ⟨c, hc⟩) := continuous_fst.continuousAt
      exact hfst.eventually (eventually_gap_posDef H hgap)
    filter_upwards [hev, hevg] with q hq hgapq
    have hroot : resolventRoot q.1.2.eigenvalues p hp q.2.1 q.2.2 ≤ b := by
      apply (resolventRoot_le_iff q.1.2.eigenvalues hp q.2.2).mpr
      refine ⟨(q.1.gap_posDef_iff b).mp hgapq, ?_⟩
      rw [← q.1.resolvent_powerTrace hgapq p]
      linarith
    exact hroot.trans_lt hba

/-- A positive definite real matrix has positive trace. -/
theorem trace_pos {R : Matrix ι ι ℝ} (hR : R.PosDef) : 0 < Matrix.trace R := by
  rw [real_spectral_trace hR.isHermitian]
  exact Finset.sum_pos (fun i _ => hR.eigenvalues_pos i) Finset.univ_nonempty

/-- Sherman--Morrison with the original resolvent as base. -/
theorem rankOne_inverse {R : Matrix ι ι ℝ} (hR : R.PosDef) (x : ι → ℝ) :
    (R⁻¹ + Matrix.vecMulVec x x)⁻¹ =
      R - (1 + x ⬝ᵥ (R *ᵥ x))⁻¹ • Matrix.vecMulVec (R *ᵥ x) (R *ᵥ x) := by
  have hunit := (Matrix.isUnit_iff_isUnit_det _).mp hR.isUnit
  have hq : 0 ≤ x ⬝ᵥ (R *ᵥ x) := by simpa using hR.posSemidef.dotProduct_mulVec_nonneg x
  have hd : 1 + x ⬝ᵥ (R *ᵥ x) ≠ 0 := by positivity
  have hs : x ᵥ* R = R *ᵥ x := by
    have ht : R.transpose = R := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
    rw [← Matrix.mulVec_transpose, ht]
  have hy : R⁻¹ *ᵥ (R *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.nonsing_inv_mul _ hunit, mul_outer, hy, outer_mul, hs, outer_mul_outer]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    dotProduct] at *
  field_simp [hd]
  ring

/-- The trace drop is the positive rank-one quadratic ratio. -/
theorem rankOne_trace {R : Matrix ι ι ℝ} (hR : R.PosDef) (x : ι → ℝ) :
    Matrix.trace (R⁻¹ + Matrix.vecMulVec x x)⁻¹ =
      Matrix.trace R - (x ⬝ᵥ ((R ^ 2) *ᵥ x)) / (1 + x ⬝ᵥ (R *ᵥ x)) := by
  rw [rankOne_inverse hR, Matrix.trace_sub, Matrix.trace_smul]
  have hs : x ᵥ* R = R *ᵥ x := by
    have ht : R.transpose = R := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
    rw [← Matrix.mulVec_transpose, ht]
  have hquad : x ⬝ᵥ ((R ^ 2) *ᵥ x) = Matrix.trace (Matrix.vecMulVec (R *ᵥ x) (R *ᵥ x)) := by
    rw [pow_two, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hs]
    rfl
  rw [hquad]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

/-- The negative updated inverse matrix, for the scalar resolvent root. -/
def lowerRootMatrix (R : Matrix ι ι ℝ) (hR : R.PosDef) (x : ι → ℝ) : SymmetricMatrix ι :=
  ⟨-(R⁻¹ + Matrix.vecMulVec x x),
    (hR.inv.isHermitian.add (outer_posSemidef x).isHermitian).neg⟩

/-- The exact lower advance. -/
def lowerShift (R : Matrix ι ι ℝ) (hR : R.PosDef) (x : ι → ℝ) : ℝ :=
  -resolventRoot (lowerRootMatrix R hR x).2.eigenvalues 1 (by decide)
    (Matrix.trace R) (trace_pos hR)

theorem lowerShift_preserves {R : Matrix ι ι ℝ} (hR : R.PosDef) (x : ι → ℝ) :
    let G := R⁻¹ + Matrix.vecMulVec x x - lowerShift R hR x • (1 : Matrix ι ι ℝ)
    G.PosDef ∧ Matrix.trace G⁻¹ = Matrix.trace R := by
  let H := lowerRootMatrix R hR x
  let u := resolventRoot H.2.eigenvalues 1 (by decide) (Matrix.trace R) (trace_pos hR)
  have hg := (H.gap_posDef_iff u).mpr (resolventRoot_above _ (by decide) (trace_pos hR))
  have heq := resolventRoot_eq H.2.eigenvalues (by decide : 1 ≠ 0) (trace_pos hR)
  have hid : H.gap u = R⁻¹ + Matrix.vecMulVec x x - lowerShift R hR x • (1 : Matrix ι ι ℝ) := by
    dsimp [H, SymmetricMatrix.gap, lowerRootMatrix, lowerShift, u]
    simp only [neg_smul, sub_neg_eq_add, sub_neg_eq_add]
    abel
  refine ⟨hid ▸ hg, ?_⟩
  rw [← hid]
  change Matrix.trace (H.resolvent u) = _
  rw [← pow_one (H.resolvent u), H.resolvent_powerTrace hg 1]
  exact heq

theorem lowerShift_nonneg {R : Matrix ι ι ℝ} (hR : R.PosDef) (x : ι → ℝ) :
    0 ≤ lowerShift R hR x := by
  let H := lowerRootMatrix R hR x
  have hg : (H.gap 0).PosDef := by
    simpa [H, lowerRootMatrix, SymmetricMatrix.gap] using hR.inv.add_posSemidef (outer_posSemidef x)
  have hq : 0 ≤ x ⬝ᵥ ((R ^ 2) *ᵥ x) := by
    rw [real_spectral_square hR.isHermitian, quadratic_conjugate_diagonal]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hden : 0 < 1 + x ⬝ᵥ (R *ᵥ x) := by
    have : 0 ≤ x ⬝ᵥ (R *ᵥ x) := by simpa using hR.posSemidef.dotProduct_mulVec_nonneg x
    linarith
  have ht : Matrix.trace (H.resolvent 0) ≤ Matrix.trace R := by
    change Matrix.trace (H.gap 0)⁻¹ ≤ _
    simp only [H, lowerRootMatrix, SymmetricMatrix.gap, zero_smul, zero_sub, neg_neg]
    rw [rankOne_trace hR]
    exact sub_le_self _ (div_nonneg hq hden.le)
  have hu := (resolventRoot_le_iff H.2.eigenvalues (by decide : 1 ≠ 0) (trace_pos hR)).mpr
    ⟨(H.gap_posDef_iff 0).mp hg, by rw [← H.resolvent_powerTrace hg 1]; simpa using ht⟩
  exact neg_nonneg.mpr hu

theorem lowerShift_unique_preserves {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (x : ι → ℝ) {δ : ℝ}
    (hg : (R⁻¹ + Matrix.vecMulVec x x - δ • (1 : Matrix ι ι ℝ)).PosDef)
    (ht : Matrix.trace (R⁻¹ + Matrix.vecMulVec x x - δ • (1 : Matrix ι ι ℝ))⁻¹ =
      Matrix.trace R) : δ = lowerShift R hR x := by
  let H := lowerRootMatrix R hR x
  have hid : H.gap (-δ) = R⁻¹ + Matrix.vecMulVec x x - δ • (1 : Matrix ι ι ℝ) := by
    dsimp [H, lowerRootMatrix, SymmetricMatrix.gap]
    simp only [neg_smul, sub_neg_eq_add]
    abel
  have hg' : (H.gap (-δ)).PosDef := hid ▸ hg
  have heq : reciprocalTrace H.2.eigenvalues 1 (-δ) = Matrix.trace R := by
    rw [← H.resolvent_powerTrace hg' 1, pow_one]
    change Matrix.trace (H.gap (-δ))⁻¹ = _
    rw [hid]
    exact ht
  have hu := resolventRoot_unique H.2.eigenvalues (by decide : 1 ≠ 0) (trace_pos hR)
    ((H.gap_posDef_iff (-δ)).mp hg') heq
  exact (neg_inj.mp (by simpa [lowerShift, H] using hu))

theorem lowerShift_zero {R : Matrix ι ι ℝ} (hR : R.PosDef) : lowerShift R hR 0 = 0 := by
  have ho : Matrix.vecMulVec (0 : ι → ℝ) (0 : ι → ℝ) = 0 := by ext i j; simp [Matrix.vecMulVec]
  symm
  apply lowerShift_unique_preserves hR 0
  · simpa only [ho, add_zero, zero_smul, sub_zero] using hR.inv
  · simp only [ho, add_zero, zero_smul, sub_zero]
    rw [Matrix.nonsing_inv_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det _).mp hR.isUnit)]

theorem lowerShift_pos {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {x : ι → ℝ} (hx : x ≠ 0) : 0 < lowerShift R hR x := by
  have hn : 0 < x ⬝ᵥ ((R ^ 2) *ᵥ x) := by
    rw [real_spectral_square hR.isHermitian, quadratic_conjugate_diagonal]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (upper_coordinates_ne_zero hR hx)
    exact lt_of_lt_of_le (mul_pos (sq_pos_of_ne_zero hi)
      (sq_pos_of_pos (hR.eigenvalues_pos i)))
      (Finset.single_le_sum (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (Finset.mem_univ i))
  have hd : 0 < 1 + x ⬝ᵥ (R *ᵥ x) := by
    have : 0 ≤ x ⬝ᵥ (R *ᵥ x) := by simpa using hR.posSemidef.dotProduct_mulVec_nonneg x
    linarith
  apply lt_of_le_of_ne (lowerShift_nonneg hR x)
  intro hz
  have ht := (lowerShift_preserves hR x).2
  rw [← hz, zero_smul, sub_zero, rankOne_trace hR] at ht
  linarith [div_pos hn hd]

theorem lowerShift_pos_iff {R : Matrix ι ι ℝ} (hR : R.PosDef) (x : ι → ℝ) :
    0 < lowerShift R hR x ↔ x ≠ 0 := by
  refine ⟨?_, lowerShift_pos hR⟩
  intro h hz
  subst x
  rw [lowerShift_zero] at h
  exact lt_irrefl _ h

/-- Joint measurability of the exact lower root in its positive resolvent and row. -/
theorem measurable_lowerShift :
    Measurable (fun q : {R : Matrix ι ι ℝ // R.PosDef} × (ι → ℝ) =>
      lowerShift q.1.1 q.1.2 q.2) := by
  have hm : Measurable (fun q : {R : Matrix ι ι ℝ // R.PosDef} × (ι → ℝ) => q.1.1) :=
    measurable_subtype_coe.comp measurable_fst
  have ho : Measurable (fun q : {R : Matrix ι ι ℝ // R.PosDef} × (ι → ℝ) =>
      Matrix.vecMulVec q.2 q.2) := by
    have hc : Continuous (fun x : ι → ℝ => Matrix.vecMulVec x x) := by fun_prop
    exact hc.measurable.comp measurable_snd
  have hmat : Measurable (fun q : {R : Matrix ι ι ℝ // R.PosDef} × (ι → ℝ) =>
      lowerRootMatrix q.1.1 q.1.2 q.2) :=
    (((measurable_matrix_inverse.comp hm).add ho).neg).subtype_mk
  have ht : Measurable (fun q : {R : Matrix ι ι ℝ // R.PosDef} × (ι → ℝ) =>
      (⟨Matrix.trace q.1.1, trace_pos q.1.2⟩ : {c : ℝ // 0 < c})) :=
    (((continuous_id : Continuous (fun R : Matrix ι ι ℝ => R)).matrix_trace.measurable).comp hm).subtype_mk
  exact ((continuous_resolventRoot_joint (ι := ι) (by decide : 1 ≠ 0)).measurable.comp
    (hmat.prodMk ht)).neg

end
end SingularValueBounds.KL
