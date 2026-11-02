import SingularValueBounds.Spectral.Construction

/-! # Continuity of the variational spectral bounds

Positive definiteness is open on the space of symmetric matrices. Strict
brackets around each resolvent root then prove continuity without requiring
a continuous choice of eigenvectors.
-/

open Set Filter
open scoped BigOperators Matrix Topology

namespace SingularValueBounds

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
theorem symmetric_posDef_iff_sphere (H : SymmetricMatrix ι) :
    H.1.PosDef ↔ ∀ x : ι → ℝ, ‖x‖ = 1 → 0 < x ⬝ᵥ H.1 *ᵥ x := by
  constructor
  · intro hH x hx
    have hn : x ≠ 0 := by intro hz; simp [hz] at hx
    simpa using hH.dotProduct_mulVec_pos hn
  · intro hsphere
    apply Matrix.posDef_iff_dotProduct_mulVec.mpr
    refine ⟨H.2, ?_⟩
    intro x hx
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let y := ‖x‖⁻¹ • x
    have hy : ‖y‖ = 1 := by simp [y, norm_smul, hn.ne']
    have hq := hsphere y hy
    have hid : y ⬝ᵥ H.1 *ᵥ y = (‖x‖⁻¹) ^ 2 * (x ⬝ᵥ H.1 *ᵥ x) := by
      simp only [y, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
      ring
    rw [hid] at hq
    simpa using (mul_pos_iff_of_pos_left (pow_pos (inv_pos.mpr hn) 2)).mp hq

omit [DecidableEq ι] [Nonempty ι] in
theorem isOpen_symmetric_posDef : IsOpen {H : SymmetricMatrix ι | H.1.PosDef} := by
  let S := Metric.sphere (0 : ι → ℝ) 1
  have hs : IsCompact S := isCompact_sphere _ _
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hs
  let bad : Set (SymmetricMatrix ι × S) :=
    {p | (p.2.1 : ι → ℝ) ⬝ᵥ p.1.1 *ᵥ p.2.1 ≤ 0}
  have hx : ∀ i, Continuous (fun p : SymmetricMatrix ι × S => p.2.1 i) := fun i =>
    (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
  have hm : ∀ i j, Continuous (fun p : SymmetricMatrix ι × S => p.1.1 i j) := fun i j =>
    (show Continuous (fun M : Matrix ι ι ℝ => M i j) by fun_prop).comp
      (continuous_subtype_val.comp continuous_fst)
  have hbad : IsClosed bad := by
    apply isClosed_le _ continuous_const
    dsimp [Matrix.mulVec, dotProduct]
    apply continuous_finset_sum
    intro i _
    apply Continuous.mul
    · exact hx i
    · apply continuous_finset_sum
      intro j _
      exact (hm i j).mul (hx j)
  have himage := isClosedMap_fst_of_compactSpace bad hbad
  have heq : {H : SymmetricMatrix ι | H.1.PosDef} = (Prod.fst '' bad)ᶜ := by
    ext H
    rw [mem_setOf_eq, symmetric_posDef_iff_sphere]
    simp only [mem_compl_iff, mem_image, Prod.exists, exists_and_right, exists_eq_right]
    constructor
    · intro h ⟨x, hx⟩
      have hn : ‖x.1‖ = 1 := by simpa [S, Metric.mem_sphere, dist_zero_right] using x.2
      exact (not_le_of_gt (h x.1 hn)) hx
    · intro h x hx
      have hxS : x ∈ S := by simp [S, hx]
      exact lt_of_not_ge (fun hle => h ⟨⟨x, hxS⟩, hle⟩)
  rw [heq]
  exact himage.isOpen_compl

omit [Nonempty ι] in
theorem continuousAt_resolvent (H : SymmetricMatrix ι) {u : ℝ}
    (hu : (H.gap u).PosDef) :
    ContinuousAt (fun G : SymmetricMatrix ι => G.resolvent u) H := by
  have hinv : ContinuousAt Inv.inv (H.gap u) := by
    apply continuousAt_matrix_inv
    have heq : (Ring.inverse : ℝ → ℝ) = Inv.inv := funext Ring.inverse_eq_inv
    rw [heq]
    exact continuousAt_inv₀ hu.det_pos.ne'
  change ContinuousAt (fun G : SymmetricMatrix ι => (G.gap u)⁻¹) H
  exact hinv.comp (f := fun G : SymmetricMatrix ι => G.gap u)
    (show ContinuousAt (fun G : SymmetricMatrix ι => G.gap u) H from
    (continuous_const.sub continuous_subtype_val).continuousAt)

omit [Nonempty ι] in
theorem eventually_gap_posDef (H : SymmetricMatrix ι) {u : ℝ}
    (hu : (H.gap u).PosDef) :
    ∀ᶠ G : SymmetricMatrix ι in 𝓝 H, (G.gap u).PosDef := by
  let f : SymmetricMatrix ι → SymmetricMatrix ι := fun G =>
    ⟨G.gap u, (by exact (by simp [Matrix.IsHermitian] :
      (u • (1 : Matrix ι ι ℝ)).IsHermitian).sub G.2)⟩
  have hf : Continuous f := (continuous_const.sub continuous_subtype_val).subtype_mk _
  exact hf.continuousAt (isOpen_symmetric_posDef.mem_nhds hu)

omit [Nonempty ι] in
theorem continuousAt_resolvent_powerTrace (H : SymmetricMatrix ι) {u : ℝ}
    (hu : (H.gap u).PosDef) (p : ℕ) :
    ContinuousAt (fun G : SymmetricMatrix ι => Matrix.trace (G.resolvent u ^ p)) H :=
  (show Continuous (fun R : Matrix ι ι ℝ => Matrix.trace (R ^ p)) by fun_prop).continuousAt.comp
    (continuousAt_resolvent H hu)

/-- Continuity of either resolvent root follows by keeping two strict
level brackets valid under a small change of the matrix. -/
theorem continuous_resolventRoot {p : ℕ} (hp : p ≠ 0) {c : ℝ} (hc : 0 < c) :
    Continuous (fun H : SymmetricMatrix ι => resolventRoot H.2.eigenvalues p hp c hc) := by
  apply continuous_iff_continuousAt.mpr
  intro H
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let e := Finset.univ.sup' Finset.univ_nonempty H.2.eigenvalues
    have he : e < resolventRoot H.2.eigenvalues p hp c hc := by
      exact (Finset.sup'_lt_iff Finset.univ_nonempty).mpr
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
    have hevent := (continuousAt_resolvent_powerTrace H hgap p).eventually
      (Ioi_mem_nhds htrace)
    filter_upwards [hevent, eventually_gap_posDef H hgap] with G hG hgapG
    have hbrG : b < resolventRoot G.2.eigenvalues p hp c hc := by
      apply lt_of_not_ge
      intro hle
      have ht := ((resolventRoot_le_iff G.2.eigenvalues hp hc).mp hle).2
      rw [← G.resolvent_powerTrace hgapG p] at ht
      exact (not_lt_of_ge ht) hG
    exact hab.trans hbrG
  · intro a ha
    obtain ⟨b, hbr, hba⟩ := exists_between ha
    have hbabove : b ∈ aboveSpectrum H.2.eigenvalues := fun i =>
      (resolventRoot_above H.2.eigenvalues hp hc i).trans hbr
    have hgap := (H.gap_posDef_iff b).mpr hbabove
    have htrace : Matrix.trace (H.resolvent b ^ p) < c := by
      rw [H.resolvent_powerTrace hgap p, ← resolventRoot_eq H.2.eigenvalues hp hc]
      exact reciprocalTrace_strictAnti H.2.eigenvalues hp
        (resolventRoot_above H.2.eigenvalues hp hc) hbabove hbr
    have hevent := (continuousAt_resolvent_powerTrace H hgap p).eventually
      (Iio_mem_nhds htrace)
    filter_upwards [hevent, eventually_gap_posDef H hgap] with G hG hgapG
    have hroot : resolventRoot G.2.eigenvalues p hp c hc ≤ b := by
      apply (resolventRoot_le_iff G.2.eigenvalues hp hc).mpr
      refine ⟨(G.gap_posDef_iff b).mp hgapG, ?_⟩
      rw [← G.resolvent_powerTrace hgapG p]
      exact hG.le
    exact hroot.trans_lt hba

theorem continuous_spectralBarrier {φ η : ℝ} (hφ : 0 < φ) (hη : 0 < η) :
    Continuous (spectralBarrier (ι := ι) φ η hφ hη) :=
  (continuous_resolventRoot (by decide) hφ).max
    (continuous_resolventRoot (by decide) (sq_pos_of_pos hη))

theorem continuous_spectralResolvent {φ η : ℝ} (hφ : 0 < φ) (hη : 0 < η) :
    Continuous (fun H : SymmetricMatrix ι => H.resolvent (spectralBarrier φ η hφ hη H)) := by
  apply continuous_iff_continuousAt.mpr
  intro H
  have hg : Continuous (fun G : SymmetricMatrix ι => G.gap (spectralBarrier φ η hφ hη G)) :=
    ((continuous_spectralBarrier hφ hη).smul continuous_const).sub continuous_subtype_val
  have hinv : ContinuousAt Inv.inv (H.gap (spectralBarrier φ η hφ hη H)) := by
    apply continuousAt_matrix_inv
    have heq : (Ring.inverse : ℝ → ℝ) = Inv.inv := funext Ring.inverse_eq_inv
    rw [heq]
    exact continuousAt_inv₀ (spectralBarrier_gap φ η hφ hη H).det_pos.ne'
  exact hinv.comp (f := fun G : SymmetricMatrix ι => G.gap (spectralBarrier φ η hφ hη G))
    hg.continuousAt

theorem continuous_spectralUpper {φ η : ℝ} (hφ : 0 < φ) (hη : 0 < η) :
    Continuous (spectralUpper (ι := ι) φ η hφ hη) :=
  (continuous_spectralBarrier hφ hη).add
    ((continuous_spectralResolvent hφ hη).matrix_trace.div_const _)

theorem continuous_spectralLower {φ η : ℝ} (hφ : 0 < φ) (hη : 0 < η) :
    Continuous (spectralLower (ι := ι) φ η hφ hη) := by
  have hn : Continuous (SymmetricMatrix.neg (ι := ι)) := continuous_subtype_val.neg.subtype_mk _
  exact ((continuous_spectralUpper hφ hη).comp hn).neg

end
end SingularValueBounds
