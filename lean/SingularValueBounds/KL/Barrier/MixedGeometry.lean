import SingularValueBounds.KL.Barrier.Initialization

/-! # Geometry of mixed regularity caps

The mixed cap uses the Euclidean spectral maximum. The continuity statement
below avoids any continuous choice of eigenvectors.
-/
open Set Filter MeasureTheory
open scoped BigOperators Matrix Topology
namespace SingularValueBounds.KL
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma spectralMaximum_lt_iff_gap {R : Matrix ι ι ℝ} (hR : R.IsHermitian) (b : ℝ) :
    spectralMaximum R hR < b ↔ (b • (1 : Matrix ι ι ℝ) - R).PosDef := by
  change (Finset.univ.sup' Finset.univ_nonempty hR.eigenvalues < b) ↔ _
  rw [Finset.sup'_lt_iff]
  exact ⟨fun h => (SymmetricMatrix.gap_posDef_iff ⟨R,hR⟩ b).mpr (fun i => h i (Finset.mem_univ i)),
    fun h i _ => (SymmetricMatrix.gap_posDef_iff ⟨R,hR⟩ b).mp h i⟩

theorem continuous_spectralMaximum :
    Continuous (fun R : SymmetricMatrix ι => spectralMaximum R.1 R.2) := by
  apply continuous_iff_continuousAt.mpr
  intro R
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨x,hx,hq⟩ := spectralMaximum_attained R.2
    have hc : Continuous (fun H : SymmetricMatrix ι => (x : ι → ℝ) ⬝ᵥ (H.1 *ᵥ (x : ι → ℝ))) := by
      dsimp [dotProduct, Matrix.mulVec]
      apply continuous_finset_sum
      intro i _
      apply continuous_const.mul
      apply continuous_finset_sum
      intro j _
      have hm : Continuous (fun H : SymmetricMatrix ι => H.1) := continuous_subtype_val
      have hij : Continuous (fun H : SymmetricMatrix ι => H.1 i j) :=
        (continuous_apply j).comp ((continuous_apply i).comp hm)
      exact hij.mul continuous_const
    have he := hc.continuousAt.eventually (Ioi_mem_nhds (show a < (x : ι → ℝ) ⬝ᵥ (R.1 *ᵥ (x : ι → ℝ)) by rw [hq]; exact ha))
    filter_upwards [he] with H hH
    have hb := euclidean_quadratic_le_spectralMaximum H.2 x
    rw [hx, one_pow, mul_one] at hb
    exact hH.trans_le hb
  · intro b hb
    have hg : (R.gap b).PosDef := (spectralMaximum_lt_iff_gap R.2 b).mp hb
    filter_upwards [eventually_gap_posDef R hg] with H hH
    exact (spectralMaximum_lt_iff_gap H.2 b).mpr hH

set_option maxHeartbeats 1000000 in
lemma continuous_spectralRatio :
    Continuous (fun R : PositiveResolvent ι => spectralRatio R.1 R.2) := by
  have hm : Continuous (fun R : PositiveResolvent ι => spectralMaximum R.1 R.2.isHermitian) :=
    Continuous.comp (f := fun R : PositiveResolvent ι =>
        (⟨R.1,R.2.isHermitian⟩ : SymmetricMatrix ι))
      (g := fun R : SymmetricMatrix ι => spectralMaximum R.1 R.2)
      (continuous_spectralMaximum (ι := ι))
      (continuous_subtype_val.subtype_mk (fun R => R.2.isHermitian))
  unfold spectralRatio
  exact hm.div (continuous_frobenius.comp continuous_subtype_val) (fun R => (frobenius_pos R.2).ne')

/-- A profile is evaluated at the actual spectral shape of the resolvent. -/
def mixedCost (a : ℝ) (h : ℝ → ℝ) (R : PositiveResolvent ι) : ℝ :=
  a * Matrix.trace R.1 + frobenius R.1 * h (spectralRatio R.1 R.2)

lemma continuous_mixedCost (a : ℝ) {h : ℝ → ℝ} (hh : Continuous h) :
    Continuous (mixedCost (ι := ι) a h) := by
  unfold mixedCost
  exact (continuous_const.mul (by fun_prop)).add
    ((continuous_frobenius.comp continuous_subtype_val).mul (hh.comp continuous_spectralRatio))

theorem spectralMaximum_conjugate_diagonal (U : Matrix.unitaryGroup ι ℝ)
    (r : ι → ℝ) {R : Matrix ι ι ℝ} (hR : R.IsHermitian)
    (heq : R = (U : Matrix ι ι ℝ) * Matrix.diagonal r * star (U : Matrix ι ι ℝ)) :
    spectralMaximum R hR = Finset.univ.sup' Finset.univ_nonempty r := by
  apply eq_of_forall_gt_iff
  intro b
  rw [spectralMaximum_lt_iff_gap, Finset.sup'_lt_iff]
  have hg : b • (1 : Matrix ι ι ℝ) - R = (U : Matrix ι ι ℝ) *
      Matrix.diagonal (fun i => b-r i) * star (U : Matrix ι ι ℝ) := by
    rw [show Matrix.diagonal (fun i => b-r i) = Matrix.diagonal (fun _ => b) - Matrix.diagonal r by
      exact (Matrix.diagonal_sub _ _).symm]
    have hb : Matrix.diagonal (fun _ : ι => b) = b • (1 : Matrix ι ι ℝ) := by
      ext i j
      by_cases hij : i=j <;> simp [Matrix.diagonal, hij]
    rw [Matrix.mul_sub, Matrix.sub_mul, hb, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, U.2.2, ← heq]
  constructor
  · intro hp
    have hd := unitary_conjugate_posDef (star U) _ hp
    have he : (star (U : Matrix ι ι ℝ)) * (b • (1 : Matrix ι ι ℝ)-R) * (U : Matrix ι ι ℝ) =
        Matrix.diagonal (fun i => b-r i) := by
      rw [hg]
      simp only [← Matrix.mul_assoc, U.2.1, Matrix.one_mul]
      rw [Matrix.mul_assoc, U.2.1, Matrix.mul_one]
    change ((star (U : Matrix ι ι ℝ)) * (b • (1 : Matrix ι ι ℝ)-R) * (U : Matrix ι ι ℝ)).PosDef at hd
    rw [he, Matrix.posDef_diagonal_iff] at hd
    intro i _
    simpa only [star_trivial, sub_pos] using hd i
  · intro hp
    rw [hg]
    exact unitary_conjugate_posDef U _ (Matrix.PosDef.diagonal (fun i => sub_pos.mpr (hp i (Finset.mem_univ i))))

theorem outward_spectralMaximum {R : Matrix ι ι ℝ} (hR : R.PosDef) {ω : ℝ}
    (hω : 0 ≤ ω) :
    spectralMaximum (outwardResolvent R ω) (outwardResolvent_posDef hR hω).isHermitian =
      Finset.univ.sup' Finset.univ_nonempty (fun i => (ω-(outwardBase R hR).2.eigenvalues i)⁻¹) := by
  apply spectralMaximum_conjugate_diagonal (outwardBase R hR).2.eigenvectorUnitary
  simpa only [SymmetricMatrix.resolvent, outwardBase_gap, outwardResolvent] using
    (outwardBase R hR).resolvent_spectral
      (((outwardBase R hR).gap_posDef_iff ω).mpr (outwardBase_above hR hω))

lemma reciprocal_shape_antitone (e : ι → ℝ) (top : ι)
    (htop : ∀ i, e i ≤ e top) {x y : ℝ} (hx : ∀ i, e i < x) (hxy : x ≤ y) :
    (y-e top)⁻¹ / Real.sqrt (∑ i, ((y-e i)⁻¹)^2) ≤
      (x-e top)⁻¹ / Real.sqrt (∑ i, ((x-e i)⁻¹)^2) := by
  have hy (i : ι) : e i < y := (hx i).trans_le hxy
  have hxp (i : ι) : 0 < (x-e i)⁻¹ := inv_pos.mpr (sub_pos.mpr (hx i))
  have hyp (i : ι) : 0 < (y-e i)⁻¹ := inv_pos.mpr (sub_pos.mpr (hy i))
  have hcomp (i : ι) : (x-e i)⁻¹ * (y-e top)⁻¹ ≤ (y-e i)⁻¹ * (x-e top)⁻¹ := by
    rw [← mul_inv, ← mul_inv]
    apply (inv_le_inv₀ (mul_pos (sub_pos.mpr (hx i)) (sub_pos.mpr (hy top)))
      (mul_pos (sub_pos.mpr (hy i)) (sub_pos.mpr (hx top)))).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr (htop i))]
  have hsum : (∑ i, ((x-e i)⁻¹)^2) * ((y-e top)⁻¹)^2 ≤
      (∑ i, ((y-e i)⁻¹)^2) * ((x-e top)⁻¹)^2 := by
    simp only [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hp := mul_nonneg (hxp i).le (hyp top).le
    have hq := mul_nonneg (hyp i).le (hxp top).le
    nlinarith [hcomp i]
  have hsx : 0 < ∑ i, ((x-e i)⁻¹)^2 :=
    Finset.sum_pos (fun i _ => sq_pos_of_pos (hxp i)) Finset.univ_nonempty
  have hsy : 0 < ∑ i, ((y-e i)⁻¹)^2 :=
    Finset.sum_pos (fun i _ => sq_pos_of_pos (hyp i)) Finset.univ_nonempty
  rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hsy) (Real.sqrt_pos.mpr hsx)]
  have hrootx := Real.sq_sqrt hsx.le
  have hrooty := Real.sq_sqrt hsy.le
  have hp := mul_nonneg (hyp top).le (Real.sqrt_nonneg (∑ i, ((x-e i)⁻¹)^2))
  have hq := mul_nonneg (hxp top).le (Real.sqrt_nonneg (∑ i, ((y-e i)⁻¹)^2))
  nlinarith

/-- A total positive-resolvent version of the outward path. -/
def outwardState (R : PositiveResolvent ι) (ω : ℝ) : PositiveResolvent ι :=
  ⟨outwardResolvent R.1 (max ω 0), outwardResolvent_posDef R.2 (le_max_right _ _)⟩

lemma outwardState_of_nonneg (R : PositiveResolvent ι) {ω : ℝ} (hω : 0 ≤ ω) :
    (outwardState R ω).1 = outwardResolvent R.1 ω := by simp [outwardState,max_eq_left hω]

theorem outward_spectralRatio_antitone (R : PositiveResolvent ι) :
    AntitoneOn (fun ω => spectralRatio (outwardState R ω).1 (outwardState R ω).2)
      (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  simp only [outwardState, max_eq_left hx, max_eq_left hy]
  let hR := R.2
  obtain ⟨top,_,htop⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    Finset.univ_nonempty (outwardBase R.1 hR).2.eigenvalues
  have ht (i : ι) : (outwardBase R.1 hR).2.eigenvalues i ≤ (outwardBase R.1 hR).2.eigenvalues top := by
    rw [← htop]
    exact Finset.le_sup' _ (Finset.mem_univ i)
  have hm (z : ℝ) (hz : 0 ≤ z) :
      spectralMaximum (outwardResolvent R.1 z) (outwardResolvent_posDef hR hz).isHermitian =
        (z-(outwardBase R.1 hR).2.eigenvalues top)⁻¹ := by
    rw [outward_spectralMaximum hR hz]
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      exact (inv_le_inv₀ (sub_pos.mpr (outwardBase_above hR hz i))
        (sub_pos.mpr (outwardBase_above hR hz top))).mpr (sub_le_sub_left (ht i) z)
    · exact Finset.le_sup' (fun i => (z-(outwardBase R.1 hR).2.eigenvalues i)⁻¹) (Finset.mem_univ top)
  unfold spectralRatio
  rw [hm x hx, hm y hy, outward_frobenius hR hx, outward_frobenius hR hy]
  exact reciprocal_shape_antitone (outwardBase R.1 hR).2.eigenvalues top ht
    (outwardBase_above hR hx) hxy

/-- The precise Cauchy--Schwarz remainder after removing a largest coordinate. -/
theorem spectral_remainder_cauchy (r : ι → ℝ) (top : ι) :
    ((∑ i, r i) - r top)^2 ≤ ((Fintype.card ι : ℝ)-1) * ((∑ i, r i^2)-r top^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ.erase top)
    (fun _ : ι => (1 : ℝ)) r
  simpa [Finset.sum_erase_eq_sub (Finset.mem_univ top),
    Finset.card_erase_of_mem (Finset.mem_univ top), Nat.cast_sub (Fintype.card_pos.le)] using h

end
end SingularValueBounds.KL
