import MainTheoremStatement
import SingularValueBounds.Canonical.NLARows
import SingularValueBounds.Canonical.NLASingularValues
import SingularValueBounds.KL.Statement
import SingularValueBounds.Spectral.Continuity

/-!
Row, matrix and measurability bridges used by the canonical proof and by its
statement-equivalence check. These lemmas assert no numerical tail bound.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal

namespace SubGaussian

-- Historical spellings used only by the proof adapter. The canonical statement
-- refers directly to NLA-lib's singular values.
noncomputable abbrev smallestSingularValue := @Previous.smallestSingularValue
noncomputable abbrev largestSingularValue := @Previous.largestSingularValue

end SubGaussian

namespace SingularValueBounds.Canonical
noncomputable section
universe u

local instance rectangularMatrixMeasurableSpace {m n : ℕ} :
    MeasurableSpace (Matrix (Fin m) (Fin n) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin m → Fin n → ℝ))

local instance rectangularMatrixBorelSpace {m n : ℕ} :
    BorelSpace (Matrix (Fin m) (Fin n) ℝ) :=
  inferInstanceAs (BorelSpace (Fin m → Fin n → ℝ))

theorem smallestSingularValue_eq {m n : ℕ} (hn : 1 ≤ n) [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    SubGaussian.smallestSingularValue hn A = SingularValueBounds.smallestSingularValue A := by
  change (Finset.univ.image (SingularValueBounds.singularValues A)).min' _ =
    Finset.univ.inf' _ (SingularValueBounds.singularValues A)
  erw [Finset.min'_eq_inf', Finset.inf'_image]
  rfl

theorem largestSingularValue_eq {m n : ℕ} (hn : 1 ≤ n) [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    SubGaussian.largestSingularValue hn A = SingularValueBounds.largestSingularValue A := by
  change (Finset.univ.image (SingularValueBounds.singularValues A)).max' _ =
    Finset.univ.sup' _ (SingularValueBounds.singularValues A)
  erw [Finset.max'_eq_sup', Finset.sup'_image]
  rfl

theorem logParameter_eq {K : ℝ} (hK : 1 ≤ K) :
    Real.log (Real.exp 1 * K) = logParameter K := by
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (lt_of_lt_of_le zero_lt_one hK)),
    Real.log_exp]
  rfl

theorem euclidean_norm_sq (n : ℕ) (v : Fin n → ℝ) :
    ‖((WithLp.equiv 2 (Fin n → ℝ)).symm v : EuclideanSpace ℝ (Fin n))‖ ^ 2 = v ⬝ᵥ v := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ j, (v j) ^ 2) = ∑ j, v j * v j
  simp only [pow_two]

theorem centredIsotropic_of_coordinates {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ}
    (hm : Measurable X)
    (hc : ∀ j, Integrable (fun ω => X ω j) μ ∧ (∫ ω, X ω j ∂μ) = 0)
    (hi : ∀ j k, Integrable (fun ω => X ω j * X ω k) μ ∧
      (∫ ω, X ω j * X ω k ∂μ) = if j = k then 1 else 0) :
    CentredIsotropic μ X := by
  have hint (v : Fin n → ℝ) : Integrable (fun ω => v ⬝ᵥ X ω) μ :=
    integrable_finset_sum _ (fun j _ => (hc j).1.const_mul (v j))
  have hsquare (v : Fin n → ℝ) (ω : Ω) :
      (v ⬝ᵥ X ω) ^ 2 = ∑ j, ∑ k, (v j * v k) * (X ω j * X ω k) := by
    simp only [dotProduct, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hint2 (v : Fin n → ℝ) :
      ∀ j, Integrable (fun ω => ∑ k, (v j * v k) * (X ω j * X ω k)) μ := by
    intro j
    exact integrable_finset_sum _ (fun k _ => (hi j k).1.const_mul (v j * v k))
  refine ⟨hm, hint, ?_, ?_, ?_⟩
  · intro v
    rw [show (fun ω => v ⬝ᵥ X ω) = (fun ω => ∑ j, v j * X ω j) from rfl]
    rw [integral_finset_sum _ (fun j _ => (hc j).1.const_mul (v j))]
    simp only [integral_const_mul, (hc _).2, mul_zero, Finset.sum_const_zero]
  · intro v
    simp_rw [hsquare]
    exact integrable_finset_sum _ (fun j _ => hint2 v j)
  · intro v
    simp_rw [hsquare]
    rw [integral_finset_sum _ (fun j _ => hint2 v j)]
    simp_rw [integral_finset_sum _ (fun k _ => (hi _ k).1.const_mul (v _ * v k)),
      integral_const_mul]
    simp [fun j k => (hi j k).2, dotProduct]

theorem subGaussianMGF_of_directions {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ} {K : ℝ}
    (h : ∀ (v : EuclideanSpace ℝ (Fin n)) (θ : ℝ),
      Integrable (fun ω => Real.exp (θ * (∑ j, X ω j * v j))) μ ∧
      (∫ ω, Real.exp (θ * (∑ j, X ω j * v j)) ∂μ) ≤
        Real.exp (K ^ 2 * θ ^ 2 * ‖v‖ ^ 2 / 2)) : SubGaussianMGF μ X K := by
  have hid (v : Fin n → ℝ) (ω : Ω) :
      (∑ j, X ω j * ((WithLp.equiv 2 (Fin n → ℝ)).symm v : EuclideanSpace ℝ (Fin n)) j) = v ⬝ᵥ X ω := by
    simp [dotProduct, mul_comm]
  constructor
  · intro v θ
    simpa only [hid] using (h ((WithLp.equiv 2 (Fin n → ℝ)).symm v) θ).1
  · intro v θ
    simpa only [hid, euclidean_norm_sq, mul_comm (K ^ 2) (θ ^ 2)] using
      (h ((WithLp.equiv 2 (Fin n → ℝ)).symm v) θ).2

theorem lower_gap_posDef_iff {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.IsHermitian) (a : ℝ) :
    (H - a • 1).PosDef ↔ ∀ j, a < hH.eigenvalues j := by
  constructor
  · intro h j
    have hg : ((-a) • (1 : Matrix (Fin n) (Fin n) ℝ) - (-1 : ℝ) • H).PosDef := by
      convert h using 1; module
    have hv := eigenvalue_gap_pos hH hg j
    linarith
  · intro h
    have hd : Matrix.diagonal (fun j => hH.eigenvalues j - a) =
        Matrix.diagonal hH.eigenvalues - a • (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
    have he : H - a • 1 = (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
        Matrix.diagonal (fun j => hH.eigenvalues j - a) *
        star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := by
      rw [hd, Matrix.mul_sub, Matrix.sub_mul, unitary_conjugate_scalar,
        ← real_spectral_decomposition hH]
    rw [he]
    exact unitary_conjugate_posDef _ _ (Matrix.PosDef.diagonal (fun j => sub_pos.mpr (h j)))

theorem measurable_smallestSingularValue {m n : ℕ} (hn : 1 ≤ n) :
    Measurable (SubGaussian.smallestSingularValue (m := m) hn) := by
  letI : NeZero n := ⟨by omega⟩
  apply measurable_of_Ioi
  intro a
  by_cases ha : a < 0
  · have he : (SubGaussian.smallestSingularValue (m := m) hn) ⁻¹' Set.Ioi a = Set.univ := by
      ext A
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
      rw [smallestSingularValue_eq]
      exact ha.trans_le (smallestSingularValue_nonneg A)
    rw [he]
    exact MeasurableSet.univ
  · have ha0 : 0 ≤ a := le_of_not_gt ha
    let f : Matrix (Fin m) (Fin n) ℝ → SymmetricMatrix (Fin n) := fun A =>
      ⟨Aᴴ * A - a ^ 2 • 1,
        (Matrix.isHermitian_conjTranspose_mul_self A).sub (by simp [Matrix.IsHermitian])⟩
    have hf : Continuous f := by
      apply Continuous.subtype_mk
      fun_prop
    have he : (SubGaussian.smallestSingularValue (m := m) hn) ⁻¹' Set.Ioi a =
        f ⁻¹' {H | H.1.PosDef} := by
      ext A
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq, f,
        smallestSingularValue_eq, SingularValueBounds.smallestSingularValue,
        Finset.lt_inf'_iff, singularValues, Finset.mem_univ,
        forall_true_left]
      exact (forall_congr' (fun j : Fin n => Real.lt_sqrt (y :=
        (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues j) ha0)).trans
          (lower_gap_posDef_iff _ (Matrix.isHermitian_conjTranspose_mul_self A) (a ^ 2)).symm
    rw [he]
    exact (isOpen_symmetric_posDef.preimage hf).measurableSet

theorem measurable_largestSingularValue {m n : ℕ} (hn : 1 ≤ n) :
    Measurable (SubGaussian.largestSingularValue (m := m) hn) := by
  letI : NeZero n := ⟨by omega⟩
  apply measurable_of_Iio
  intro a
  by_cases ha : 0 < a
  · let f : Matrix (Fin m) (Fin n) ℝ → SymmetricMatrix (Fin n) := fun A =>
      ⟨a ^ 2 • 1 - Aᴴ * A,
        (by simp [Matrix.IsHermitian] : (a ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian).sub
          (Matrix.isHermitian_conjTranspose_mul_self A)⟩
    have hf : Continuous f := by
      apply Continuous.subtype_mk
      fun_prop
    have he : (SubGaussian.largestSingularValue (m := m) hn) ⁻¹' Set.Iio a =
        f ⁻¹' {H | H.1.PosDef} := by
      ext A
      have hg := SymmetricMatrix.gap_posDef_iff
        (⟨Aᴴ * A, Matrix.isHermitian_conjTranspose_mul_self A⟩ : SymmetricMatrix (Fin n)) (a ^ 2)
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_setOf_eq, f,
        largestSingularValue_eq, SingularValueBounds.largestSingularValue,
        Finset.sup'_lt_iff, singularValues, Finset.mem_univ, forall_true_left]
      exact (forall_congr' (fun j : Fin n => Real.sqrt_lt' (x :=
        (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues j) ha)).trans hg.symm
    rw [he]
    exact (isOpen_symmetric_posDef.preimage hf).measurableSet
  · have he : (SubGaussian.largestSingularValue (m := m) hn) ⁻¹' Set.Iio a = ∅ := by
      ext A
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false]
      rw [largestSingularValue_eq]
      have hnonneg : 0 ≤ SingularValueBounds.largestSingularValue A :=
        (singularValues_nonneg A ⟨0, hn⟩).trans (Finset.le_sup' _ (Finset.mem_univ _))
      exact not_lt.mpr ((le_of_not_gt ha).trans hnonneg)
    rw [he]
    exact MeasurableSet.empty

theorem ennreal_bound_of_real {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Set Ω} {b : ℝ}
    (hb : 0 ≤ b) (h : μ.real s ≤ b) : μ s ≤ ENNReal.ofReal b :=
  (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ s) hb).mpr h

end
end SingularValueBounds.Canonical
