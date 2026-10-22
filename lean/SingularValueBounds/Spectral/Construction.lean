import SingularValueBounds.Spectral.Scalar

/-! # The variational spectral bounds

The upper spectral bound is the value of the capped resolvent objective at
its minimizing root. The lower bound is obtained by reflection.
-/

open scoped BigOperators Matrix

namespace SingularValueBounds

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace SymmetricMatrix

theorem gap_spectral (H : SymmetricMatrix ι) (u : ℝ) :
    gap H u = (H.2.eigenvectorUnitary : Matrix ι ι ℝ) *
      Matrix.diagonal (fun i => u - H.2.eigenvalues i) *
      star (H.2.eigenvectorUnitary : Matrix ι ι ℝ) := by
  have hid : Matrix.diagonal (fun _ : ι => u) = u • (1 : Matrix ι ι ℝ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  rw [show Matrix.diagonal (fun i => u - H.2.eigenvalues i) =
    Matrix.diagonal (fun _ => u) - Matrix.diagonal H.2.eigenvalues from
    (Matrix.diagonal_sub _ _).symm, Matrix.mul_sub, Matrix.sub_mul, hid,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, H.2.eigenvectorUnitary.2.2]
  rw [← real_spectral_decomposition H.2]
  rfl

theorem gap_posDef_iff (H : SymmetricMatrix ι) (u : ℝ) :
    (gap H u).PosDef ↔ u ∈ aboveSpectrum H.2.eigenvalues := by
  constructor
  · intro hgap j
    have h := eigenvalue_gap_pos H.2 (a := u) (ε := 1)
      (by simpa only [one_smul] using hgap) j
    simpa only [one_mul, sub_pos] using h
  · intro hu
    rw [gap_spectral]
    exact unitary_conjugate_posDef _ _ (Matrix.PosDef.diagonal (fun i => sub_pos.mpr (hu i)))

theorem resolvent_spectral (H : SymmetricMatrix ι) {u : ℝ}
    (hu : (gap H u).PosDef) :
    resolvent H u = (H.2.eigenvectorUnitary : Matrix ι ι ℝ) *
      Matrix.diagonal (fun i => (u - H.2.eigenvalues i)⁻¹) *
      star (H.2.eigenvectorUnitary : Matrix ι ι ℝ) := by
  rw [resolvent, gap_spectral, unitary_conjugate_inverse,
    positive_diagonal_inverse _ (fun i => sub_pos.mpr ((gap_posDef_iff H u).mp hu i))]

theorem resolvent_powerTrace (H : SymmetricMatrix ι) {u : ℝ}
    (hu : (gap H u).PosDef) (p : ℕ) :
    Matrix.trace (resolvent H u ^ p) = reciprocalTrace H.2.eigenvalues p u := by
  let U := H.2.eigenvectorUnitary
  let A := Matrix.diagonal (fun i => (u - H.2.eigenvalues i)⁻¹)
  have hpow : ∀ p : ℕ, ((U : Matrix ι ι ℝ) * A * star (U : Matrix ι ι ℝ)) ^ p =
      (U : Matrix ι ι ℝ) * A ^ p * star (U : Matrix ι ι ℝ) := by
    intro p
    induction p with
    | zero => simp only [pow_zero, Matrix.mul_one, U.2.2]
    | succ p ih => rw [pow_succ, ih, unitary_conjugate_mul, pow_succ]
  rw [resolvent_spectral H hu, hpow, unitary_conjugate_trace]
  simp only [A, Matrix.diagonal_pow, Matrix.trace_diagonal, reciprocalTrace, Pi.pow_apply]

theorem resolvent_trace (H : SymmetricMatrix ι) {u : ℝ}
    (hu : (gap H u).PosDef) :
    Matrix.trace (resolvent H u) = reciprocalTrace H.2.eigenvalues 1 u := by
  simpa only [pow_one] using H.resolvent_powerTrace hu 1

theorem resolvent_squareTrace (H : SymmetricMatrix ι) {u : ℝ}
    (hu : (gap H u).PosDef) :
    Matrix.trace (resolvent H u ^ 2) = reciprocalTrace H.2.eigenvalues 2 u :=
  H.resolvent_powerTrace hu 2

end SymmetricMatrix

variable [Nonempty ι]

def spectralBarrier (φ η : ℝ) (hφ : 0 < φ) (hη : 0 < η)
    (H : SymmetricMatrix ι) : ℝ := cappedMinimizer H.2.eigenvalues φ η hφ hη

def spectralUpper (φ η : ℝ) (hφ : 0 < φ) (hη : 0 < η)
    (H : SymmetricMatrix ι) : ℝ :=
  SymmetricMatrix.objective η H (spectralBarrier φ η hφ hη H)

def spectralLower (φ η : ℝ) (hφ : 0 < φ) (hη : 0 < η)
    (H : SymmetricMatrix ι) : ℝ := -spectralUpper φ η hφ hη H.neg

theorem spectralBarrier_gap (φ η : ℝ) (hφ : 0 < φ) (hη : 0 < η)
    (H : SymmetricMatrix ι) :
    (H.gap (spectralBarrier φ η hφ hη H)).PosDef :=
  (H.gap_posDef_iff _).mpr (cappedMinimizer_above H.2.eigenvalues hφ hη)

theorem spectralBarrier_trace (φ η : ℝ) (hφ : 0 < φ) (hη : 0 < η)
    (H : SymmetricMatrix ι) :
    Matrix.trace (H.resolvent (spectralBarrier φ η hφ hη H)) ≤ φ := by
  rw [H.resolvent_trace (spectralBarrier_gap φ η hφ hη H)]
  exact cappedMinimizer_trace H.2.eigenvalues hφ hη

theorem spectralBarrier_squareTrace (φ η : ℝ) (hφ : 0 < φ) (hη : 0 < η)
    (H : SymmetricMatrix ι) :
    Matrix.trace (H.resolvent (spectralBarrier φ η hφ hη H) ^ 2) ≤ η ^ 2 := by
  rw [H.resolvent_squareTrace (spectralBarrier_gap φ η hφ hη H)]
  exact cappedMinimizer_squareTrace H.2.eigenvalues hφ hη

theorem spectralUpper_le_candidate (φ η : ℝ) (hφ : 0 < φ) (hη : 0 < η)
    (H : SymmetricMatrix ι) {u : ℝ} (hu : H.feasible φ u) :
    spectralUpper φ η hφ hη H ≤ H.objective η u := by
  unfold spectralUpper SymmetricMatrix.objective
  rw [H.resolvent_trace (spectralBarrier_gap φ η hφ hη H), H.resolvent_trace hu.1]
  apply cappedMinimizer_minimizes H.2.eigenvalues hφ hη
  · exact (H.gap_posDef_iff _).mp hu.1
  · rw [← H.resolvent_trace hu.1]
    exact hu.2

theorem spectralUpper_gap (φ η : ℝ) (hφ : 0 < φ) (hη : 0 < η)
    (H : SymmetricMatrix ι) :
    (H.gap (spectralUpper φ η hφ hη H)).PosDef := by
  apply (H.gap_posDef_iff _).mpr
  intro i
  have hu := (H.gap_posDef_iff _).mp (spectralBarrier_gap φ η hφ hη H) i
  have ht := reciprocalTrace_pos H.2.eigenvalues 1
    (cappedMinimizer_above H.2.eigenvalues hφ hη)
  change 0 < reciprocalTrace H.2.eigenvalues 1 (spectralBarrier φ η hφ hη H) at ht
  rw [← H.resolvent_trace (spectralBarrier_gap φ η hφ hη H)] at ht
  exact hu.trans (lt_add_of_pos_right _ (div_pos ht (sq_pos_of_pos hη)))

theorem spectralLower_gap (φ η : ℝ) (hφ : 0 < φ) (hη : 0 < η)
    (H : SymmetricMatrix ι) :
    (H.1 - spectralLower φ η hφ hη H • (1 : Matrix ι ι ℝ)).PosDef := by
  have h := spectralUpper_gap φ η hφ hη H.neg
  simpa [SymmetricMatrix.gap, SymmetricMatrix.neg, spectralLower, sub_eq_add_neg,
    add_comm] using h

theorem spectralUpper_le_shifted_candidate (φ η : ℝ) (hφ : 0 < φ) (hη : 0 < η)
    (H H' : SymmetricMatrix ι) (δ : ℝ)
    (hgap : (H'.gap (spectralBarrier φ η hφ hη H + δ)).PosDef)
    (htrace : Matrix.trace (H'.resolvent (spectralBarrier φ η hφ hη H + δ)) ≤
      Matrix.trace (H.resolvent (spectralBarrier φ η hφ hη H))) :
    spectralUpper φ η hφ hη H' ≤ spectralUpper φ η hφ hη H + δ := by
  calc
    spectralUpper φ η hφ hη H' ≤
        H'.objective η (spectralBarrier φ η hφ hη H + δ) :=
      spectralUpper_le_candidate φ η hφ hη H'
        ⟨hgap, htrace.trans (spectralBarrier_trace φ η hφ hη H)⟩
    _ ≤ spectralUpper φ η hφ hη H + δ := by
      unfold SymmetricMatrix.objective spectralUpper
      dsimp [SymmetricMatrix.objective]
      have hd := div_le_div_of_nonneg_right htrace (sq_nonneg η)
      linarith

theorem spectralUpper_translate_le (φ η : ℝ) (hφ : 0 < φ) (hη : 0 < η)
    (H : SymmetricMatrix ι) (a : ℝ) :
    spectralUpper φ η hφ hη (H.translate a) ≤ spectralUpper φ η hφ hη H + a := by
  have hgap : (H.translate a).gap (spectralBarrier φ η hφ hη H + a) =
      H.gap (spectralBarrier φ η hφ hη H) := by
    simp only [SymmetricMatrix.gap, SymmetricMatrix.translate, add_smul]
    abel
  apply spectralUpper_le_shifted_candidate φ η hφ hη H (H.translate a) a
  · rw [hgap]
    exact spectralBarrier_gap φ η hφ hη H
  · change Matrix.trace ((H.translate a).gap _ )⁻¹ ≤ _
    rw [hgap]
    exact le_rfl

theorem spectralUpper_translate (φ η : ℝ) (hφ : 0 < φ) (hη : 0 < η)
    (H : SymmetricMatrix ι) (a : ℝ) :
    spectralUpper φ η hφ hη (H.translate a) = spectralUpper φ η hφ hη H + a := by
  apply le_antisymm (spectralUpper_translate_le φ η hφ hη H a)
  have h := spectralUpper_translate_le φ η hφ hη (H.translate a) (-a)
  have hid : (H.translate a).translate (-a) = H := by
    apply Subtype.ext
    simp [SymmetricMatrix.translate]
  rw [hid] at h
  linarith

theorem spectralLower_translate (φ η : ℝ) (hφ : 0 < φ) (hη : 0 < η)
    (H : SymmetricMatrix ι) (a : ℝ) :
    spectralLower φ η hφ hη (H.translate a) = spectralLower φ η hφ hη H + a := by
  have hid : (H.translate a).neg = H.neg.translate (-a) := by
    apply Subtype.ext
    simp [SymmetricMatrix.translate, SymmetricMatrix.neg, add_comm]
  unfold spectralLower
  rw [hid, spectralUpper_translate]
  ring

theorem spectralUpper_zero (φ η : ℝ) (hφ : 0 < φ) (hη : 0 < η) :
    spectralUpper φ η hφ hη (SymmetricMatrix.zero : SymmetricMatrix ι) ≤
      Fintype.card ι / φ + φ / η ^ 2 := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hgap : (SymmetricMatrix.zero : SymmetricMatrix ι).gap (Fintype.card ι / φ) =
      Matrix.diagonal (fun _ : ι => Fintype.card ι / φ) := by
    ext i j
    by_cases h : i = j <;> simp [SymmetricMatrix.gap, SymmetricMatrix.zero, Matrix.diagonal, h]
  have htrace : Matrix.trace ((SymmetricMatrix.zero : SymmetricMatrix ι).resolvent
      (Fintype.card ι / φ)) = φ := by
    rw [SymmetricMatrix.resolvent, hgap,
      positive_diagonal_inverse _ (fun _ => div_pos hn hφ), Matrix.trace_diagonal]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_div]
    exact mul_div_cancel₀ φ hn.ne'
  have h := spectralUpper_le_candidate φ η hφ hη
    (SymmetricMatrix.zero : SymmetricMatrix ι)
    (u := Fintype.card ι / φ) ⟨by rw [hgap]; exact Matrix.PosDef.diagonal (fun _ => div_pos hn hφ),
      htrace.le⟩
  simpa only [SymmetricMatrix.objective, htrace] using h

end
end SingularValueBounds
