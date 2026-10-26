import SingularValueBounds.KL.Upper.GeneralMeanCells

/-! Kernel-checked coverage and scalar domains of the general upper-mean rows.
The polynomial certificates and entropy margins are separate obligations. -/
namespace SingularValueBounds.KL.Certificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def partitionValidDecidable {n : ℕ} (intervals : Fin n → ℚ × ℚ)
    (tree : RationalPartition n) (lo hi : ℚ) :
    Decidable (tree.Valid intervals lo hi) :=
  match tree with
  | .leaf _ => inferInstanceAs (Decidable (_ ∧ _))
  | .split p left right =>
      letI := partitionValidDecidable intervals left lo p
      letI := partitionValidDecidable intervals right p hi
      inferInstanceAs (Decidable (_ ∧ _))

private def clippedValidDecidable {n : ℕ} (rows : Fin n → RationalBox)
    (tree : ClippedTree n) (b : RationalBox) : Decidable (tree.Valid rows b) :=
  match tree with
  | .empty => inferInstanceAs (Decidable (_ ∨ _))
  | .row _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
  | .split ll lh hl hh =>
      letI := clippedValidDecidable rows ll ((clipSpectralBox b).child false false)
      letI := clippedValidDecidable rows lh ((clipSpectralBox b).child false true)
      letI := clippedValidDecidable rows hl ((clipSpectralBox b).child true false)
      letI := clippedValidDecidable rows hh ((clipSpectralBox b).child true true)
      inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

private instance instPartitionValidDecidable {n : ℕ} (intervals : Fin n → ℚ × ℚ) (tree : RationalPartition n)
    (lo hi : ℚ) : Decidable (tree.Valid intervals lo hi) :=
  partitionValidDecidable intervals tree lo hi

private instance instClippedValidDecidable {n : ℕ} (rows : Fin n → RationalBox) (tree : ClippedTree n)
    (b : RationalBox) : Decidable (tree.Valid rows b) :=
  clippedValidDecidable rows tree b

theorem generalMeanAPartition_valid :
    generalMeanAPartition.Valid generalMeanAIntervals 0 1 := by
  decide +kernel

theorem generalMeanClippedTrees_valid (ki : Fin 48) (ai : Fin 42) :
    (generalMeanClippedTrees ki ai).Valid
      (fun i => (generalMeanRows i).box) (generalMeanSeed ki ai) := by
  revert ki ai
  decide +kernel

theorem generalMeanRows_domains (i : Fin 1330) :
    0 ≤ (generalMeanRows i).klo ∧ (generalMeanRows i).khi ≤ 1 ∧
    0 ≤ (generalMeanRows i).alo ∧ (generalMeanRows i).ahi ≤ 1 ∧
    (generalMeanRows i).rateCompatible := by
  unfold GeneralMeanRow.rateCompatible
  revert i
  decide +kernel

end SingularValueBounds.KL.Certificates
