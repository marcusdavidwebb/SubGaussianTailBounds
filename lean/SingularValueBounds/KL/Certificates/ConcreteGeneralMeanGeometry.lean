import SingularValueBounds.KL.Upper.GeneralMeanCells

/-! Kernel-checked coverage and scalar domains of the general upper-mean rows.
Bounded private decisions validate every existing tree witness and row domain.
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

private def clippedRowValid (j : ℕ) : Prop :=
  ∀ ai : Fin 42, (generalMeanClippedTrees (Fin.ofNat 48 j) ai).Valid
    (fun i => (generalMeanRows i).box) (generalMeanSeed (Fin.ofNat 48 j) ai)

private theorem clippedRowValid_block00 : ∀ k : Fin 4,
    0 * 4 + k.val < 48 → clippedRowValid (0 * 4 + k.val) := by
  unfold clippedRowValid
  decide +kernel

private theorem clippedRowValid_block01 : ∀ k : Fin 4,
    1 * 4 + k.val < 48 → clippedRowValid (1 * 4 + k.val) := by
  unfold clippedRowValid
  decide +kernel

private theorem clippedRowValid_block02 : ∀ k : Fin 4,
    2 * 4 + k.val < 48 → clippedRowValid (2 * 4 + k.val) := by
  unfold clippedRowValid
  decide +kernel

private theorem clippedRowValid_block03 : ∀ k : Fin 4,
    3 * 4 + k.val < 48 → clippedRowValid (3 * 4 + k.val) := by
  unfold clippedRowValid
  decide +kernel

private theorem clippedRowValid_block04 : ∀ k : Fin 4,
    4 * 4 + k.val < 48 → clippedRowValid (4 * 4 + k.val) := by
  unfold clippedRowValid
  decide +kernel

private theorem clippedRowValid_block05 : ∀ k : Fin 4,
    5 * 4 + k.val < 48 → clippedRowValid (5 * 4 + k.val) := by
  unfold clippedRowValid
  decide +kernel

private theorem clippedRowValid_block06 : ∀ k : Fin 4,
    6 * 4 + k.val < 48 → clippedRowValid (6 * 4 + k.val) := by
  unfold clippedRowValid
  decide +kernel

private theorem clippedRowValid_block07 : ∀ k : Fin 4,
    7 * 4 + k.val < 48 → clippedRowValid (7 * 4 + k.val) := by
  unfold clippedRowValid
  decide +kernel

private theorem clippedRowValid_block08 : ∀ k : Fin 4,
    8 * 4 + k.val < 48 → clippedRowValid (8 * 4 + k.val) := by
  unfold clippedRowValid
  decide +kernel

private theorem clippedRowValid_block09 : ∀ k : Fin 4,
    9 * 4 + k.val < 48 → clippedRowValid (9 * 4 + k.val) := by
  unfold clippedRowValid
  decide +kernel

private theorem clippedRowValid_block10 : ∀ k : Fin 4,
    10 * 4 + k.val < 48 → clippedRowValid (10 * 4 + k.val) := by
  unfold clippedRowValid
  decide +kernel

private theorem clippedRowValid_block11 : ∀ k : Fin 4,
    11 * 4 + k.val < 48 → clippedRowValid (11 * 4 + k.val) := by
  unfold clippedRowValid
  decide +kernel

private theorem clippedRowValid_all (j : Fin 48) : clippedRowValid j.val := by
  have blocks (b : Fin 12) : ∀ k : Fin 4,
      b.val * 4 + k.val < 48 → clippedRowValid (b.val * 4 + k.val) := by
    fin_cases b
    · exact clippedRowValid_block00
    · exact clippedRowValid_block01
    · exact clippedRowValid_block02
    · exact clippedRowValid_block03
    · exact clippedRowValid_block04
    · exact clippedRowValid_block05
    · exact clippedRowValid_block06
    · exact clippedRowValid_block07
    · exact clippedRowValid_block08
    · exact clippedRowValid_block09
    · exact clippedRowValid_block10
    · exact clippedRowValid_block11
  let b : Fin 12 := ⟨j.val / 4, by omega⟩
  let k : Fin 4 := ⟨j.val % 4, Nat.mod_lt _ (by norm_num)⟩
  have hk : b.val * 4 + k.val = j.val := by dsimp [b, k]; omega
  have h := blocks b k (by rw [hk]; exact j.isLt)
  simpa only [hk] using h

theorem generalMeanClippedTrees_valid (ki : Fin 48) (ai : Fin 42) :
    (generalMeanClippedTrees ki ai).Valid
      (fun i => (generalMeanRows i).box) (generalMeanSeed ki ai) := by
  have h := clippedRowValid_all ki
  have hk : Fin.ofNat 48 ki.val = ki := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt ki.isLt
  simpa only [clippedRowValid, hk] using h ai

private def rowDomainValid (j : ℕ) : Prop :=
  let r := generalMeanRows (Fin.ofNat 1330 j)
  0 ≤ r.klo ∧ r.khi ≤ 1 ∧ 0 ≤ r.alo ∧ r.ahi ≤ 1 ∧ r.rateCompatible

private theorem rowDomainValid_block00 : ∀ k : Fin 32,
    0 * 32 + k.val < 1330 → rowDomainValid (0 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block01 : ∀ k : Fin 32,
    1 * 32 + k.val < 1330 → rowDomainValid (1 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block02 : ∀ k : Fin 32,
    2 * 32 + k.val < 1330 → rowDomainValid (2 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block03 : ∀ k : Fin 32,
    3 * 32 + k.val < 1330 → rowDomainValid (3 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block04 : ∀ k : Fin 32,
    4 * 32 + k.val < 1330 → rowDomainValid (4 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block05 : ∀ k : Fin 32,
    5 * 32 + k.val < 1330 → rowDomainValid (5 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block06 : ∀ k : Fin 32,
    6 * 32 + k.val < 1330 → rowDomainValid (6 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block07 : ∀ k : Fin 32,
    7 * 32 + k.val < 1330 → rowDomainValid (7 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block08 : ∀ k : Fin 32,
    8 * 32 + k.val < 1330 → rowDomainValid (8 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block09 : ∀ k : Fin 32,
    9 * 32 + k.val < 1330 → rowDomainValid (9 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block10 : ∀ k : Fin 32,
    10 * 32 + k.val < 1330 → rowDomainValid (10 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block11 : ∀ k : Fin 32,
    11 * 32 + k.val < 1330 → rowDomainValid (11 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block12 : ∀ k : Fin 32,
    12 * 32 + k.val < 1330 → rowDomainValid (12 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block13 : ∀ k : Fin 32,
    13 * 32 + k.val < 1330 → rowDomainValid (13 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block14 : ∀ k : Fin 32,
    14 * 32 + k.val < 1330 → rowDomainValid (14 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block15 : ∀ k : Fin 32,
    15 * 32 + k.val < 1330 → rowDomainValid (15 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block16 : ∀ k : Fin 32,
    16 * 32 + k.val < 1330 → rowDomainValid (16 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block17 : ∀ k : Fin 32,
    17 * 32 + k.val < 1330 → rowDomainValid (17 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block18 : ∀ k : Fin 32,
    18 * 32 + k.val < 1330 → rowDomainValid (18 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block19 : ∀ k : Fin 32,
    19 * 32 + k.val < 1330 → rowDomainValid (19 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block20 : ∀ k : Fin 32,
    20 * 32 + k.val < 1330 → rowDomainValid (20 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block21 : ∀ k : Fin 32,
    21 * 32 + k.val < 1330 → rowDomainValid (21 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block22 : ∀ k : Fin 32,
    22 * 32 + k.val < 1330 → rowDomainValid (22 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block23 : ∀ k : Fin 32,
    23 * 32 + k.val < 1330 → rowDomainValid (23 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block24 : ∀ k : Fin 32,
    24 * 32 + k.val < 1330 → rowDomainValid (24 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block25 : ∀ k : Fin 32,
    25 * 32 + k.val < 1330 → rowDomainValid (25 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block26 : ∀ k : Fin 32,
    26 * 32 + k.val < 1330 → rowDomainValid (26 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block27 : ∀ k : Fin 32,
    27 * 32 + k.val < 1330 → rowDomainValid (27 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block28 : ∀ k : Fin 32,
    28 * 32 + k.val < 1330 → rowDomainValid (28 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block29 : ∀ k : Fin 32,
    29 * 32 + k.val < 1330 → rowDomainValid (29 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block30 : ∀ k : Fin 32,
    30 * 32 + k.val < 1330 → rowDomainValid (30 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block31 : ∀ k : Fin 32,
    31 * 32 + k.val < 1330 → rowDomainValid (31 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block32 : ∀ k : Fin 32,
    32 * 32 + k.val < 1330 → rowDomainValid (32 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block33 : ∀ k : Fin 32,
    33 * 32 + k.val < 1330 → rowDomainValid (33 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block34 : ∀ k : Fin 32,
    34 * 32 + k.val < 1330 → rowDomainValid (34 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block35 : ∀ k : Fin 32,
    35 * 32 + k.val < 1330 → rowDomainValid (35 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block36 : ∀ k : Fin 32,
    36 * 32 + k.val < 1330 → rowDomainValid (36 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block37 : ∀ k : Fin 32,
    37 * 32 + k.val < 1330 → rowDomainValid (37 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block38 : ∀ k : Fin 32,
    38 * 32 + k.val < 1330 → rowDomainValid (38 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block39 : ∀ k : Fin 32,
    39 * 32 + k.val < 1330 → rowDomainValid (39 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block40 : ∀ k : Fin 32,
    40 * 32 + k.val < 1330 → rowDomainValid (40 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_block41 : ∀ k : Fin 32,
    41 * 32 + k.val < 1330 → rowDomainValid (41 * 32 + k.val) := by
  unfold rowDomainValid GeneralMeanRow.rateCompatible
  decide +kernel

private theorem rowDomainValid_all (j : Fin 1330) : rowDomainValid j.val := by
  have blocks (b : Fin 42) : ∀ k : Fin 32,
      b.val * 32 + k.val < 1330 → rowDomainValid (b.val * 32 + k.val) := by
    fin_cases b
    · exact rowDomainValid_block00
    · exact rowDomainValid_block01
    · exact rowDomainValid_block02
    · exact rowDomainValid_block03
    · exact rowDomainValid_block04
    · exact rowDomainValid_block05
    · exact rowDomainValid_block06
    · exact rowDomainValid_block07
    · exact rowDomainValid_block08
    · exact rowDomainValid_block09
    · exact rowDomainValid_block10
    · exact rowDomainValid_block11
    · exact rowDomainValid_block12
    · exact rowDomainValid_block13
    · exact rowDomainValid_block14
    · exact rowDomainValid_block15
    · exact rowDomainValid_block16
    · exact rowDomainValid_block17
    · exact rowDomainValid_block18
    · exact rowDomainValid_block19
    · exact rowDomainValid_block20
    · exact rowDomainValid_block21
    · exact rowDomainValid_block22
    · exact rowDomainValid_block23
    · exact rowDomainValid_block24
    · exact rowDomainValid_block25
    · exact rowDomainValid_block26
    · exact rowDomainValid_block27
    · exact rowDomainValid_block28
    · exact rowDomainValid_block29
    · exact rowDomainValid_block30
    · exact rowDomainValid_block31
    · exact rowDomainValid_block32
    · exact rowDomainValid_block33
    · exact rowDomainValid_block34
    · exact rowDomainValid_block35
    · exact rowDomainValid_block36
    · exact rowDomainValid_block37
    · exact rowDomainValid_block38
    · exact rowDomainValid_block39
    · exact rowDomainValid_block40
    · exact rowDomainValid_block41
  let b : Fin 42 := ⟨j.val / 32, by omega⟩
  let k : Fin 32 := ⟨j.val % 32, Nat.mod_lt _ (by norm_num)⟩
  have hk : b.val * 32 + k.val = j.val := by dsimp [b, k]; omega
  have h := blocks b k (by rw [hk]; exact j.isLt)
  simpa only [hk] using h

theorem generalMeanRows_domains (i : Fin 1330) :
    0 ≤ (generalMeanRows i).klo ∧ (generalMeanRows i).khi ≤ 1 ∧
    0 ≤ (generalMeanRows i).alo ∧ (generalMeanRows i).ahi ≤ 1 ∧
    (generalMeanRows i).rateCompatible := by
  have h := rowDomainValid_all i
  have hi : Fin.ofNat 1330 i.val = i := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  simpa only [rowDomainValid, hi] using h

end SingularValueBounds.KL.Certificates
