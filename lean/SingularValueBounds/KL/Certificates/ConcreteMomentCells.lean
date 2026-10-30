import SingularValueBounds.KL.Certificates.MomentCellSideConditions
import SingularValueBounds.KL.Certificates.IntegerMomentEvaluation

/-! The lower moment grid, with generic side conditions and bounded private
numerical lemmas. Each block is checked independently by Lean's kernel. -/
namespace SingularValueBounds.KL.LowerCertificates
open SingularValueBounds.KL.Certificates.NumericalCertificateConditions
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def momentPrimary (j : ℕ) : Prop :=
  let a : ℚ := (j + 30 : ℚ) / 1000
  let b : ℚ := (j + 31 : ℚ) / 1000
  let p := lowerCellPower (j + 30)
  (4 * p / ((p - 1) * generalLowerProfileQ a)) * b < 1 ∧
  a ^ 2 < lowerMPartialQ 59 ((4 * p / ((p - 1) * generalLowerProfileQ b)) * a) ∧
  (p - 1) * (logUpperQ (1 / (1 - (4 * p / ((p - 1) * generalLowerProfileQ a)) * b)) -
      (4 * p / ((p - 1) * generalLowerProfileQ a)) * b) / (2 * b ^ 2) +
    momentLogMinusOneQ (momentEllQ a p) + p * logUpperQ (p * momentBq b p) +
    1 / (expTaylorQ 24 (p - 1 / 20) - 1) < 3 * p

private theorem momentPrimary_block00 : ∀ i : Fin 32,
    0 * 32 + i.val < 681 → momentPrimary (0 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block01 : ∀ i : Fin 32,
    1 * 32 + i.val < 681 → momentPrimary (1 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block02 : ∀ i : Fin 32,
    2 * 32 + i.val < 681 → momentPrimary (2 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block03 : ∀ i : Fin 32,
    3 * 32 + i.val < 681 → momentPrimary (3 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block04 : ∀ i : Fin 32,
    4 * 32 + i.val < 681 → momentPrimary (4 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block05 : ∀ i : Fin 32,
    5 * 32 + i.val < 681 → momentPrimary (5 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block06 : ∀ i : Fin 32,
    6 * 32 + i.val < 681 → momentPrimary (6 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block07 : ∀ i : Fin 32,
    7 * 32 + i.val < 681 → momentPrimary (7 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block08 : ∀ i : Fin 32,
    8 * 32 + i.val < 681 → momentPrimary (8 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block09 : ∀ i : Fin 32,
    9 * 32 + i.val < 681 → momentPrimary (9 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block10 : ∀ i : Fin 32,
    10 * 32 + i.val < 681 → momentPrimary (10 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block11 : ∀ i : Fin 32,
    11 * 32 + i.val < 681 → momentPrimary (11 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block12 : ∀ i : Fin 32,
    12 * 32 + i.val < 681 → momentPrimary (12 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block13 : ∀ i : Fin 32,
    13 * 32 + i.val < 681 → momentPrimary (13 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block14 : ∀ i : Fin 32,
    14 * 32 + i.val < 681 → momentPrimary (14 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block15 : ∀ i : Fin 32,
    15 * 32 + i.val < 681 → momentPrimary (15 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block16 : ∀ i : Fin 32,
    16 * 32 + i.val < 681 → momentPrimary (16 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block17 : ∀ i : Fin 32,
    17 * 32 + i.val < 681 → momentPrimary (17 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block18 : ∀ i : Fin 32,
    18 * 32 + i.val < 681 → momentPrimary (18 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block19 : ∀ i : Fin 32,
    19 * 32 + i.val < 681 → momentPrimary (19 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block20 : ∀ i : Fin 32,
    20 * 32 + i.val < 681 → momentPrimary (20 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_block21 : ∀ i : Fin 32,
    21 * 32 + i.val < 681 → momentPrimary (21 * 32 + i.val) := by
  simp only [momentPrimary, lowerMPartialQ_eq_integer,
    momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
    logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
  decide +kernel

private theorem momentPrimary_all (j : Fin 681) : momentPrimary j.val := by
  have blocks (b : Fin 22) : ∀ i : Fin 32,
      b.val * 32 + i.val < 681 → momentPrimary (b.val * 32 + i.val) := by
    fin_cases b
    · exact momentPrimary_block00
    · exact momentPrimary_block01
    · exact momentPrimary_block02
    · exact momentPrimary_block03
    · exact momentPrimary_block04
    · exact momentPrimary_block05
    · exact momentPrimary_block06
    · exact momentPrimary_block07
    · exact momentPrimary_block08
    · exact momentPrimary_block09
    · exact momentPrimary_block10
    · exact momentPrimary_block11
    · exact momentPrimary_block12
    · exact momentPrimary_block13
    · exact momentPrimary_block14
    · exact momentPrimary_block15
    · exact momentPrimary_block16
    · exact momentPrimary_block17
    · exact momentPrimary_block18
    · exact momentPrimary_block19
    · exact momentPrimary_block20
    · exact momentPrimary_block21
  let b : Fin 22 := ⟨j.val / 32, by omega⟩
  let i : Fin 32 := ⟨j.val % 32, Nat.mod_lt _ (by norm_num)⟩
  have hi : b.val * 32 + i.val = j.val := by dsimp [b, i]; omega
  have h := blocks b i (by rw [hi]; exact j.isLt)
  simpa only [hi] using h

/-- Every rational moment-cell condition, including the separate endpoint cell. -/
theorem momentCellConditions : MomentCellConditions := by
  constructor
  · intro j
    obtain ⟨hu, hs, he⟩ := momentPrimary_all j
    exact MomentCellCertificate.of_primary (momentCell_grid j).1
      (momentCell_grid j).2.1 (momentCell_grid j).2.2.1 (momentCell_grid j).2.2.2 hu hs he
  · apply MomentCellCertificate.of_primary (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    · decide +kernel
    · simp only [lowerMPartialQ_eq_integer]
      decide +kernel
    · simp only [momentLogMinusOneQ, momentVQ, momentEllQ, logUpperQ,
        logTaylorUpperQ_eq_integer, expTaylorUpperQ_eq_integer, expTaylorQ_eq_integer]
      decide +kernel

end SingularValueBounds.KL.LowerCertificates
