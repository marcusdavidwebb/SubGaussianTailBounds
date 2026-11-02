import SingularValueBounds.KL.Certificates.GeneralSecondSideConditions
import SingularValueBounds.KL.Certificates.IntegerMomentEvaluation

/-! Concrete fourth-moment exclusion conditions for the general upper bound.
All finite rational computations are checked by Lean's kernel. -/

namespace SingularValueBounds.KL.UpperSecond
open Certificates.NumericalCertificateConditions
set_option maxHeartbeats 800000000
set_option maxRecDepth 10000

private theorem fourthExclusion_iff (m E x : ℚ) : FourthExclusionCertificate m E x ↔
    0 < m ∧ 0 < x ∧ x < 50 ∧ 0 ≤ secondCoshLowerQ x ∧ 0 < secondExclusionQ m E x := by
  constructor
  · intro h
    exact ⟨h.m_pos, h.x_pos, h.x_domain, h.cosh_nonneg, h.exclusion⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩

local instance (m E x : ℚ) : Decidable (FourthExclusionCertificate m E x) :=
  decidable_of_iff _ (fourthExclusion_iff m E x).symm

/-- Uniform small-range exclusion. -/
theorem secondSmallExclusion :
    FourthExclusionCertificate 4 (secondExpUpperQ (1/25)) (5/2) := by
  constructor <;>
    norm_num [secondExclusionQ, secondCoshLowerQ, secondExpLowerQ, secondExpUpperQ,
      secondUpQ, secondDownQ, secondLogLowerQ, secondLogCount, secondLogReduced,
      expTaylorUpperQ, expTaylorQ, logTaylorQ, Finset.sum_range_succ]

/-- The lower exponential enclosure at the small-range endpoint is nonnegative. -/
theorem secondSmallExp_nonneg : 0 ≤ secondExpLowerQ (-1/25) := by
  exact (secondExp_nonneg (by norm_num)).1

/-- All three small-range second-moment margins. -/
theorem secondSmallUpperQ_lt (i : Fin 3) : secondSmallUpperQ i < 9/2 := by
  fin_cases i <;>
    norm_num [secondSmallUpperQ, secondRareZQ, secondRarePQ, secondRarePolyQ, secondRareAQ,
      secondExpLowerQ, secondDownQ, expTaylorUpperQ, expTaylorQ, Finset.sum_range_succ]

private def secondPrimary (j : ℕ) : Prop :=
  FourthExclusionCertificate (secondCellM (Fin.ofNat 334 j))
    (secondCellE (Fin.ofNat 334 j)) (secondCellX (Fin.ofNat 334 j))

private theorem secondPrimary_block00 : ∀ i : Fin 32,
    0 * 32 + i.val < 334 → secondPrimary (0 * 32 + i.val) := by
  simp only [secondPrimary, fourthExclusion_iff, secondCellM, secondCellE,
    secondCellX, secondCellDHi, secondCellHi, secondExclusionQ, secondCoshLowerQ,
    secondExpLowerQ, secondExpUpperQ, secondLogLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer, logTaylorQ_eq_integer]
  decide +kernel

private theorem secondPrimary_block01 : ∀ i : Fin 32,
    1 * 32 + i.val < 334 → secondPrimary (1 * 32 + i.val) := by
  simp only [secondPrimary, fourthExclusion_iff, secondCellM, secondCellE,
    secondCellX, secondCellDHi, secondCellHi, secondExclusionQ, secondCoshLowerQ,
    secondExpLowerQ, secondExpUpperQ, secondLogLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer, logTaylorQ_eq_integer]
  decide +kernel

private theorem secondPrimary_block02 : ∀ i : Fin 32,
    2 * 32 + i.val < 334 → secondPrimary (2 * 32 + i.val) := by
  simp only [secondPrimary, fourthExclusion_iff, secondCellM, secondCellE,
    secondCellX, secondCellDHi, secondCellHi, secondExclusionQ, secondCoshLowerQ,
    secondExpLowerQ, secondExpUpperQ, secondLogLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer, logTaylorQ_eq_integer]
  decide +kernel

private theorem secondPrimary_block03 : ∀ i : Fin 32,
    3 * 32 + i.val < 334 → secondPrimary (3 * 32 + i.val) := by
  simp only [secondPrimary, fourthExclusion_iff, secondCellM, secondCellE,
    secondCellX, secondCellDHi, secondCellHi, secondExclusionQ, secondCoshLowerQ,
    secondExpLowerQ, secondExpUpperQ, secondLogLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer, logTaylorQ_eq_integer]
  decide +kernel

private theorem secondPrimary_block04 : ∀ i : Fin 32,
    4 * 32 + i.val < 334 → secondPrimary (4 * 32 + i.val) := by
  simp only [secondPrimary, fourthExclusion_iff, secondCellM, secondCellE,
    secondCellX, secondCellDHi, secondCellHi, secondExclusionQ, secondCoshLowerQ,
    secondExpLowerQ, secondExpUpperQ, secondLogLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer, logTaylorQ_eq_integer]
  decide +kernel

private theorem secondPrimary_block05 : ∀ i : Fin 32,
    5 * 32 + i.val < 334 → secondPrimary (5 * 32 + i.val) := by
  simp only [secondPrimary, fourthExclusion_iff, secondCellM, secondCellE,
    secondCellX, secondCellDHi, secondCellHi, secondExclusionQ, secondCoshLowerQ,
    secondExpLowerQ, secondExpUpperQ, secondLogLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer, logTaylorQ_eq_integer]
  decide +kernel

private theorem secondPrimary_block06 : ∀ i : Fin 32,
    6 * 32 + i.val < 334 → secondPrimary (6 * 32 + i.val) := by
  simp only [secondPrimary, fourthExclusion_iff, secondCellM, secondCellE,
    secondCellX, secondCellDHi, secondCellHi, secondExclusionQ, secondCoshLowerQ,
    secondExpLowerQ, secondExpUpperQ, secondLogLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer, logTaylorQ_eq_integer]
  decide +kernel

private theorem secondPrimary_block07 : ∀ i : Fin 32,
    7 * 32 + i.val < 334 → secondPrimary (7 * 32 + i.val) := by
  simp only [secondPrimary, fourthExclusion_iff, secondCellM, secondCellE,
    secondCellX, secondCellDHi, secondCellHi, secondExclusionQ, secondCoshLowerQ,
    secondExpLowerQ, secondExpUpperQ, secondLogLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer, logTaylorQ_eq_integer]
  decide +kernel

private theorem secondPrimary_block08 : ∀ i : Fin 32,
    8 * 32 + i.val < 334 → secondPrimary (8 * 32 + i.val) := by
  simp only [secondPrimary, fourthExclusion_iff, secondCellM, secondCellE,
    secondCellX, secondCellDHi, secondCellHi, secondExclusionQ, secondCoshLowerQ,
    secondExpLowerQ, secondExpUpperQ, secondLogLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer, logTaylorQ_eq_integer]
  decide +kernel

private theorem secondPrimary_block09 : ∀ i : Fin 32,
    9 * 32 + i.val < 334 → secondPrimary (9 * 32 + i.val) := by
  simp only [secondPrimary, fourthExclusion_iff, secondCellM, secondCellE,
    secondCellX, secondCellDHi, secondCellHi, secondExclusionQ, secondCoshLowerQ,
    secondExpLowerQ, secondExpUpperQ, secondLogLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer, logTaylorQ_eq_integer]
  decide +kernel

private theorem secondPrimary_block10 : ∀ i : Fin 32,
    10 * 32 + i.val < 334 → secondPrimary (10 * 32 + i.val) := by
  simp only [secondPrimary, fourthExclusion_iff, secondCellM, secondCellE,
    secondCellX, secondCellDHi, secondCellHi, secondExclusionQ, secondCoshLowerQ,
    secondExpLowerQ, secondExpUpperQ, secondLogLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer, logTaylorQ_eq_integer]
  decide +kernel

private theorem secondPrimary_all (j : Fin 334) : secondPrimary j.val := by
  have blocks (b : Fin 11) : ∀ i : Fin 32,
      b.val * 32 + i.val < 334 → secondPrimary (b.val * 32 + i.val) := by
    fin_cases b
    · exact secondPrimary_block00
    · exact secondPrimary_block01
    · exact secondPrimary_block02
    · exact secondPrimary_block03
    · exact secondPrimary_block04
    · exact secondPrimary_block05
    · exact secondPrimary_block06
    · exact secondPrimary_block07
    · exact secondPrimary_block08
    · exact secondPrimary_block09
    · exact secondPrimary_block10
  let b : Fin 11 := ⟨j.val / 32, by omega⟩
  let i : Fin 32 := ⟨j.val % 32, Nat.mod_lt _ (by norm_num)⟩
  have hi : b.val * 32 + i.val = j.val := by dsimp [b, i]; omega
  have h := blocks b i (by rw [hi]; exact j.isLt)
  simpa only [hi] using h

/-- Every spectral cell's exact domain, sign and fourth-moment exclusion fields. -/
theorem secondCellConditions (j : Fin 334) :
    0 ≤ secondCellDLo j ∧ secondCellDLo j ≤ secondCellDHi j ∧ secondCellDHi j < 1 ∧
    2*secondCellDHi j < 50 ∧ 0 ≤ secondExpUpperQ (-2*secondCellDLo j) ∧
    0 ≤ secondExpLowerQ (-2*secondCellDHi j) ∧
    FourthExclusionCertificate (secondCellM j) (secondCellE j) (secondCellX j) := by
  refine ⟨(secondCell_basicConditions j).1, (secondCell_basicConditions j).2.1,
    (secondCell_basicConditions j).2.2.1, (secondCell_basicConditions j).2.2.2.1,
    (secondCell_basicConditions j).2.2.2.2.1, (secondCell_basicConditions j).2.2.2.2.2, ?_⟩
  have h := secondPrimary_all j
  have hj : Fin.ofNat 334 j.val = j := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt j.isLt
  simpa only [secondPrimary, hj] using h

end SingularValueBounds.KL.UpperSecond
