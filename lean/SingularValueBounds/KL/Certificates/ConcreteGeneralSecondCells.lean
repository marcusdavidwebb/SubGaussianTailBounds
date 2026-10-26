import SingularValueBounds.KL.Upper.GeneralSecondData

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
  norm_num [secondExpLowerQ, secondDownQ, expTaylorUpperQ, expTaylorQ, Finset.sum_range_succ]

/-- All three small-range second-moment margins. -/
theorem secondSmallUpperQ_lt (i : Fin 3) : secondSmallUpperQ i < 9/2 := by
  fin_cases i <;>
    norm_num [secondSmallUpperQ, secondRareZQ, secondRarePQ, secondRarePolyQ, secondRareAQ,
      secondExpLowerQ, secondDownQ, expTaylorUpperQ, expTaylorQ, Finset.sum_range_succ]

/-- Every spectral cell's exact domain, sign and fourth-moment exclusion fields. -/
theorem secondCellConditions (j : Fin 334) :
    0 ≤ secondCellDLo j ∧ secondCellDLo j ≤ secondCellDHi j ∧ secondCellDHi j < 1 ∧
    2*secondCellDHi j < 50 ∧ 0 ≤ secondExpUpperQ (-2*secondCellDLo j) ∧
    0 ≤ secondExpLowerQ (-2*secondCellDHi j) ∧
    FourthExclusionCertificate (secondCellM j) (secondCellE j) (secondCellX j) := by
  revert j
  decide +kernel

end SingularValueBounds.KL.UpperSecond
