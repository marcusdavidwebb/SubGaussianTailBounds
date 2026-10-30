import SingularValueBounds.KL.Upper.GeneralSecondData
import SingularValueBounds.KL.Certificates.IntegerMomentEvaluation

/-! Concrete second-moment upper margins, proved in bounded private blocks.
Each block checks all three margins for at most 32 cells using exact integer
Taylor evaluation; the original rational specification is unchanged. -/

namespace SingularValueBounds.KL.UpperSecond
open Certificates.NumericalCertificateConditions
set_option maxHeartbeats 800000000
set_option maxRecDepth 10000

private def secondUpperPrimary (j : ℕ) : Prop :=
  ∀ i : Fin 3, secondCellUpperQ (Fin.ofNat' 334 j) i < 9 / 2

private theorem secondUpperPrimary_block00 : ∀ k : Fin 32,
    0 * 32 + k.val < 334 → secondUpperPrimary (0 * 32 + k.val) := by
  simp only [secondUpperPrimary, secondCellUpperQ, secondCellM, secondCellE,
    secondCellDLo, secondCellDHi, secondCellLo, secondCellHi,
    secondExpUpperQ, secondExpLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer]
  decide +kernel

private theorem secondUpperPrimary_block01 : ∀ k : Fin 32,
    1 * 32 + k.val < 334 → secondUpperPrimary (1 * 32 + k.val) := by
  simp only [secondUpperPrimary, secondCellUpperQ, secondCellM, secondCellE,
    secondCellDLo, secondCellDHi, secondCellLo, secondCellHi,
    secondExpUpperQ, secondExpLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer]
  decide +kernel

private theorem secondUpperPrimary_block02 : ∀ k : Fin 32,
    2 * 32 + k.val < 334 → secondUpperPrimary (2 * 32 + k.val) := by
  simp only [secondUpperPrimary, secondCellUpperQ, secondCellM, secondCellE,
    secondCellDLo, secondCellDHi, secondCellLo, secondCellHi,
    secondExpUpperQ, secondExpLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer]
  decide +kernel

private theorem secondUpperPrimary_block03 : ∀ k : Fin 32,
    3 * 32 + k.val < 334 → secondUpperPrimary (3 * 32 + k.val) := by
  simp only [secondUpperPrimary, secondCellUpperQ, secondCellM, secondCellE,
    secondCellDLo, secondCellDHi, secondCellLo, secondCellHi,
    secondExpUpperQ, secondExpLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer]
  decide +kernel

private theorem secondUpperPrimary_block04 : ∀ k : Fin 32,
    4 * 32 + k.val < 334 → secondUpperPrimary (4 * 32 + k.val) := by
  simp only [secondUpperPrimary, secondCellUpperQ, secondCellM, secondCellE,
    secondCellDLo, secondCellDHi, secondCellLo, secondCellHi,
    secondExpUpperQ, secondExpLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer]
  decide +kernel

private theorem secondUpperPrimary_block05 : ∀ k : Fin 32,
    5 * 32 + k.val < 334 → secondUpperPrimary (5 * 32 + k.val) := by
  simp only [secondUpperPrimary, secondCellUpperQ, secondCellM, secondCellE,
    secondCellDLo, secondCellDHi, secondCellLo, secondCellHi,
    secondExpUpperQ, secondExpLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer]
  decide +kernel

private theorem secondUpperPrimary_block06 : ∀ k : Fin 32,
    6 * 32 + k.val < 334 → secondUpperPrimary (6 * 32 + k.val) := by
  simp only [secondUpperPrimary, secondCellUpperQ, secondCellM, secondCellE,
    secondCellDLo, secondCellDHi, secondCellLo, secondCellHi,
    secondExpUpperQ, secondExpLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer]
  decide +kernel

private theorem secondUpperPrimary_block07 : ∀ k : Fin 32,
    7 * 32 + k.val < 334 → secondUpperPrimary (7 * 32 + k.val) := by
  simp only [secondUpperPrimary, secondCellUpperQ, secondCellM, secondCellE,
    secondCellDLo, secondCellDHi, secondCellLo, secondCellHi,
    secondExpUpperQ, secondExpLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer]
  decide +kernel

private theorem secondUpperPrimary_block08 : ∀ k : Fin 32,
    8 * 32 + k.val < 334 → secondUpperPrimary (8 * 32 + k.val) := by
  simp only [secondUpperPrimary, secondCellUpperQ, secondCellM, secondCellE,
    secondCellDLo, secondCellDHi, secondCellLo, secondCellHi,
    secondExpUpperQ, secondExpLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer]
  decide +kernel

private theorem secondUpperPrimary_block09 : ∀ k : Fin 32,
    9 * 32 + k.val < 334 → secondUpperPrimary (9 * 32 + k.val) := by
  simp only [secondUpperPrimary, secondCellUpperQ, secondCellM, secondCellE,
    secondCellDLo, secondCellDHi, secondCellLo, secondCellHi,
    secondExpUpperQ, secondExpLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer]
  decide +kernel

private theorem secondUpperPrimary_block10 : ∀ k : Fin 32,
    10 * 32 + k.val < 334 → secondUpperPrimary (10 * 32 + k.val) := by
  simp only [secondUpperPrimary, secondCellUpperQ, secondCellM, secondCellE,
    secondCellDLo, secondCellDHi, secondCellLo, secondCellHi,
    secondExpUpperQ, secondExpLowerQ,
    expTaylorQ_eq_integer, expTaylorUpperQ_eq_integer]
  decide +kernel

private theorem secondUpperPrimary_all (j : Fin 334) : secondUpperPrimary j.val := by
  have blocks (b : Fin 11) : ∀ k : Fin 32,
      b.val * 32 + k.val < 334 → secondUpperPrimary (b.val * 32 + k.val) := by
    fin_cases b
    · exact secondUpperPrimary_block00
    · exact secondUpperPrimary_block01
    · exact secondUpperPrimary_block02
    · exact secondUpperPrimary_block03
    · exact secondUpperPrimary_block04
    · exact secondUpperPrimary_block05
    · exact secondUpperPrimary_block06
    · exact secondUpperPrimary_block07
    · exact secondUpperPrimary_block08
    · exact secondUpperPrimary_block09
    · exact secondUpperPrimary_block10
  let b : Fin 11 := ⟨j.val / 32, by omega⟩
  let k : Fin 32 := ⟨j.val % 32, Nat.mod_lt _ (by norm_num)⟩
  have hk : b.val * 32 + k.val = j.val := by dsimp [b, k]; omega
  have h := blocks b k (by rw [hk]; exact j.isLt)
  simpa only [hk] using h

/-- All three bounds in each of the 334 spectral cells. -/
theorem secondCellUpperQ_lt (j : Fin 334) (i : Fin 3) :
    secondCellUpperQ j i < 9 / 2 := by
  have h := secondUpperPrimary_all j
  have hj : Fin.ofNat' 334 j.val = j := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt j.isLt
  have hall : ∀ i : Fin 3, secondCellUpperQ j i < 9 / 2 := by
    simpa only [secondUpperPrimary, hj] using h
  exact hall i

end SingularValueBounds.KL.UpperSecond
