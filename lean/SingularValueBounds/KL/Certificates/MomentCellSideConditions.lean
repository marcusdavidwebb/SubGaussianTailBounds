import SingularValueBounds.KL.Lower.CellEnclosures

/-!
Uniform side conditions for the lower moment certificates. These use the
existing logarithm/exponential enclosures and floor-rounding inequalities;
only the domain, shape and entropy margins need cell-specific arithmetic.
-/
namespace SingularValueBounds.KL.LowerCertificates
open SingularValueBounds.KL.Certificates
open SingularValueBounds.KL.Certificates.NumericalCertificateConditions

theorem momentEllQ_pos {a p : ℚ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hp : (19 : ℚ) / 4 ≤ p) : 0 < momentEllQ a p := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have ha1' : (a : ℝ) ≤ 1 := by exact_mod_cast ha1
  have hp' : (19 : ℝ) / 4 ≤ p := by
    have h := (Rat.cast_le (K := ℝ)).2 hp
    norm_num at h
    exact h
  have hm : 0 < momentLogM (a : ℝ) (p : ℝ) :=
    div_pos (Real.log_pos (momentD_gt_one ha' ha1' hp')) (by positivity)
  exact_mod_cast hm.trans_le (momentEll_upper ha ha1 hp)

theorem momentVQ_bounds {ell : ℚ} (he : 0 < ell) (hd : ell < 8) :
    0 ≤ momentVQ ell ∧ momentVQ ell < 1 ∧
      momentVQ ell * expTaylorUpperQ 40 ell ≤ 1 := by
  have he' : (0 : ℝ) < ell := by exact_mod_cast he
  have hd' : (ell : ℝ) < (40 : ℝ) + 2 := by exact_mod_cast (hd.trans (by norm_num : (8 : ℚ) < 42))
  have hupper : (1 : ℚ) < expTaylorUpperQ 40 ell := by
    have h := (Real.one_lt_exp_iff.mpr he').trans_le (exp_le_expTaylorUpper 40 he'.le hd')
    rw [← cast_expTaylorUpperQ] at h
    exact_mod_cast h
  have hpos : 0 < expTaylorUpperQ 40 ell := zero_lt_one.trans hupper
  have hnonneg : 0 ≤ momentVQ ell := by
    unfold momentVQ roundDownQ
    positivity
  have hle : momentVQ ell ≤ 1 / expTaylorUpperQ 40 ell := roundDownQ_le _
  refine ⟨hnonneg, hle.trans_lt ((div_lt_one hpos).mpr hupper), ?_⟩
  calc
    momentVQ ell * expTaylorUpperQ 40 ell ≤
        (1 / expTaylorUpperQ 40 ell) * expTaylorUpperQ 40 ell :=
      mul_le_mul_of_nonneg_right hle hpos.le
    _ = 1 := div_mul_cancel₀ _ hpos.ne'

/-- The stored power exceeds its required lower bound throughout the whole grid. -/
theorem lowerCellPower_ge {j : ℕ} (hjhi : j ≤ 710) :
    (19 : ℚ) / 4 ≤ lowerCellPower j := by
  let mid : ℚ := (2 * j + 1 : ℚ) / 2000
  change (19 : ℚ) / 4 ≤ if j < 650 then 37 / 10 + 13 / (10 * mid) - mid ^ 2 / 2
    else 12 - 10 * mid
  have hmpos : 0 < mid := by dsimp [mid]; positivity
  split_ifs with hj
  · have hj' : (j : ℚ) ≤ 649 := by exact_mod_cast (show j ≤ 649 by omega)
    have hmle : mid ≤ 13 / 20 := by dsimp [mid]; linarith
    have hsq : mid ^ 2 ≤ 1 := by nlinarith
    have hdiv : (2 : ℚ) ≤ 13 / (10 * mid) :=
      (le_div_iff₀ (by positivity)).mpr (by linarith)
    linarith
  · have hj' : (j : ℚ) ≤ 710 := by exact_mod_cast hjhi
    dsimp [mid]
    linarith

theorem momentCell_grid (j : Fin 681) :
    (0 : ℚ) < (j.val + 30 : ℚ) / 1000 ∧
    (j.val + 30 : ℚ) / 1000 ≤ (j.val + 31 : ℚ) / 1000 ∧
    (j.val + 31 : ℚ) / 1000 ≤ 711 / 1000 ∧
    (19 : ℚ) / 4 ≤ lowerCellPower (j.val + 30) := by
  have hj : (j.val : ℚ) ≤ 680 := by exact_mod_cast (show j.val ≤ 680 by omega)
  exact ⟨by positivity, by linarith, by linarith, lowerCellPower_ge (by omega)⟩

/-- Preserve the original certificate interface while deriving its generic fields. -/
theorem MomentCellCertificate.of_primary {a b p : ℚ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 711 / 1000) (hp : 19 / 4 ≤ p)
    (hu : (4 * p / ((p - 1) * generalLowerProfileQ a)) * b < 1)
    (hs : a ^ 2 < lowerMPartialQ 59 ((4 * p / ((p - 1) * generalLowerProfileQ b)) * a))
    (he : (p - 1) * (logUpperQ (1 / (1 - (4 * p / ((p - 1) * generalLowerProfileQ a)) * b)) -
          (4 * p / ((p - 1) * generalLowerProfileQ a)) * b) / (2 * b ^ 2) +
        momentLogMinusOneQ (momentEllQ a p) + p * logUpperQ (p * momentBq b p) +
        1 / (expTaylorQ 24 (p - 1 / 20) - 1) < 3 * p) : MomentCellCertificate a b p := by
  have hell := momentEllQ_pos ha (hab.trans (hb.trans (by norm_num))) hp
  exact ⟨ha, hab, hb, hp, hu, hs, hell,
    (fun h => (momentVQ_bounds hell h).1),
    (fun h => (momentVQ_bounds hell h).2.1),
    (fun h => (momentVQ_bounds hell h).2.2), he⟩

end SingularValueBounds.KL.LowerCertificates
