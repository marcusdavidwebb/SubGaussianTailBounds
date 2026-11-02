import SingularValueBounds.KL.Lower.CellAnalysis

/-! Exact rational rounded enclosures imply the logarithmic cell bounds. -/
open Set MeasureTheory
open scoped BigOperators
namespace SingularValueBounds.KL.LowerCertificates
open SingularValueBounds.KL.Certificates
open SingularValueBounds.KL.Certificates.NumericalCertificateConditions
noncomputable section
set_option maxHeartbeats 1000000

theorem le_roundUpQ (x : ℚ) : x ≤ roundUpQ x := by
  unfold roundUpQ
  apply (le_div_iff₀ (by norm_num : (0:ℚ) < 10^12)).2
  exact Int.le_ceil _

theorem roundDownQ_le (x : ℚ) : roundDownQ x ≤ x := by
  unfold roundDownQ
  apply (div_le_iff₀ (by norm_num : (0:ℚ) < 10^12)).2
  exact Int.floor_le _

theorem log_le_logUpperQ {x : ℚ} (hx : 1 ≤ x) : Real.log (x:ℝ) ≤ (logUpperQ x:ℝ) := by
  have hx' : (1:ℝ) ≤ x := by exact_mod_cast hx
  have hz := log_argument_transform hx'
  have h := log_ratio_le_logTaylorUpper 24 hz.1 hz.2.1
  rw [hz.2.2] at h
  have hc : (logTaylorUpperQ 24 ((x-1)/(x+1)):ℝ) =
      logTaylorUpper 24 (((x:ℝ)-1)/((x:ℝ)+1)) := by simp
  have hr : (logTaylorUpperQ 24 ((x-1)/(x+1)):ℝ) ≤ (logUpperQ x:ℝ) := by
    exact_mod_cast le_roundUpQ (logTaylorUpperQ 24 ((x-1)/(x+1)))
  rw [hc] at hr
  exact h.trans hr

theorem log_exp_sub_one_le {ell : ℝ} (h : 0 < ell) :
    Real.log (Real.exp ell-1) ≤ ell := by
  have hm := Real.log_le_log (sub_pos.mpr (Real.one_lt_exp_iff.mpr h))
    (by linarith : Real.exp ell-1 ≤ Real.exp ell)
  simpa using hm

theorem log_exp_sub_one_partial {ell v : ℝ} (hell : 0 < ell)
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hv : v ≤ Real.exp (-ell)) (N : ℕ) :
    Real.log (Real.exp ell-1) ≤ ell-∑ r ∈ Finset.range N,v^(r+1)/(r+1:ℝ) := by
  have he : Real.exp (-ell) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpos : 0 < 1-Real.exp (-ell) := by linarith
  have hfactor : Real.exp ell-1 = Real.exp ell*(1-Real.exp (-ell)) := by
    have hm : Real.exp ell*Real.exp (-ell) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  rw [hfactor,Real.log_mul (Real.exp_ne_zero _) hpos.ne',Real.log_exp]
  have hl := Real.log_le_log hpos (sub_le_sub_left hv 1)
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (show |v| < 1 by rwa [abs_of_nonneg hv0])
  have hp := sum_le_hasSum (Finset.range N) (by intros; positivity) hs
  linarith

theorem moment_log_minus_one_upper {ell : ℚ} (he : 0 < ell)
    (hv0 : ell < 8 → 0 ≤ momentVQ ell)
    (hv1 : ell < 8 → momentVQ ell < 1)
    (hve : ell < 8 → momentVQ ell*expTaylorUpperQ 40 ell ≤ 1) :
    Real.log (Real.exp (ell:ℝ)-1) ≤ (momentLogMinusOneQ ell:ℝ) := by
  have he' : (0:ℝ) < ell := by exact_mod_cast he
  unfold momentLogMinusOneQ
  split_ifs with hell
  · exact log_exp_sub_one_le he'
  · have hel : ell < 8 := lt_of_not_ge hell
    have hv : (momentVQ ell:ℝ) ≤ Real.exp (-(ell:ℝ)) := by
      have hExp := exp_le_expTaylorUpper (N:=40) he'.le
        (show (ell:ℝ) < (40:ℝ)+2 by exact_mod_cast (hel.trans (by norm_num : (8:ℚ) < 42)))
      have hval : (momentVQ ell:ℝ)*expTaylorUpper 40 (ell:ℝ) ≤ 1 := by
        rw [← cast_expTaylorUpperQ]
        exact_mod_cast hve hel
      have hv0' : (0:ℝ) ≤ momentVQ ell := by exact_mod_cast hv0 hel
      have hmul := (mul_le_mul_of_nonneg_left hExp hv0').trans hval
      rw [Real.exp_neg]
      rw [← one_div]
      apply (le_div_iff₀ (Real.exp_pos _)).2
      exact hmul
    have h := log_exp_sub_one_partial he' (by exact_mod_cast hv0 hel)
      (by exact_mod_cast hv1 hel) hv 6
    simpa using h

theorem momentEll_upper {a p : ℚ} (ha : 0 < a) (ha1 : a ≤ 1) (hp : (19:ℚ)/4 ≤ p) :
    momentLogM (a:ℝ) (p:ℝ) ≤ (momentEllQ a p:ℝ) := by
  have hD : 1 ≤ momentDq a p := by
    have hp' : (19:ℝ)/4 ≤ p := by
      have hh := (Rat.cast_le (K:=ℝ)).2 hp
      norm_num at hh
      exact hh
    have h := momentD_gt_one (k:=(a:ℝ)) (p:=(p:ℝ)) (by exact_mod_cast ha) (by exact_mod_cast ha1) hp'
    rw [← cast_momentDq] at h
    exact_mod_cast h.le
  have hlog := log_le_logUpperQ hD
  have hdiv := div_le_div_of_nonneg_right hlog (show (0:ℝ) ≤ 2*(a:ℝ)^2 by positivity)
  have hr : (logUpperQ (momentDq a p)/(2*a^2):ℝ) ≤ (momentEllQ a p:ℝ) := by
    have hh := (Rat.cast_le (K:=ℝ)).2 (le_roundUpQ (logUpperQ (momentDq a p)/(2*a^2)))
    simpa only [momentEllQ,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat] using hh
  dsimp [momentLogM]
  rw [← cast_momentDq]
  exact hdiv.trans (by simpa using hr)

theorem lowerJ_upperQ {q : ℚ} (hq0 : 0 ≤ q) (hq : q < 1) :
    lowerJ (q:ℝ) ≤ (logUpperQ (1/(1-q))-q:ℝ) := by
  have hq' : (q:ℝ) < 1 := by exact_mod_cast hq
  have hh : (1:ℚ) ≤ 1/(1-q) := (le_div_iff₀ (by linarith)).2 (by linarith)
  have h := log_le_logUpperQ hh
  have hid : Real.log ((1/(1-q):ℚ):ℝ) = -Real.log (1-(q:ℝ)) := by simp [Real.log_inv]
  rw [hid] at h
  dsimp [lowerJ]
  linarith

theorem epsilon_upper {p : ℚ} (hp : (19:ℚ)/4 ≤ p) :
    -Real.log (1-Real.exp (-((p:ℝ)-1/20))) ≤
      (1/(expTaylorQ 24 (p-1/20)-1):ℝ) := by
  have hp' : (19:ℝ)/4 ≤ p := by
    have hh := (Rat.cast_le (K:=ℝ)).2 hp
    norm_num at hh
    exact hh
  have hx : 0 < (p:ℝ)-1/20 := by linarith
  have hExp := expTaylor_le_exp 24 hx.le
  have hTaylor : 1 < expTaylor 24 ((p:ℝ)-1/20) := by
    have hfirst : 1+((p:ℝ)-1/20) ≤ expTaylor 24 ((p:ℝ)-1/20) := by
      unfold expTaylor
      have h := Finset.sum_le_sum_of_subset_of_nonneg
        (show Finset.range 2 ⊆ Finset.range 25 by intro i hi; simp only [Finset.mem_range] at *; omega)
        (fun i _ _ => by positivity : ∀ i ∈ Finset.range 25,i ∉ Finset.range 2 →
          0 ≤ ((p:ℝ)-1/20)^i/(Nat.factorial i:ℝ))
      have hsmall : (∑ i ∈ Finset.range 2,((p:ℝ)-1/20)^i/(Nat.factorial i:ℝ)) =
          1+((p:ℝ)-1/20) := by norm_num [Finset.sum_range_succ]
      rw [hsmall] at h
      exact h
    linarith
  have he : Real.exp (-((p:ℝ)-1/20)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr (sub_pos.mpr he))
  rw [Real.log_inv] at hl
  have hid : (1-Real.exp (-((p:ℝ)-1/20)))⁻¹-1 =
      1/(Real.exp ((p:ℝ)-1/20)-1) := by
    have ha : Real.exp ((p:ℝ)-1/20)-1 ≠ 0 := ne_of_gt
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx))
    have hb : 1-Real.exp (-((p:ℝ)-1/20)) ≠ 0 := ne_of_gt (sub_pos.mpr he)
    have hab : Real.exp ((p:ℝ)-1/20)*Real.exp (-((p:ℝ)-1/20)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hinv := mul_inv_cancel₀ hb
    apply (eq_div_iff ha).2
    have hm := congrArg (fun z : ℝ => z*(1-Real.exp (-((p:ℝ)-1/20)))⁻¹) hab
    have hm2 := congrArg (fun z : ℝ => Real.exp ((p:ℝ)-1/20)*z) hinv
    nlinarith
  rw [hid] at hl
  have hi := one_div_le_one_div_of_le (sub_pos.mpr hTaylor) (sub_le_sub_right hExp 1)
  have hc : (1/(expTaylorQ 24 (p-1/20)-1):ℝ) =
      1/(expTaylor 24 ((p:ℝ)-1/20)-1) := by simp
  rw [hc]
  exact hl.trans hi

end
end SingularValueBounds.KL.LowerCertificates
