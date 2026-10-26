import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanGeometry

/-! Sound upper estimates obtained by selecting one of the small-range rates. -/
namespace SingularValueBounds.KL.Certificates

theorem roundUpQ_le_add (x : ℚ) : roundUpQ x ≤ x + 1 / roundingScale := by
  have hS : (0 : ℚ) < roundingScale := by norm_num [roundingScale]
  have h := Int.lt_floor_add_one (-(x * roundingScale))
  have hn : -(⌊-(x * roundingScale)⌋ : ℚ) ≤ x * roundingScale + 1 := by linarith
  unfold roundUpQ
  calc
    _ ≤ (x * roundingScale + 1) / roundingScale := div_le_div_of_nonneg_right hn hS.le
    _ = x + 1 / roundingScale := by rw [add_div, mul_div_cancel_right₀ _ hS.ne']

theorem endpointSmallBound_le_selected (i : Fin 50) (j : ℕ) (h : Fin 23)
    (hm : (j : ℚ)/200 * endpointSmallK i * ((endpointSmallQ h : ℚ)/100-1) ≤ 58/25) :
    endpointSmallBound i j ≤ roundUpQ
      (endpointSmallPrefactorQ (endpointSmallK i) ((endpointSmallQ h : ℚ)/100) *
        endpointDecayQ (endpointSmallQ h) j) := by
  have hi : Finset.univ.inf' Finset.univ_nonempty (endpointSmallBoundTerm i j) ≤
      endpointSmallBoundTerm i j h := Finset.inf'_le _ (Finset.mem_univ h)
  have hb : endpointSmallBound i j ≤ endpointSmallBoundTerm i j h :=
    (min_le_right _ _).trans hi
  simpa only [endpointSmallBoundTerm, if_pos hm] using hb

theorem endpointSmallBound_le_selected_add (i : Fin 50) (j : ℕ) (h : Fin 23)
    (hm : (j : ℚ)/200 * endpointSmallK i * ((endpointSmallQ h : ℚ)/100-1) ≤ 58/25) :
    endpointSmallBound i j ≤
      endpointSmallPrefactorQ (endpointSmallK i) ((endpointSmallQ h : ℚ)/100) *
        endpointDecayQ (endpointSmallQ h) j + 1 / roundingScale :=
  (endpointSmallBound_le_selected i j h hm).trans (roundUpQ_le_add _)

theorem endpointSmall_margin_of_le_one (i : Fin 50) (j : ℕ) (q : ℚ) (hq : q ≤ 1) :
    (j : ℚ)/200 * endpointSmallK i * (q-1) ≤ 58/25 := by
  have hk : 0 ≤ endpointSmallK i := by unfold endpointSmallK; positivity
  have h : (j : ℚ)/200 * endpointSmallK i * (q-1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by positivity) hk) (sub_nonpos.mpr hq)
  exact h.trans (by norm_num)

theorem endpointSmall_margin_of_upper (i : Fin 50) (j hi : ℕ) (q : ℚ)
    (hj : j ≤ hi) (hq : 1 ≤ q)
    (hm : (hi : ℚ)/200 * endpointSmallK i * (q-1) ≤ 58/25) :
    (j : ℚ)/200 * endpointSmallK i * (q-1) ≤ 58/25 := by
  have hk : 0 ≤ endpointSmallK i := by unfold endpointSmallK; positivity
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (by exact_mod_cast hj) (by norm_num)) hk)
      (sub_nonneg.mpr hq)).trans hm

end SingularValueBounds.KL.Certificates
