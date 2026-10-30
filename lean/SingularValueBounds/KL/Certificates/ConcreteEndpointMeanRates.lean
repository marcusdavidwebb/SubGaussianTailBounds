import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanGeometry

/-! Uniform proof of the clipped endpoint rate bounds, including all grid indices. -/
namespace SingularValueBounds.KL.Certificates
set_option maxHeartbeats 2000000
private lemma clipped_rate_bounds (k u : ℚ) (opt : ℤ) (hk : 0 < k) (hk1 : k ≤ 1)
    (hu : 0 < u) :
    let margin : ℤ := 100 + ⌊100*(58/25)/(u*k)⌋
    let spectral : ℤ := -⌊-(100/k^2)⌋ - 1
    let z : ℤ := max 90 (min 200 (min opt (min margin spectral)))
    90 ≤ z.toNat ∧ z.toNat ≤ 200 ∧
      ((z.toNat : ℚ)/100)*k^2 < 1 ∧ u*k*((z.toNat : ℚ)/100-1) ≤ 58/25 := by
  dsimp only
  let margin : ℤ := 100 + ⌊100*(58/25)/(u*k)⌋
  let spectral : ℤ := -⌊-(100/k^2)⌋ - 1
  let z : ℤ := max 90 (min 200 (min opt (min margin spectral)))
  change 90 ≤ z.toNat ∧ z.toNat ≤ 200 ∧ _ ∧ _
  have hzlo : 90 ≤ z := le_max_left _ _
  have hz0 : 0 ≤ z := le_trans (by norm_num) hzlo
  have hzhi : z ≤ 200 := max_le (by norm_num) (min_le_left _ _)
  have hzcast : (z.toNat : ℚ) = (z : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hz0
  have hzm : z ≤ max 90 margin := by
    exact max_le_max_left _ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hzs : z ≤ max 90 spectral := by
    exact max_le_max_left _ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hk2 : 0 < k^2 := sq_pos_of_pos hk
  have hk21 : k^2 ≤ 1 := by nlinarith
  have huK : 0 < u*k := mul_pos hu hk
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [hzcast]
    have hs : (spectral : ℚ) < 100/k^2 := by
      have h := Int.lt_floor_add_one (-(100/k^2))
      dsimp [spectral]
      push_cast
      linarith
    have h90 : (90:ℚ) < 100/k^2 := (lt_div_iff₀ hk2).mpr (by nlinarith)
    have hz : (z:ℚ) < 100/k^2 :=
      (show (z:ℚ) ≤ max 90 (spectral:ℚ) by exact_mod_cast hzs).trans_lt (max_lt h90 hs)
    have h := (lt_div_iff₀ hk2).mp hz
    nlinarith
  · rw [hzcast]
    have hm : (margin : ℚ) ≤ 100+100*(58/25)/(u*k) := by
      dsimp [margin]
      push_cast
      exact add_le_add_left (Int.floor_le _) _
    have h90 : (90:ℚ) ≤ 100+100*(58/25)/(u*k) := by
      have : (0:ℚ) ≤ 100*(58/25)/(u*k) := by positivity
      linarith
    have hz : (z:ℚ) ≤ 100+100*(58/25)/(u*k) :=
      (show (z:ℚ) ≤ max 90 (margin:ℚ) by exact_mod_cast hzm).trans (max_le h90 hm)
    have hz' : (z:ℚ)-100 ≤ 100*(58/25)/(u*k) := by linarith
    have h := (le_div_iff₀ huK).mp hz'
    nlinarith
theorem endpointMean_jointRates (ki : Fin 60) (ai : Fin 42)
    (hactive : endpointMeanActive ki ai) (j : ℕ)
    (hj : j ∈ Finset.Ico (endpointMeanCutoff ki ai) 8000) :
    let q : ℚ := (endpointMeanRate ki ai j : ℚ) / 100
    90 ≤ endpointMeanRate ki ai j ∧ endpointMeanRate ki ai j ≤ 200 ∧
    q * (endpointMeanBox ki ai).top^2 < 1 ∧
    (j : ℚ) / 200 * (endpointMeanBox ki ai).top * (q - 1) ≤ 58 / 25 := by
  have hbox := endpointMean_jointBoxes ki ai hactive
  have hcut := endpointMean_jointCutoff ki ai hactive
  have hjpos : 0 < j := lt_of_lt_of_le hcut.1 (Finset.mem_Ico.mp hj).1
  exact clipped_rate_bounds _ _ _ (hbox.2.1.trans hbox.2.2.1)
    hbox.2.2.2 (by positivity)

end SingularValueBounds.KL.Certificates
