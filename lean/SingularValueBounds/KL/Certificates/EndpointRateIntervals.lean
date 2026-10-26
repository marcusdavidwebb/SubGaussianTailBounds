import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanRates

/-! Rational endpoint bounds certify whole runs of the clipped rate selector. -/
namespace SingularValueBounds.KL.Certificates

def endpointRateOpt (k a u : ℚ) : ℤ := ⌊100 * (u - 1) / (k * a + k^2 * (u - 1))⌋
def endpointRateMargin (kh u : ℚ) : ℤ := 100 + ⌊100 * (58 / 25) / (u * kh)⌋
def endpointRateSpectral (kh : ℚ) : ℤ := -⌊-(100 / kh^2)⌋ - 1
def endpointRateClip (opt margin spectral : ℤ) : ℕ :=
  (max 90 (min 200 (min opt (min margin spectral)))).toNat

theorem endpointRateOpt_mono (k a u v : ℚ) (hk : 0 < k) (ha : 0 < a)
    (hu : 1 ≤ u) (huv : u ≤ v) : endpointRateOpt k a u ≤ endpointRateOpt k a v := by
  apply Int.floor_mono
  have hka := mul_pos hk ha
  have hku : 0 ≤ k^2 * (u - 1) := mul_nonneg (sq_nonneg k) (by linarith)
  have hkv : 0 ≤ k^2 * (v - 1) := mul_nonneg (sq_nonneg k) (by linarith)
  apply (div_le_div_iff₀ (by linarith : 0 < k*a+k^2*(u-1))
    (by linarith : 0 < k*a+k^2*(v-1))).2
  have h : 0 ≤ k*a*(v-u) := mul_nonneg hka.le (sub_nonneg.mpr huv)
  nlinarith

theorem endpointRateMargin_antitone (kh u v : ℚ) (hk : 0 < kh)
    (hu : 0 < u) (huv : u ≤ v) : endpointRateMargin kh v ≤ endpointRateMargin kh u := by
  apply add_le_add_left
  apply Int.floor_mono
  exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hu hk)
    (mul_le_mul_of_nonneg_right huv hk.le)

theorem endpointRateClip_mono {o o' m m' s : ℤ} (ho : o ≤ o') (hm : m ≤ m') :
    endpointRateClip o m s ≤ endpointRateClip o' m' s := by
  apply Int.toNat_le_toNat
  exact max_le_max_left _ (min_le_min_left _ (min_le_min ho (min_le_min_right _ hm)))

theorem endpointRate_interval (k a kh lo hi u : ℚ)
    (hk : 0 < k) (ha : 0 < a) (hkh : 0 < kh) (hlo : 1 ≤ lo)
    (hlu : lo ≤ u) (huh : u ≤ hi) :
    endpointRateClip (endpointRateOpt k a lo) (endpointRateMargin kh hi)
      (endpointRateSpectral kh) ≤
        endpointRateClip (endpointRateOpt k a u) (endpointRateMargin kh u)
          (endpointRateSpectral kh) ∧
    endpointRateClip (endpointRateOpt k a u) (endpointRateMargin kh u)
      (endpointRateSpectral kh) ≤
        endpointRateClip (endpointRateOpt k a hi) (endpointRateMargin kh lo)
          (endpointRateSpectral kh) := by
  constructor
  · exact endpointRateClip_mono (endpointRateOpt_mono k a lo u hk ha hlo hlu)
      (endpointRateMargin_antitone kh u hi hkh (by linarith) huh)
  · exact endpointRateClip_mono (endpointRateOpt_mono k a u hi hk ha (hlo.trans hlu) huh)
      (endpointRateMargin_antitone kh lo u hkh (by linarith) hlu)

theorem endpointRate_constant_on_interval (k a kh lo hi u : ℚ) (q : ℕ)
    (hk : 0 < k) (ha : 0 < a) (hkh : 0 < kh) (hlo : 1 ≤ lo)
    (hlu : lo ≤ u) (huh : u ≤ hi)
    (hl : endpointRateClip (endpointRateOpt k a lo) (endpointRateMargin kh hi)
      (endpointRateSpectral kh) = q)
    (hh : endpointRateClip (endpointRateOpt k a hi) (endpointRateMargin kh lo)
      (endpointRateSpectral kh) = q) :
    endpointRateClip (endpointRateOpt k a u) (endpointRateMargin kh u)
      (endpointRateSpectral kh) = q := by
  have h := endpointRate_interval k a kh lo hi u hk ha hkh hlo hlu huh
  rw [hl, hh] at h
  exact le_antisymm h.2 h.1

end SingularValueBounds.KL.Certificates
