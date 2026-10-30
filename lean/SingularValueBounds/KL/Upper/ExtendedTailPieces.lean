import SingularValueBounds.KL.Upper.CertificateBridges
import SingularValueBounds.KL.Upper.ExtendedTails

/-! # Two-piece continuation of extended upper tails

The finite-threshold continuation in supplementary S1.6.1 chooses the allowed
rate continuously in the tail threshold. The functional lemmas isolate this
algebra; the matrix applications use the proved exact-shift tail bound.
-/
open MeasureTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section

def extendedTailCutoff (w k v : ℝ) : ℝ := w / (k * (v - 1))

def extendedTailPrefactor (v k C : ℝ) : ℝ :=
  Real.exp (-Real.log (1 - v * k ^ 2) / (2 * k ^ 2) + C / (2 * k ^ 2))

lemma extendedTailCutoff_pos {w k v : ℝ} (hw : 0 < w) (hk : 0 < k) (hv : 1 < v) :
    0 < extendedTailCutoff w k v := div_pos hw (mul_pos hk (sub_pos.mpr hv))

/-- The continuation rate is admissible and uses exactly the cap margin. -/
lemma extendedTail_continuation_rate {w k v K L u : ℝ}
    (hw : 0 < w) (hk : 0 < k) (hv : 1 < v) (hK : 0 < K) (hL : 0 < L)
    (hu : extendedTailCutoff w k v * K ^ 2 * L < u) :
    let vsmall := 1 + extendedTailCutoff w k v * (v - 1) * K ^ 2 * L / u
    1 < vsmall ∧ vsmall ≤ v ∧
      u * k * (vsmall - 1) = w * K ^ 2 * L := by
  have hs := extendedTailCutoff_pos hw hk hv
  have hu0 : 0 < u := (mul_pos (mul_pos hs (sq_pos_of_pos hK)) hL).trans hu
  have hv0 : 0 < v - 1 := sub_pos.mpr hv
  dsimp only
  have hpositive : 0 < extendedTailCutoff w k v * (v - 1) * K ^ 2 * L / u := by positivity
  refine ⟨by linarith, ?_, ?_⟩
  · have hh : extendedTailCutoff w k v * (v - 1) * K ^ 2 * L / u ≤ v - 1 := by
      apply (div_le_iff₀ hu0).mpr
      have hm := mul_le_mul_of_nonneg_right hu.le hv0.le
      nlinarith only [hm]
    linarith
  · unfold extendedTailCutoff
    field_simp [hk.ne', hv0.ne', hu0.ne']
    ring

/-- On the first interval the full tabulated rate is admissible. -/
theorem upper_extended_two_piece_low {tail : ℝ → ℝ} {K L w k v C u : ℝ}
    (hK : 0 < K) (hL : 0 < L) (hw : 0 < w) (hk : 0 < k) (hv : 1 < v)
    (hbase : ∀ (rate threshold : ℝ), 1 < rate → rate ≤ v → 0 ≤ threshold →
      threshold * k * (rate - 1) ≤ w * K ^ 2 * L →
      tail threshold ≤ Real.exp (-Real.log (1 - v * k ^ 2) / (2 * k ^ 2) +
        C / (2 * k ^ 2) - rate * threshold / (2 * K ^ 2)))
    (hu : 0 ≤ u) (hcut : u ≤ extendedTailCutoff w k v * K ^ 2 * L) :
    tail u ≤ extendedTailPrefactor v k C * Real.exp (-v * u / (2 * K ^ 2)) := by
  have hv0 : 0 < v - 1 := sub_pos.mpr hv
  have hmargin : u * k * (v - 1) ≤ w * K ^ 2 * L := by
    have hm := mul_le_mul_of_nonneg_right hcut (mul_nonneg hk.le hv0.le)
    have he : extendedTailCutoff w k v * K ^ 2 * L * (k * (v - 1)) = w * K ^ 2 * L := by
      unfold extendedTailCutoff
      field_simp [hk.ne', hv0.ne']
    rw [he] at hm
    nlinarith only [hm]
  have ht := hbase v u hv le_rfl hu hmargin
  unfold extendedTailPrefactor
  rw [← Real.exp_add]
  convert! ht using 1 <;> congr 1 <;> ring

/-- Past the cutoff, retain the complete finite-threshold penalty. -/
theorem upper_extended_two_piece_high {tail : ℝ → ℝ} {K L w k v C u : ℝ}
    (hK : 0 < K) (hL : 0 < L) (hw : 0 < w) (hk : 0 < k) (hv : 1 < v)
    (hbase : ∀ (rate threshold : ℝ), 1 < rate → rate ≤ v → 0 ≤ threshold →
      threshold * k * (rate - 1) ≤ w * K ^ 2 * L →
      tail threshold ≤ Real.exp (-Real.log (1 - v * k ^ 2) / (2 * k ^ 2) +
        C / (2 * k ^ 2) - rate * threshold / (2 * K ^ 2)))
    (hcut : extendedTailCutoff w k v * K ^ 2 * L < u) :
    tail u ≤ extendedTailPrefactor v k C *
      Real.exp (-u / (2 * K ^ 2) - extendedTailCutoff w k v * (v - 1) * L / 2) := by
  have hs := extendedTailCutoff_pos hw hk hv
  have hu0 : 0 < u := (mul_pos (mul_pos hs (sq_pos_of_pos hK)) hL).trans hcut
  obtain ⟨hr1, hrv, hm⟩ := extendedTail_continuation_rate hw hk hv hK hL hcut
  let rate := 1 + extendedTailCutoff w k v * (v - 1) * K ^ 2 * L / u
  have ht := hbase rate u hr1 hrv hu0.le hm.le
  unfold extendedTailPrefactor
  rw [← Real.exp_add]
  convert! ht using 1
  congr 1
  dsimp [rate]
  field_simp [hK.ne', hu0.ne']
  ring

/-- The two explicit pieces, with their common closed breakpoint. -/
def ExtendedUpperTailPieces (tail : ℝ → ℝ) (K L w k v C : ℝ) : Prop :=
  (∀ u : ℝ, 0 ≤ u → u ≤ extendedTailCutoff w k v * K ^ 2 * L →
    tail u ≤ extendedTailPrefactor v k C * Real.exp (-v * u / (2 * K ^ 2))) ∧
  (∀ u : ℝ, extendedTailCutoff w k v * K ^ 2 * L < u →
    tail u ≤ extendedTailPrefactor v k C *
      Real.exp (-u / (2 * K ^ 2) - extendedTailCutoff w k v * (v - 1) * L / 2))

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Actual exact-shift tail continuation; the whole-domain correction can
subsequently be supplied by one of the fifteen finite rate certificates. -/
theorem upperShift_tail_extended_two_pieces {X : Ω → ι → ℝ}
    {K L w b v C k eta : ℝ} (hsg : SubGaussianMGF μ X K)
    (hm : Measurable X) (hK : 0 < K) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (hw : 0 < w) (hL : 0 < L)
    (hcap : K ^ 2 * Matrix.trace R + w * K ^ 2 * L * eta ≤ b) (hb : b < 1)
    (hv : 1 < v) (hk : 0 < k) (hvk : v * k ^ 2 < 1) (hC : 0 ≤ C)
    (hbound : ∀ theta ∈ Icc (1 : ℝ) v, upperRateF v theta ≤ C)
    (heta : 0 < eta) (hnorm : eta ^ 2 = ∑ i, hR.isHermitian.eigenvalues i ^ 2)
    (hmax : ∀ i, hR.isHermitian.eigenvalues i ≤ k * eta) :
    ExtendedUpperTailPieces
      (fun u => μ.real {ω | u < (1 - b) * upperShift R hR (X ω)}) K L w k v C := by
  have hbase : ∀ (rate threshold : ℝ), 1 < rate → rate ≤ v → 0 ≤ threshold →
      threshold * k * (rate - 1) ≤ w * K ^ 2 * L →
      μ.real {ω | threshold < (1 - b) * upperShift R hR (X ω)} ≤
        Real.exp (-Real.log (1 - v * k ^ 2) / (2 * k ^ 2) + C / (2 * k ^ 2) -
          rate * threshold / (2 * K ^ 2)) := by
    intro rate threshold hr hrv ht hmargin
    exact upperShift_tail_extended hsg hm hK hR hw.le hL.le hcap hb hr hrv hk hvk hC
      hbound heta hnorm hmax ht hmargin
  constructor
  · intro u hu hcut
    exact upper_extended_two_piece_low hK hL hw hk hv hbase hu hcut
  · intro u hcut
    exact upper_extended_two_piece_high hK hL hw hk hv hbase hcut

/-- All fifteen tabulated rates have their complete two-piece probability
tails. Only finite rational rate-certificate facts remain numerical premises;
the spectral normalization is the actual `κ=M/η` of the input matrix. -/
theorem upperShift_tail_extended_two_pieces_of_certificates
    (hcert : Certificates.RateCertificateConditions) (i : Fin 15)
    {X : Ω → ι → ℝ} {K L w b : ℝ} (hsg : SubGaussianMGF μ X K)
    (hm : Measurable X) (hK : 0 < K) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (hw : 0 < w) (hL : 0 < L)
    (hcap : K ^ 2 * Matrix.trace R + w * K ^ 2 * L * frobenius R ≤ b) (hb : b < 1)
    (hvk : (Certificates.rateRows i).1 * spectralRatio R hR ^ 2 < 1) :
    ExtendedUpperTailPieces
      (fun u => μ.real {ω | u < (1 - b) * upperShift R hR (X ω)})
      K L w (spectralRatio R hR) (Certificates.rateRows i).1 (Certificates.rateRows i).2 := by
  have hv : (1 : ℝ) < (Certificates.rateRows i).1 := by
    fin_cases i <;> norm_num [Certificates.rateRows]
  have hC : (0 : ℝ) ≤ (Certificates.rateRows i).2 := by
    fin_cases i <;> norm_num [Certificates.rateRows]
  have hnorm : frobenius R ^ 2 = ∑ j, hR.isHermitian.eigenvalues j ^ 2 := by
    rw [frobenius_eq_sqrt_trace_square hR.isHermitian, Real.sq_sqrt (trace_square_pos hR).le,
      real_spectral_trace_square hR.isHermitian]
  have hmax : ∀ j, hR.isHermitian.eigenvalues j ≤ spectralRatio R hR * frobenius R := by
    intro j
    unfold spectralRatio
    rw [div_mul_cancel₀ _ (frobenius_pos hR).ne']
    exact eigenvalue_le_spectralMaximum hR.isHermitian j
  exact upperShift_tail_extended_two_pieces hsg hm hK hR hw hL hcap hb hv
    (spectralRatio_pos_le_one hR).1 hvk hC (fun theta ht => upper_rate_of_certificates hcert i ht)
    (frobenius_pos hR) hnorm hmax

end
end SingularValueBounds.KL
