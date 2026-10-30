import SingularValueBounds.KL.Weighted.Entropy
import SingularValueBounds.KL.Weighted.RationalIntegral

open MeasureTheory Set
open scoped ENNReal
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 800000

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The entropy integrand has at most quadratic growth on the nonnegative axis. -/
theorem abs_mul_log_le_one_add_sq {w : ℝ} (hw : 0 ≤ w) :
    |w * Real.log w| ≤ 1 + w^2 := by
  by_cases hw0 : w = 0
  · simp [hw0]
  have hwp : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  by_cases hw1 : w ≤ 1
  · have h := Real.abs_log_mul_self_lt w hwp hw1
    rw [mul_comm] at h
    nlinarith [sq_nonneg w]
  · have hw1' : 1 ≤ w := le_of_not_ge hw1
    rw [abs_of_nonneg (Real.mul_log_nonneg hw1')]
    have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hwp) hw
    nlinarith [sq_nonneg w]

/-- A second moment suffices for finite entropy, including weights which vanish. -/
theorem entropy_integrable_of_second_moment [IsFiniteMeasure μ] {W : Ω → ℝ}
    (hW : AEMeasurable W μ) (hW0 : ∀ ω, 0 ≤ W ω)
    (hW2 : Integrable (fun ω => W ω ^ 2) μ) :
    Integrable (fun ω => W ω * Real.log (W ω)) μ := by
  apply ((integrable_const (1 : ℝ)).add hW2).mono'
  · exact (Real.continuous_mul_log.measurable.comp_aemeasurable hW).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs, Pi.add_apply] using abs_mul_log_le_one_add_sq (hW0 ω))

/-- Exponential tails imply the finite entropy needed by weighted entropy. -/
theorem entropy_integrable_of_exponential_tail [IsFiniteMeasure μ]
    {Y : Ω → ℝ} {C r : ℝ}
    (hY : AEMeasurable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω) (hC : 0 ≤ C) (hr : 0 < r)
    (htail : ∀ u : ℝ, 0 ≤ u → μ.real {ω | u < Y ω} ≤ C * Real.exp (-(r*u))) :
    Integrable (fun ω => Y ω * Real.log (Y ω)) μ :=
  entropy_integrable_of_second_moment hY hY0
    (by simpa using (exponential_tail_moment hY hY0 hC hr htail 1).1)

/-- Normalizing a nonnegative variable of mean at least one gives a mean-one
weight below the original variable, hence preserves every upper-tail bound. -/
theorem normalized_weight_properties [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : Integrable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hMean : 1 ≤ ∫ ω, Y ω ∂μ) :
    let m := ∫ ω, Y ω ∂μ
    Integrable (fun ω => Y ω / m) μ ∧
    (∫ ω, Y ω / m ∂μ) = 1 ∧
    (∀ ω, 0 ≤ Y ω / m ∧ Y ω / m ≤ Y ω) ∧
    (∀ u : ℝ, μ.real {ω | u < Y ω / m} ≤ μ.real {ω | u < Y ω}) := by
  dsimp only
  have hm : 0 < ∫ ω, Y ω ∂μ := by linarith
  refine ⟨hY.div_const _, ?_, ?_, ?_⟩
  · rw [integral_div, div_self hm.ne']
  · intro ω
    exact ⟨div_nonneg (hY0 ω) hm.le, (div_le_iff₀ hm).2 (by nlinarith [hY0 ω])⟩
  · intro u
    apply measureReal_mono _ (measure_ne_top μ _)
    intro ω hω
    exact lt_of_lt_of_le hω ((div_le_iff₀ hm).2 (by nlinarith [hY0 ω]))

/-- Common upper-mean reduction. Gaussian comparison enters through the bound
`log E exp(Q/a) ≤ H`; the spectrum/entropy certificate bounds `a(D+H)`.
The tail proves all finiteness hypotheses, and the branch with mean below one
is handled before normalization. -/
theorem upper_mean_of_entropy [IsProbabilityMeasure μ]
    {Y Q : Ω → ℝ} {C r a H b : ℝ}
    (hY : AEMeasurable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hC : 0 ≤ C) (hr : 0 < r) (ha : 0 < a) (hb : b < 1)
    (htail : ∀ u : ℝ, 0 ≤ u → μ.real {ω | u < Y ω} ≤ C * Real.exp (-(r*u)))
    (hQ0 : ∀ᵐ ω ∂μ, 0 ≤ Q ω)
    (hExp : Integrable (fun ω => Real.exp (Q ω / a)) μ)
    (hGaussian : Real.log (∫ ω, Real.exp (Q ω / a) ∂μ) ≤ H)
    (hFixed : (∫ ω, Y ω ∂μ) ≤ 1-b + ∫ ω, Y ω * Q ω ∂μ)
    (hCost : ∀ W : Ω → ℝ, Integrable W μ → (∀ ω, 0 ≤ W ω) →
      (∫ ω, W ω ∂μ) = 1 → (∀ ω, W ω ≤ Y ω) →
      Integrable (fun ω => W ω * Real.log (W ω)) μ →
      a * ((∫ ω, W ω * Real.log (W ω) ∂μ) + H) ≤ b) :
    Integrable Y μ ∧ (∫ ω, Y ω ∂μ) ≤ 1 := by
  have hYi : Integrable Y μ := by
    simpa using (exponential_tail_moment hY hY0 hC hr htail 0).1
  refine ⟨hYi, ?_⟩
  by_cases hMean : (∫ ω, Y ω ∂μ) < 1
  · exact hMean.le
  have hm1 : 1 ≤ ∫ ω, Y ω ∂μ := le_of_not_gt hMean
  let m := ∫ ω, Y ω ∂μ
  let W : Ω → ℝ := fun ω => Y ω / m
  have hm : 0 < m := by dsimp [m]; linarith
  have hn := normalized_weight_properties hYi hY0 hm1
  change Integrable W μ ∧ _ at hn
  have hW0 : ∀ ω, 0 ≤ W ω := fun ω => (hn.2.2.1 ω).1
  have hWY : ∀ ω, W ω ≤ Y ω := fun ω => (hn.2.2.1 ω).2
  have hWE : Integrable (fun ω => W ω * Real.log (W ω)) μ := by
    apply entropy_integrable_of_exponential_tail (hY.div_const m) hW0 hC hr
    intro u hu
    exact (hn.2.2.2 u).trans (htail u hu)
  have hZ0 : ∀ᵐ ω ∂μ, 0 ≤ Q ω / a := hQ0.mono fun ω hω => div_nonneg hω ha.le
  have hWeighted := weighted_entropy_of_nonneg (Filter.Eventually.of_forall hW0)
    hZ0 hn.1 hn.2.1 hWE hExp
  have hWZi := integrable_weighted_of_nonneg (Filter.Eventually.of_forall hW0)
    hZ0 hn.1 hWE hExp
  have hWQi : Integrable (fun ω => W ω * Q ω) μ := by
    convert! hWZi.mul_const a using 1
    ext ω
    field_simp
  have hWQ : (∫ ω, W ω * Q ω ∂μ) ≤ b := by
    have hid : (∫ ω, W ω * (Q ω / a) ∂μ) = (∫ ω, W ω * Q ω ∂μ) / a := by
      simp_rw [← mul_div_assoc]
      rw [integral_div]
    rw [hid] at hWeighted
    have h := (div_le_iff₀ ha).1 hWeighted
    have hCost' := hCost W hn.1 hW0 hn.2.1 hWY hWE
    nlinarith
  have hid : (∫ ω, Y ω * Q ω ∂μ) = m * (∫ ω, W ω * Q ω ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by dsimp [W]; field_simp <;> ring
  rw [hid] at hFixed
  have hprod := mul_le_mul_of_nonneg_left hWQ hm.le
  change m ≤ 1-b+m*(∫ ω, W ω * Q ω ∂μ) at hFixed
  change m ≤ 1
  nlinarith

/-- Translation of a tail integral from a positive cutoff to zero. -/
private theorem tail_integral_translate (f : ℝ → ℝ) (c : ℝ) :
    (∫ u in Ioi 0, f (c+u)) = ∫ u in Ioi c, f u := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have h := integral_add_left_eq_self (μ := volume) ((Ioi c).indicator f) c
  convert! h using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    by_cases hu : 0 < u
    · simp [Set.indicator_of_mem, hu, show c < c+u by linarith]
    · simp [Set.indicator_of_notMem, hu, show ¬ c < c+u by linarith]

/-- The entropy tail integral in supplementary equation
`eq:app-up-entropy-integration`. Finiteness of the tail integral follows from
finite entropy; no analytic tail-integration premise is assumed. -/
theorem entropy_tail_integral [IsProbabilityMeasure μ] {W : Ω → ℝ} {c : ℝ}
    (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω)
    (hWi : Integrable W μ) (hMean : (∫ ω, W ω ∂μ) = 1)
    (hEntropy : Integrable (fun ω => W ω * Real.log (W ω)) μ) (hc : 0 < c) :
    (∫ ω, W ω * Real.log (W ω) ∂μ) ≤ Real.log c +
      ∫ u in Ioi c, (1 + Real.log (u/c)) * μ.real {ω | u < W ω} := by
  let U : Ω → ℝ := fun ω => max (W ω-c) 0
  let F : ℝ → ℝ := fun t => (c+t)*(Real.log (c+t)-Real.log c)
  let g : ℝ → ℝ := fun t => 1+Real.log (c+t)-Real.log c
  have hU0 : ∀ ω, 0 ≤ U ω := fun ω => le_max_right _ _
  have hg0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ g t := by
    intro t ht
    have hlog := Real.log_le_log hc (show c ≤ c+t by linarith)
    dsimp [g]
    linarith
  have hFn : ∀ t : ℝ, 0 ≤ t → 0 ≤ F t := by
    intro t ht
    exact mul_nonneg (by linarith) (sub_nonneg.mpr (Real.log_le_log hc (by linarith)))
  have hg : ContinuousOn g (Ici 0) := by
    apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.add continuousOn_const
    apply ContinuousOn.log (continuous_const.add continuous_id).continuousOn
    intro t ht
    exact ne_of_gt (by have ht0 : 0 ≤ t := ht; change 0 < c+t; linarith)
  have hgi : ∀ t > 0, IntervalIntegrable g volume 0 t := by
    intro t ht
    exact (hg.mono (fun u hu => hu.1)).intervalIntegrable_of_Icc ht.le
  have hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivAt F (g t) t := by
    intro t ht
    have hct : c+t ≠ 0 := ne_of_gt (by linarith)
    have hlin := (hasDerivAt_const t c).add (hasDerivAt_id t)
    convert! hlin.mul (hlin.log hct |>.sub_const (Real.log c)) using 1 <;>
      dsimp [F, g] <;> simp only [zero_add, id_eq, one_div] <;> field_simp <;> ring
  have hFi : ∀ t : ℝ, 0 ≤ t → (∫ u in (0 : ℝ)..t, g u) = F t := by
    intro t ht
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => hderiv u (by rw [uIcc_of_le ht] at hu; exact hu.1))
      ((hg.mono (fun u hu => hu.1)).intervalIntegrable_of_Icc ht)
    simpa [F] using hi
  have hFU : ∀ ω, F (U ω) =
      ({ω | c < W ω}.indicator (fun ω => W ω*Real.log (W ω)-W ω*Real.log c)) ω := by
    intro ω
    by_cases hw : c < W ω
    · simp only [Set.indicator, Set.mem_setOf_eq, hw, if_true]
      dsimp [F, U]
      rw [max_eq_left (by linarith : 0 ≤ W ω-c)]
      ring_nf
    · simp only [Set.indicator, Set.mem_setOf_eq, hw, if_false]
      dsimp [F, U]
      rw [max_eq_right (by linarith : W ω-c ≤ 0)]
      simp
  have hFint : Integrable (fun ω => F (U ω)) μ := by
    have hi := (hEntropy.sub (hWi.mul_const (Real.log c))).indicator
      (measurableSet_lt (measurable_const : Measurable (fun _ : Ω => c)) hW)
    exact hi.congr (Filter.Eventually.of_forall fun ω => (hFU ω).symm)
  have hPoint : ∀ ω, W ω*Real.log (W ω) ≤ W ω*Real.log c + F (U ω) := by
    intro ω
    rw [hFU]
    by_cases hw : c < W ω
    · simp only [Set.indicator, Set.mem_setOf_eq, hw, if_true]
      linarith
    · simp only [Set.indicator, Set.mem_setOf_eq, hw, if_false, add_zero]
      by_cases hw0 : W ω = 0
      · simp [hw0]
      · exact mul_le_mul_of_nonneg_left
          (Real.log_le_log (lt_of_le_of_ne (hW0 ω) (Ne.symm hw0)) (le_of_not_gt hw)) (hW0 ω)
  have hbound := integral_mono hEntropy ((hWi.mul_const (Real.log c)).add hFint) hPoint
  change (∫ ω, W ω*Real.log (W ω) ∂μ) ≤
    (∫ ω, W ω*Real.log c+F (U ω) ∂μ) at hbound
  rw [integral_add (hWi.mul_const _) hFint, integral_mul_const, hMean, one_mul] at hbound
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (Filter.Eventually.of_forall hU0) ((hW.sub_const c).max measurable_const).aemeasurable
    hgi (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu; exact hg0 u hu.le)
  have hleft : (∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..U ω, g t) ∂μ) =
      ENNReal.ofReal (∫ ω, F (U ω) ∂μ) := by
    simp_rw [hFi _ (hU0 _)]
    exact (ofReal_integral_eq_lintegral_ofReal hFint
      (Filter.Eventually.of_forall fun ω => hFn _ (hU0 ω))).symm
  have htail : ∀ u : ℝ, 0 < u → {ω | u < U ω} = {ω | c+u < W ω} := by
    intro u hu
    ext ω
    dsimp [U]
    simp only [Set.mem_setOf_eq, lt_max_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact False.elim (by linarith)
    · intro h
      exact Or.inl (by linarith)
  have hTm : Measurable (fun u : ℝ => μ {ω | c+u < W ω}) := by
    apply Antitone.measurable
    intro u v huv
    exact measure_mono (fun ω hω => by dsimp at *; linarith)
  have hgm : Measurable g := by dsimp [g]; fun_prop
  have hreal := integral_toReal (μ := volume.restrict (Ioi 0))
    (hTm.mul (ENNReal.measurable_ofReal.comp hgm)).aemeasurable
    (Filter.Eventually.of_forall fun u => ENNReal.mul_lt_top (measure_lt_top μ _) ENNReal.ofReal_lt_top)
  have hLayer' : (∫⁻ u in Ioi 0, μ {ω | c+u < W ω} * ENNReal.ofReal (g u)) =
      ENNReal.ofReal (∫ ω, F (U ω) ∂μ) := by
    rw [← hleft, hlayer]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [htail u hu]
  simp only [Function.comp_def, Pi.mul_apply] at hreal
  rw [hLayer', ENNReal.toReal_ofReal (integral_nonneg fun ω => hFn _ (hU0 ω))] at hreal
  have hprod : (∫ u in Ioi 0, (1+Real.log ((c+u)/c))*μ.real {ω | c+u < W ω}) =
      ∫ ω, F (U ω) ∂μ := by
    rw [← hreal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hcu : c+u ≠ 0 := ne_of_gt (add_pos hc hu)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hg0 u hu.le)]
    dsimp [g, Measure.real]
    rw [Real.log_div hcu hc.ne']
    ring
  have htranslate := tail_integral_translate
    (fun u => (1+Real.log (u/c))*μ.real {ω | u < W ω}) c
  rw [hprod] at htranslate
  rwa [← htranslate]

end
end SingularValueBounds.KL
