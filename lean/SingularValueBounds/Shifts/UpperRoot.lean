import SingularValueBounds.Shifts.UpperQuadraticComparison
import SingularValueBounds.Core.MeasurableMatrix

/-! # The exact upper-barrier shift (Lemma 3.2) -/

open Filter Set
open scoped BigOperators Matrix Topology

namespace SingularValueBounds

noncomputable section

variable {ι : Type*} [Fintype ι]

def spectralUpperResolvent (r : ι → ℝ) (h : ℝ) (i : ι) : ℝ :=
  r i / (1 + h * r i)

def spectralUpperDrop (r : ι → ℝ) (h : ℝ) : ℝ :=
  (∑ i, r i) - ∑ i, spectralUpperResolvent r h i

def spectralUpperEquation (r x : ι → ℝ) (h : ℝ) : ℝ :=
  (∑ i, x i ^ 2 * spectralUpperResolvent r h i ^ 2) -
    spectralUpperDrop r h * (1 - ∑ i, x i ^ 2 * spectralUpperResolvent r h i)

def spectralUpperCriterion (r x : ι → ℝ) (h : ℝ) : ℝ :=
  ∑ i, x i ^ 2 * (spectralUpperResolvent r h i +
    spectralUpperResolvent r h i ^ 2 / spectralUpperDrop r h)

omit [Fintype ι] in
theorem spectralUpperResolvent_pos {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    {h : ℝ} (hh : 0 ≤ h) (i : ι) : 0 < spectralUpperResolvent r h i := by
  exact div_pos (hr i) (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh (hr i).le))

theorem spectralUpperDrop_eq {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    {h : ℝ} (hh : 0 ≤ h) :
    spectralUpperDrop r h = h * ∑ i, r i ^ 2 / (1 + h * r i) := by
  unfold spectralUpperDrop spectralUpperResolvent
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hd : 0 < 1 + h * r i :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh (hr i).le)
  field_simp [hd.ne']
  ring

theorem spectralUpperDrop_pos [Nonempty ι] {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    {h : ℝ} (hh : 0 < h) : 0 < spectralUpperDrop r h := by
  rw [spectralUpperDrop_eq hr hh.le]
  exact mul_pos hh (Finset.sum_pos (fun i _ => div_pos (sq_pos_of_pos (hr i))
    (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh.le (hr i).le))) Finset.univ_nonempty)

theorem spectralUpperEquation_continuousOn {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (x : ι → ℝ) : ContinuousOn (spectralUpperEquation r x) (Ici 0) := by
  intro h hh
  have hne : ∀ i, 1 + h * r i ≠ 0 := fun i =>
    (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh (hr i).le)).ne'
  unfold spectralUpperEquation spectralUpperDrop spectralUpperResolvent
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := exact hne _)

omit [Fintype ι] in
theorem spectralUpperResolvent_tendsto {r : ι → ℝ} (hr : ∀ i, 0 < r i) (i : ι) :
    Tendsto (fun h => spectralUpperResolvent r h i) atTop (𝓝 0) := by
  have hd : Tendsto (fun h : ℝ => 1 + h * r i) atTop atTop := by
    simpa only [mul_comm, id_eq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add_atTop
      (Tendsto.const_mul_atTop (hr i) (tendsto_id : Tendsto (fun h : ℝ => h) atTop atTop))
  exact tendsto_const_nhds.div_atTop hd

theorem spectralUpperEquation_tendsto {r : ι → ℝ} (hr : ∀ i, 0 < r i) (x : ι → ℝ) :
    Tendsto (spectralUpperEquation r x) atTop (𝓝 (-(∑ i, r i))) := by
  have hsum : Tendsto (fun h => ∑ i, spectralUpperResolvent r h i) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum Finset.univ (fun i _ => spectralUpperResolvent_tendsto hr i)
  have hq1 : Tendsto (fun h => ∑ i, x i ^ 2 * spectralUpperResolvent r h i) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum Finset.univ (fun i _ =>
      (spectralUpperResolvent_tendsto hr i).const_mul (x i ^ 2))
  have hq2 : Tendsto (fun h => ∑ i, x i ^ 2 * spectralUpperResolvent r h i ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum Finset.univ (fun i _ =>
      ((spectralUpperResolvent_tendsto hr i).pow 2).const_mul (x i ^ 2))
  have htrace : Tendsto (fun _ : ℝ => ∑ i, r i) atTop (𝓝 (∑ i, r i)) := tendsto_const_nhds
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa only [spectralUpperEquation, spectralUpperDrop, sub_zero, mul_one, zero_sub] using
    hq2.sub ((htrace.sub hsum).mul (hone.sub hq1))

theorem spectralUpperEquation_zero_pos {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    {x : ι → ℝ} (hx : x ≠ 0) : 0 < spectralUpperEquation r x 0 := by
  simp only [spectralUpperEquation, spectralUpperDrop, spectralUpperResolvent,
    zero_mul, add_zero, div_one, sub_self, zero_mul, sub_zero]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hisq : 0 < x i ^ 2 := sq_pos_of_ne_zero hi
  exact lt_of_lt_of_le (mul_pos hisq (sq_pos_of_pos (hr i)))
    (Finset.single_le_sum (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Finset.mem_univ i))

/-- Existence of a positive exact shift in spectral coordinates, by the
intermediate value theorem applied to the equation after clearing its positive
trace-drop denominator. -/
theorem exists_spectralUpperEquation_zero [Nonempty ι] {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) {x : ι → ℝ} (hx : x ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ spectralUpperEquation r x δ = 0 := by
  have htrace : 0 < ∑ i, r i := Finset.sum_pos (fun i _ => hr i) Finset.univ_nonempty
  have hneg : ∀ᶠ h in atTop, spectralUpperEquation r x h < 0 :=
    (spectralUpperEquation_tendsto hr x).eventually_lt_const (neg_neg_of_pos htrace)
  obtain ⟨b, hb, hfb⟩ := ((eventually_gt_atTop (0 : ℝ)).and hneg).exists
  have hc := (spectralUpperEquation_continuousOn hr x).mono
    (show Icc 0 b ⊆ Ici 0 from fun _ h => h.1)
  obtain ⟨δ, hδ, heq⟩ := intermediate_value_Icc' hb.le hc
    (show (0 : ℝ) ∈ Icc (spectralUpperEquation r x b) (spectralUpperEquation r x 0) from
      ⟨hfb.le, (spectralUpperEquation_zero_pos hr hx).le⟩)
  refine ⟨δ, ?_, heq⟩
  have hδne : δ ≠ 0 := by
    intro hz
    rw [hz] at heq
    exact (ne_of_gt (spectralUpperEquation_zero_pos hr hx)) heq
  exact lt_of_le_of_ne hδ.1 hδne.symm

theorem spectralUpperEquation_iff_criterion [Nonempty ι] {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) (x : ι → ℝ) {h : ℝ} (hh : 0 < h) :
    spectralUpperEquation r x h = 0 ↔ spectralUpperCriterion r x h = 1 := by
  have hd := spectralUpperDrop_pos hr hh
  unfold spectralUpperEquation spectralUpperCriterion
  simp only [mul_add, Finset.sum_add_distrib, ← mul_div_assoc, ← Finset.sum_div]
  apply Iff.intro
  · intro heq
    have hq : (∑ i, x i ^ 2 * spectralUpperResolvent r h i ^ 2) / spectralUpperDrop r h =
        1 - ∑ i, x i ^ 2 * spectralUpperResolvent r h i := by
      apply (div_eq_iff hd.ne').2
      nlinarith only [heq]
    linarith
  · intro heq
    have := (div_eq_iff hd.ne').mp (show
      (∑ i, x i ^ 2 * spectralUpperResolvent r h i ^ 2) / spectralUpperDrop r h =
        1 - ∑ i, x i ^ 2 * spectralUpperResolvent r h i by linarith)
    linarith

omit [Fintype ι] in
theorem spectralUpperResolvent_strictAnti {r : ι → ℝ} (hr : ∀ i, 0 < r i) (i : ι) :
    StrictAntiOn (fun h => spectralUpperResolvent r h i) (Ici 0) := by
  intro a ha b hb hab
  apply div_lt_div_of_pos_left (hr i)
    (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg ha (hr i).le))
  nlinarith [mul_pos (sub_pos.mpr hab) (hr i)]

theorem spectralUpperDrop_strictMono [Nonempty ι] {r : ι → ℝ} (hr : ∀ i, 0 < r i) :
    StrictMonoOn (spectralUpperDrop r) (Ici 0) := by
  intro a ha b hb hab
  have hsum : (∑ i, spectralUpperResolvent r b i) < ∑ i, spectralUpperResolvent r a i := by
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun i _ => spectralUpperResolvent_strictAnti hr i ha hb hab)
  unfold spectralUpperDrop
  linarith

theorem spectralUpperCriterion_strictAnti [Nonempty ι] {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) {x : ι → ℝ} (hx : x ≠ 0) :
    StrictAntiOn (spectralUpperCriterion r x) (Ioi 0) := by
  intro a ha b hb hab
  have ha0 : 0 ≤ a := le_of_lt ha
  have hb0 : 0 ≤ b := le_of_lt hb
  have hda := spectralUpperDrop_pos hr ha
  have hdb := spectralUpperDrop_pos hr hb
  have hdrop := spectralUpperDrop_strictMono hr (a := a) (b := b)
    ha0 hb0 hab
  have hcoeff : ∀ i, spectralUpperResolvent r b i +
      spectralUpperResolvent r b i ^ 2 / spectralUpperDrop r b <
      spectralUpperResolvent r a i + spectralUpperResolvent r a i ^ 2 / spectralUpperDrop r a := by
    intro i
    have hri := spectralUpperResolvent_strictAnti hr i ha0 hb0 hab
    have hsa := spectralUpperResolvent_pos hr ha0 i
    have hsb := spectralUpperResolvent_pos hr hb0 i
    have hsq : spectralUpperResolvent r b i ^ 2 ≤ spectralUpperResolvent r a i ^ 2 := by
      nlinarith
    have hdiv := (div_le_div_of_nonneg_right hsq hdb.le).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) hda hdrop.le)
    linarith
  unfold spectralUpperCriterion
  apply Finset.sum_lt_sum
  · intro i _
    exact mul_le_mul_of_nonneg_left (hcoeff i).le (sq_nonneg _)
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (hcoeff i) (sq_pos_of_ne_zero hi)⟩

/-- The exact shift, defined by the unique scalar root, with value zero on
the zero vector. -/
def spectralUpperShift [Nonempty ι] (r : ι → ℝ) (hr : ∀ i, 0 < r i) (x : ι → ℝ) : ℝ :=
  if hx : x = 0 then 0 else (exists_spectralUpperEquation_zero hr hx).choose

theorem spectralUpperShift_zero [Nonempty ι] {r : ι → ℝ} (hr : ∀ i, 0 < r i) :
    spectralUpperShift r hr 0 = 0 := by simp [spectralUpperShift]

theorem spectralUpperShift_pos [Nonempty ι] {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    {x : ι → ℝ} (hx : x ≠ 0) : 0 < spectralUpperShift r hr x := by
  simp only [spectralUpperShift, dif_neg hx]
  exact (exists_spectralUpperEquation_zero hr hx).choose_spec.1

theorem spectralUpperShift_nonneg [Nonempty ι] {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (x : ι → ℝ) : 0 ≤ spectralUpperShift r hr x := by
  by_cases hx : x = 0
  · subst x; simp only [spectralUpperShift_zero]; exact le_rfl
  · exact (spectralUpperShift_pos hr hx).le

theorem spectralUpperShift_equation [Nonempty ι] {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    {x : ι → ℝ} (hx : x ≠ 0) :
    spectralUpperCriterion r x (spectralUpperShift r hr x) = 1 := by
  apply (spectralUpperEquation_iff_criterion hr x (spectralUpperShift_pos hr hx)).1
  simp only [spectralUpperShift, dif_neg hx]
  exact (exists_spectralUpperEquation_zero hr hx).choose_spec.2

theorem spectralUpperShift_unique [Nonempty ι] {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    {x : ι → ℝ} (hx : x ≠ 0) {h : ℝ} (hh : 0 < h)
    (heq : spectralUpperCriterion r x h = 1) : h = spectralUpperShift r hr x := by
  exact (spectralUpperCriterion_strictAnti hr hx).injOn hh (spectralUpperShift_pos hr hx)
    (heq.trans (spectralUpperShift_equation hr hx).symm)

theorem spectralUpperShift_lt_iff [Nonempty ι] {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (x : ι → ℝ) {h : ℝ} (hh : 0 < h) :
    h < spectralUpperShift r hr x ↔ 1 < spectralUpperCriterion r x h := by
  by_cases hx : x = 0
  · subst x
    simp only [spectralUpperShift_zero, spectralUpperCriterion, Pi.zero_apply, zero_pow
      (by decide : 2 ≠ 0), zero_mul, Finset.sum_const_zero]
    constructor <;> intro hbad <;> linarith
  · have hδ := spectralUpperShift_pos hr hx
    have heq := spectralUpperShift_equation hr hx
    constructor
    · intro hlt
      have := spectralUpperCriterion_strictAnti hr hx hh hδ hlt
      linarith
    · intro hgt
      by_contra hn
      have hle : spectralUpperShift r hr x ≤ h := le_of_not_gt hn
      have := (spectralUpperCriterion_strictAnti hr hx).antitoneOn hδ hh hle
      linarith

variable [DecidableEq ι] [Nonempty ι]

/-- The exact upper advance for a positive definite resolvent. -/
def upperShift (R : Matrix ι ι ℝ) (hR : R.PosDef) (x : ι → ℝ) : ℝ :=
  spectralUpperShift hR.isHermitian.eigenvalues hR.eigenvalues_pos
    (star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *ᵥ x)

omit [Nonempty ι] in
theorem upper_coordinates_ne_zero {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {x : ι → ℝ} (hx : x ≠ 0) :
    star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *ᵥ x ≠ 0 := by
  intro hzero
  apply hx
  have := congrArg (Matrix.mulVec (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ)) hzero
  simpa only [Matrix.mulVec_mulVec, hR.isHermitian.eigenvectorUnitary.2.2,
    Matrix.one_mulVec, Matrix.mulVec_zero] using this

theorem upperShift_zero {R : Matrix ι ι ℝ} (hR : R.PosDef) : upperShift R hR 0 = 0 := by
  simp only [upperShift, Matrix.mulVec_zero, spectralUpperShift_zero]

theorem upperShift_nonneg {R : Matrix ι ι ℝ} (hR : R.PosDef) (x : ι → ℝ) :
    0 ≤ upperShift R hR x := spectralUpperShift_nonneg _ _

theorem upperShift_pos {R : Matrix ι ι ℝ} (hR : R.PosDef) {x : ι → ℝ} (hx : x ≠ 0) :
    0 < upperShift R hR x := spectralUpperShift_pos _ (upper_coordinates_ne_zero hR hx)

theorem upperShift_pos_iff {R : Matrix ι ι ℝ} (hR : R.PosDef) (x : ι → ℝ) :
    0 < upperShift R hR x ↔ x ≠ 0 := by
  refine ⟨?_, upperShift_pos hR⟩
  intro hp hz
  subst x
  rw [upperShift_zero] at hp
  exact lt_irrefl _ hp

omit [Nonempty ι] in
theorem upperCriterion_quadratic_spectral {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (x : ι → ℝ) {h : ℝ} (hh : 0 ≤ h) :
    x ⬝ᵥ (upperCriterion R h *ᵥ x) =
      spectralUpperCriterion hR.isHermitian.eigenvalues
        (star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *ᵥ x) h := by
  rw [upperCriterion_spectral hR hh, quadratic_conjugate_diagonal]
  simp only [spectralUpperCriterion, spectralUpperResolvent, spectralUpperDrop_eq hR.eigenvalues_pos hh]

theorem upperShift_equation {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {x : ι → ℝ} (hx : x ≠ 0) :
    x ⬝ᵥ (upperCriterion R (upperShift R hR x) *ᵥ x) = 1 := by
  rw [upperCriterion_quadratic_spectral hR x (upperShift_nonneg hR x)]
  exact spectralUpperShift_equation _ (upper_coordinates_ne_zero hR hx)

theorem upperShift_unique {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {x : ι → ℝ} (hx : x ≠ 0) {h : ℝ} (hh : 0 < h)
    (heq : x ⬝ᵥ (upperCriterion R h *ᵥ x) = 1) : h = upperShift R hR x := by
  rw [upperCriterion_quadratic_spectral hR x hh.le] at heq
  exact spectralUpperShift_unique _ (upper_coordinates_ne_zero hR hx) hh heq

/-- The upper shift tail event is exactly a deterministic quadratic-form tail. -/
theorem upperShift_lt_iff {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (x : ι → ℝ) {h : ℝ} (hh : 0 < h) :
    h < upperShift R hR x ↔ 1 < x ⬝ᵥ (upperCriterion R h *ᵥ x) := by
  rw [upperCriterion_quadratic_spectral hR x hh.le]
  exact spectralUpperShift_lt_iff _ _ hh

/-- Lemma 3.2: the exact upper advance is controlled by a single fixed matrix. -/
theorem upperShift_quadratic_bound {R : Matrix ι ι ℝ} (hR : R.PosDef) (x : ι → ℝ) :
    upperShift R hR x ≤ (x ⬝ᵥ ((R ^ 2) *ᵥ x)) / Matrix.trace (R ^ 2) +
      upperShift R hR x * (x ⬝ᵥ (upperComparison R *ᵥ x)) := by
  by_cases hx : x = 0
  · subst x
    simp only [upperShift_zero, Matrix.mulVec_zero, dotProduct_zero, zero_div, zero_mul, add_zero, le_rfl]
  · exact upper_shift_quadratic_of_equation hR x (upperShift_pos hR hx) (upperShift_equation hR hx)

omit [Nonempty ι] in
theorem measurable_upperCriterion (h : ℝ) : Measurable (fun R : Matrix ι ι ℝ => upperCriterion R h) := by
  have hres : Measurable (fun R : Matrix ι ι ℝ => upperResolvent R h) :=
    measurable_matrix_inverse.comp (measurable_matrix_inverse.add_const _)
  have hsub : Measurable (fun R : Matrix ι ι ℝ => R - upperResolvent R h) :=
    (show Continuous (fun p : Matrix ι ι ℝ × Matrix ι ι ℝ => p.1 - p.2) by
      fun_prop).measurable.comp (measurable_id.prodMk hres)
  have hdrop : Measurable (fun R : Matrix ι ι ℝ => Matrix.trace (R - upperResolvent R h)) :=
    (continuous_id : Continuous (fun R : Matrix ι ι ℝ => R)).matrix_trace.measurable.comp
      hsub
  have hsquare : Measurable (fun R : Matrix ι ι ℝ => upperResolvent R h ^ 2) :=
    (show Continuous (fun R : Matrix ι ι ℝ => R ^ 2) by fun_prop).measurable.comp hres
  exact (show Continuous (fun p : Matrix ι ι ℝ × Matrix ι ι ℝ => p.1 + p.2) by
    fun_prop).measurable.comp (hres.prodMk (hdrop.inv.smul hsquare))

/-- Joint measurability of the shift in the positive definite matrix and row.
The proof uses the quadratic tail characterization, so it does not require a
continuous choice of eigenvectors. -/
theorem measurable_upperShift :
    Measurable (fun p : {R : Matrix ι ι ℝ // R.PosDef} × (ι → ℝ) => upperShift p.1.1 p.1.2 p.2) := by
  apply measurable_of_Ioi
  intro h
  rcases lt_trichotomy h 0 with hh | rfl | hh
  · have heq : (fun p : {R : Matrix ι ι ℝ // R.PosDef} × (ι → ℝ) =>
        upperShift p.1.1 p.1.2 p.2) ⁻¹' Ioi h = Set.univ := by
      ext p
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
      exact hh.trans_le (upperShift_nonneg p.1.2 p.2)
    rw [heq]
    exact MeasurableSet.univ
  · have heq : (fun p : {R : Matrix ι ι ℝ // R.PosDef} × (ι → ℝ) =>
        upperShift p.1.1 p.1.2 p.2) ⁻¹' Ioi 0 =
        (fun p : {R : Matrix ι ι ℝ // R.PosDef} × (ι → ℝ) => p.2) ⁻¹' ({0}ᶜ) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_Ioi, upperShift_pos_iff, Set.mem_compl_iff,
        Set.mem_singleton_iff]
    rw [heq]
    exact (measurableSet_singleton (0 : ι → ℝ)).compl.preimage measurable_snd
  · have heq : (fun p : {R : Matrix ι ι ℝ // R.PosDef} × (ι → ℝ) =>
        upperShift p.1.1 p.1.2 p.2) ⁻¹' Ioi h =
        {p | 1 < p.2 ⬝ᵥ (upperCriterion p.1.1 h *ᵥ p.2)} := by
      ext p
      exact upperShift_lt_iff p.1.2 p.2 hh
    rw [heq]
    have hm : Measurable (fun p : {R : Matrix ι ι ℝ // R.PosDef} × (ι → ℝ) =>
        p.2 ⬝ᵥ (upperCriterion p.1.1 h *ᵥ p.2)) := by
      have hmat : Measurable (fun p : {R : Matrix ι ι ℝ // R.PosDef} × (ι → ℝ) => p.1.1) :=
        measurable_subtype_coe.comp measurable_fst
      have hc := (measurable_upperCriterion h).comp hmat
      simp only [dotProduct, Matrix.mulVec]
      fun_prop
    exact measurableSet_lt measurable_const hm

end
end SingularValueBounds
