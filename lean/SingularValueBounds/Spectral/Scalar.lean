import SingularValueBounds.Spectral.Basic

/-! # The two scalar resolvent roots and the capped minimizer

These are the roots used in the variational proof, for an arbitrary finite
list of eigenvalues. No recursive barrier process is used.
-/

open Filter Set
open scoped BigOperators Topology

namespace SingularValueBounds

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def reciprocalTrace (d : ι → ℝ) (p : ℕ) (u : ℝ) : ℝ :=
  ∑ i, ((u - d i)⁻¹) ^ p

def aboveSpectrum (d : ι → ℝ) : Set ℝ := {u | ∀ i, d i < u}

theorem reciprocalTrace_pos (d : ι → ℝ) (p : ℕ) {u : ℝ}
    (hu : u ∈ aboveSpectrum d) : 0 < reciprocalTrace d p u := by
  exact Finset.sum_pos (fun i _ => pow_pos (inv_pos.mpr (sub_pos.mpr (hu i))) p)
    Finset.univ_nonempty

theorem reciprocalTrace_strictAnti (d : ι → ℝ) {p : ℕ} (hp : p ≠ 0) :
    StrictAntiOn (reciprocalTrace d p) (aboveSpectrum d) := by
  intro u hu v hv huv
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro i _
  exact pow_lt_pow_left₀
    (inv_lt_inv₀ (sub_pos.mpr (hv i)) (sub_pos.mpr (hu i)) |>.mpr (by linarith))
    (inv_nonneg.mpr (sub_nonneg.mpr (hv i).le)) hp

omit [Nonempty ι] in
theorem reciprocalTrace_continuousOn (d : ι → ℝ) (p : ℕ) :
    ContinuousOn (reciprocalTrace d p) (aboveSpectrum d) := by
  intro u hu
  apply ContinuousAt.continuousWithinAt
  unfold reciprocalTrace
  have hn : ∀ i, u - d i ≠ 0 := fun i => (sub_pos.mpr (hu i)).ne'
  fun_prop (disch := exact hn _)

omit [Nonempty ι] in
theorem reciprocalTrace_tendsto (d : ι → ℝ) {p : ℕ} (hp : p ≠ 0) :
    Tendsto (reciprocalTrace d p) atTop (𝓝 0) := by
  have ht : ∀ i, Tendsto (fun u : ℝ => (u - d i)⁻¹) atTop (𝓝 0) := fun i =>
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (-d i) tendsto_id)
  unfold reciprocalTrace
  simpa [sub_eq_add_neg, zero_pow hp] using
    tendsto_finset_sum Finset.univ (fun i _ => (ht i).pow p)

theorem exists_reciprocalTrace_eq (d : ι → ℝ) {p : ℕ} (hp : p ≠ 0)
    {c : ℝ} (hc : 0 < c) :
    ∃ u ∈ aboveSpectrum d, reciprocalTrace d p u = c := by
  let e := Finset.univ.sup' Finset.univ_nonempty d
  let a := e + (c + 1)⁻¹
  have hc1 : 0 < c + 1 := by linarith
  have hea : e < a := by dsimp [a]; exact lt_add_of_pos_right _ (inv_pos.mpr hc1)
  have hda : a ∈ aboveSpectrum d := fun i =>
    (Finset.le_sup' d (Finset.mem_univ i)).trans_lt hea
  have ha : c < reciprocalTrace d p a := by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
      Finset.univ_nonempty d
    have hai : (a - d i)⁻¹ = c + 1 := by
      change e = d i at hi
      dsimp [a]
      rw [hi]
      simp
    have hterm := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) =>
        (pow_pos (inv_pos.mpr (sub_pos.mpr (hda j))) p).le) (Finset.mem_univ i)
    change ((a - d i)⁻¹) ^ p ≤ reciprocalTrace d p a at hterm
    rw [hai] at hterm
    exact (show c < c + 1 by linarith).trans_le
      ((le_self_pow₀ (by linarith : 1 ≤ c + 1) hp).trans hterm)
  obtain ⟨b, hab, hb⟩ := ((eventually_gt_atTop a).and
    ((reciprocalTrace_tendsto d hp).eventually_lt_const hc)).exists
  have hcont := (reciprocalTrace_continuousOn d p).mono
    (show Icc a b ⊆ aboveSpectrum d from fun u hu i => (hda i).trans_le hu.1)
  obtain ⟨u, hu, heq⟩ := intermediate_value_Icc' hab.le hcont ⟨hb.le, ha.le⟩
  exact ⟨u, (fun i => (hda i).trans_le hu.1), heq⟩

def resolventRoot (d : ι → ℝ) (p : ℕ) (hp : p ≠ 0)
    (c : ℝ) (hc : 0 < c) : ℝ := (exists_reciprocalTrace_eq d hp hc).choose

theorem resolventRoot_above (d : ι → ℝ) {p : ℕ} (hp : p ≠ 0)
    {c : ℝ} (hc : 0 < c) :
    resolventRoot d p hp c hc ∈ aboveSpectrum d :=
  (exists_reciprocalTrace_eq d hp hc).choose_spec.1

theorem resolventRoot_eq (d : ι → ℝ) {p : ℕ} (hp : p ≠ 0)
    {c : ℝ} (hc : 0 < c) :
    reciprocalTrace d p (resolventRoot d p hp c hc) = c :=
  (exists_reciprocalTrace_eq d hp hc).choose_spec.2

theorem resolventRoot_unique (d : ι → ℝ) {p : ℕ} (hp : p ≠ 0)
    {c u : ℝ} (hc : 0 < c) (hu : u ∈ aboveSpectrum d)
    (heq : reciprocalTrace d p u = c) : u = resolventRoot d p hp c hc := by
  exact (reciprocalTrace_strictAnti d hp).injOn hu (resolventRoot_above d hp hc)
    (heq.trans (resolventRoot_eq d hp hc).symm)

theorem resolventRoot_le_iff (d : ι → ℝ) {p : ℕ} (hp : p ≠ 0)
    {c u : ℝ} (hc : 0 < c) :
    resolventRoot d p hp c hc ≤ u ↔
      u ∈ aboveSpectrum d ∧ reciprocalTrace d p u ≤ c := by
  constructor
  · intro hu
    have hu' : u ∈ aboveSpectrum d := fun i => (resolventRoot_above d hp hc i).trans_le hu
    refine ⟨hu', ?_⟩
    rw [← resolventRoot_eq d hp hc]
    exact (reciprocalTrace_strictAnti d hp).antitoneOn (resolventRoot_above d hp hc) hu' hu
  · rintro ⟨hu, hval⟩
    by_contra hn
    have hlt := reciprocalTrace_strictAnti d hp hu (resolventRoot_above d hp hc)
      (lt_of_not_ge hn)
    rw [resolventRoot_eq] at hlt
    exact (not_lt_of_ge hval) hlt

def cappedMinimizer (d : ι → ℝ) (φ η : ℝ) (hφ : 0 < φ) (hη : 0 < η) : ℝ :=
  max (resolventRoot d 1 (by decide) φ hφ)
    (resolventRoot d 2 (by decide) (η ^ 2) (sq_pos_of_pos hη))

theorem cappedMinimizer_above (d : ι → ℝ) {φ η : ℝ} (hφ : 0 < φ) (hη : 0 < η) :
    cappedMinimizer d φ η hφ hη ∈ aboveSpectrum d := fun i =>
  (resolventRoot_above d (by decide : 1 ≠ 0) hφ i).trans_le (le_max_left _ _)

theorem cappedMinimizer_trace (d : ι → ℝ) {φ η : ℝ} (hφ : 0 < φ) (hη : 0 < η) :
    reciprocalTrace d 1 (cappedMinimizer d φ η hφ hη) ≤ φ :=
  ((resolventRoot_le_iff d (by decide) hφ).mp (le_max_left _ _)).2

theorem cappedMinimizer_squareTrace (d : ι → ℝ) {φ η : ℝ} (hφ : 0 < φ) (hη : 0 < η) :
    reciprocalTrace d 2 (cappedMinimizer d φ η hφ hη) ≤ η ^ 2 :=
  ((resolventRoot_le_iff d (by decide) (sq_pos_of_pos hη)).mp (le_max_right _ _)).2

omit [Nonempty ι] in
/-- The supporting-line inequality for the inverse trace. Its nonnegative
remainder is a sum of rational squares. -/
theorem reciprocalTrace_support (d : ι → ℝ) {u v : ℝ}
    (hu : u ∈ aboveSpectrum d) (hv : v ∈ aboveSpectrum d) :
    reciprocalTrace d 1 u - (v - u) * reciprocalTrace d 2 u ≤
      reciprocalTrace d 1 v := by
  unfold reciprocalTrace
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hui := sub_pos.mpr (hu i)
  have hvi := sub_pos.mpr (hv i)
  have hid : (v - d i)⁻¹ - ((u - d i)⁻¹ - (v - u) * (u - d i)⁻¹ ^ 2) =
      (v - u) ^ 2 / ((u - d i) ^ 2 * (v - d i)) := by
    field_simp
    ring
  have hrhs : 0 ≤ (v - u) ^ 2 / ((u - d i) ^ 2 * (v - d i)) := by positivity
  simp only [pow_one]
  linarith

/-- The actual minimum in the paper's variational definition, attained at
the maximum of the two resolvent roots. -/
theorem cappedMinimizer_minimizes (d : ι → ℝ) {φ η : ℝ}
    (hφ : 0 < φ) (hη : 0 < η) {v : ℝ}
    (hv : v ∈ aboveSpectrum d) (htrace : reciprocalTrace d 1 v ≤ φ) :
    cappedMinimizer d φ η hφ hη +
      reciprocalTrace d 1 (cappedMinimizer d φ η hφ hη) / η ^ 2 ≤
    v + reciprocalTrace d 1 v / η ^ 2 := by
  let u := cappedMinimizer d φ η hφ hη
  have hsupport := reciprocalTrace_support d (cappedMinimizer_above d hφ hη) hv
  have hη2 := sq_pos_of_pos hη
  have hterm : 0 ≤ (v - u) * (η ^ 2 - reciprocalTrace d 2 u) := by
    by_cases hroots : resolventRoot d 1 (by decide) φ hφ ≤
        resolventRoot d 2 (by decide) (η ^ 2) hη2
    · have hu : u = resolventRoot d 2 (by decide) (η ^ 2) hη2 := max_eq_right hroots
      rw [hu, resolventRoot_eq]
      simp
    · have hu : u = resolventRoot d 1 (by decide) φ hφ := max_eq_left (le_of_not_ge hroots)
      have huv : u ≤ v := by
        rw [hu]
        exact (resolventRoot_le_iff d (by decide) hφ).mpr ⟨hv, htrace⟩
      exact mul_nonneg (sub_nonneg.mpr huv)
        (sub_nonneg.mpr (cappedMinimizer_squareTrace d hφ hη))
  change u + reciprocalTrace d 1 u / η ^ 2 ≤ v + reciprocalTrace d 1 v / η ^ 2
  apply (mul_le_mul_iff_left₀ hη2).mp
  simp only [add_mul, div_mul_cancel₀ _ hη2.ne']
  dsimp [u] at hterm ⊢
  nlinarith

end
end SingularValueBounds
