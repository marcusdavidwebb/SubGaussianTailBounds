import SingularValueBounds.KL.Barrier.MixedGeometry

/-! # A continuous inverse for the scalar mixed cap

The inverse is clipped at the endpoints so that its total extension stays
continuous and positive. On the cap interval it is the actual order inverse.
-/
open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace SingularValueBounds.KL
noncomputable section

lemma mixedProfile_image {g : ℝ → ℝ} {l : ℝ} (hl : l ≤ 1)
    (hc : ContinuousOn g (Icc l 1)) (hm : StrictMonoOn g (Icc l 1)) :
    g '' Icc l 1 = Icc (g l) (g 1) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨hm.monotoneOn ⟨le_rfl,hl⟩ hx hx.1,
      hm.monotoneOn hx ⟨hl,le_rfl⟩ hx.2⟩
  · exact intermediate_value_Icc hl hc

def mixedProfileIso (g : ℝ → ℝ) (l : ℝ) (hl : l ≤ 1)
    (hc : ContinuousOn g (Icc l 1)) (hm : StrictMonoOn g (Icc l 1)) :
    Icc l 1 ≃o Icc (g l) (g 1) :=
  (hm.orderIso g (Icc l 1)).trans
    (OrderIso.setCongr _ _ (mixedProfile_image hl hc hm))

lemma mixedProfileIso_apply (g : ℝ → ℝ) (l : ℝ) (hl : l ≤ 1)
    (hc : ContinuousOn g (Icc l 1)) (hm : StrictMonoOn g (Icc l 1)) (x : Icc l 1) :
    (mixedProfileIso g l hl hc hm x).1 = g x := rfl

def mixedInverse (g : ℝ → ℝ) (l : ℝ) (hl : l ≤ 1)
    (hc : ContinuousOn g (Icc l 1)) (hm : StrictMonoOn g (Icc l 1)) (c : ℝ) : ℝ :=
  ((mixedProfileIso g l hl hc hm).symm
    (projIcc (g l) (g 1) (hm.monotoneOn ⟨le_rfl,hl⟩ ⟨hl,le_rfl⟩ hl) c)).1

theorem continuous_mixedInverse (g : ℝ → ℝ) (l : ℝ) (hl : l ≤ 1)
    (hc : ContinuousOn g (Icc l 1)) (hm : StrictMonoOn g (Icc l 1)) :
    Continuous (mixedInverse g l hl hc hm) :=
  continuous_subtype_val.comp ((mixedProfileIso g l hl hc hm).symm.continuous.comp continuous_projIcc)

theorem mixedInverse_mem (g : ℝ → ℝ) (l : ℝ) (hl : l ≤ 1)
    (hc : ContinuousOn g (Icc l 1)) (hm : StrictMonoOn g (Icc l 1)) (c : ℝ) :
    mixedInverse g l hl hc hm c ∈ Icc l 1 :=
  ((mixedProfileIso g l hl hc hm).symm _).2

theorem mixedInverse_le_iff {g : ℝ → ℝ} {l : ℝ} (hl : l ≤ 1)
    (hc : ContinuousOn g (Icc l 1)) (hm : StrictMonoOn g (Icc l 1))
    {c x : ℝ} (hc' : c ∈ Icc (g l) (g 1)) (hx : x ∈ Icc l 1) :
    mixedInverse g l hl hc hm c ≤ x ↔ c ≤ g x := by
  let e := mixedProfileIso g l hl hc hm
  have hp : projIcc (g l) (g 1) (hm.monotoneOn ⟨le_rfl,hl⟩ ⟨hl,le_rfl⟩ hl) c = ⟨c,hc'⟩ :=
    projIcc_of_mem _ hc'
  unfold mixedInverse
  rw [hp]
  have he : e (e.symm ⟨c,hc'⟩) ≤ e ⟨x,hx⟩ ↔ e.symm ⟨c,hc'⟩ ≤ ⟨x,hx⟩ := e.le_iff_le
  simpa only [OrderIso.apply_symm_apply] using he.symm

theorem mixedInverse_apply {g : ℝ → ℝ} {l : ℝ} (hl : l ≤ 1)
    (hc : ContinuousOn g (Icc l 1)) (hm : StrictMonoOn g (Icc l 1))
    {x : ℝ} (hx : x ∈ Icc l 1) : mixedInverse g l hl hc hm (g x) = x := by
  have hgx : g x ∈ Icc (g l) (g 1) :=
    ⟨hm.monotoneOn ⟨le_rfl,hl⟩ hx hx.1,hm.monotoneOn hx ⟨hl,le_rfl⟩ hx.2⟩
  have hp : projIcc (g l) (g 1) (hm.monotoneOn ⟨le_rfl,hl⟩ ⟨hl,le_rfl⟩ hl) (g x) =
      mixedProfileIso g l hl hc hm ⟨x,hx⟩ := by
    apply Subtype.ext
    exact congrArg Subtype.val (projIcc_of_mem _ hgx)
  unfold mixedInverse
  rw [hp]
  exact congrArg Subtype.val ((mixedProfileIso g l hl hc hm).symm_apply_apply ⟨x,hx⟩)

end
end SingularValueBounds.KL
