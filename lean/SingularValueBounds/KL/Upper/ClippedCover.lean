import SingularValueBounds.KL.Certificates.Polynomial

/-! Finite clipped subdivisions cover closed feasible spectral domains.
Empty leaves require strict inconsistency; degenerate boundary leaves use row aliases. -/
open Set
namespace SingularValueBounds.KL.Certificates
noncomputable section
set_option maxHeartbeats 1000000

def clipSpectralBox (b : RationalBox) : RationalBox :=
  let k := max b.bottom b.left
  ⟨max b.left (k^3),min b.right b.top,k,b.top⟩

def RationalBox.includes (outer inner : RationalBox) : Prop :=
  outer.left  ≤  inner.left ∧ inner.right  ≤  outer.right ∧
    outer.bottom  ≤  inner.bottom ∧ inner.top  ≤  outer.top

lemma RationalBox.includes_contains {outer inner : RationalBox} (h : outer.includes inner)
    {a k : ℝ} (hm : inner.contains a k) : outer.contains a k := by
  have h1 : (outer.left:ℝ) ≤ inner.left := by exact_mod_cast h.1
  have h2 : (inner.right:ℝ) ≤ outer.right := by exact_mod_cast h.2.1
  have h3 : (outer.bottom:ℝ) ≤ inner.bottom := by exact_mod_cast h.2.2.1
  have h4 : (inner.top:ℝ) ≤ outer.top := by exact_mod_cast h.2.2.2
  exact ⟨⟨h1.trans hm.1.1,hm.1.2.trans h2⟩,⟨h3.trans hm.2.1,hm.2.2.trans h4⟩⟩

lemma clipSpectralBox_preserves {b : RationalBox} (hb : 0 ≤ b.bottom) {a k : ℝ}
    (hm : b.contains a k) (ha : k^3 ≤ a ∧ a ≤ k) : (clipSpectralBox b).contains a k := by
  have hbR : (0:ℝ) ≤ b.bottom := by exact_mod_cast hb
  have hleft : (b.left:ℝ) ≤ k := hm.1.1.trans ha.2
  have hk : ((max b.bottom b.left:ℚ):ℝ) ≤ k := by push_cast; exact max_le hm.2.1 hleft
  have hk0 : (0:ℝ) ≤ ((max b.bottom b.left:ℚ):ℝ) := by push_cast; exact hbR.trans (le_max_left _ _)
  have hp := pow_le_pow_left₀ hk0 hk 3
  push_cast at hp
  dsimp [clipSpectralBox,RationalBox.contains]
  push_cast
  exact ⟨⟨max_le hm.1.1 (hp.trans ha.1),le_min hm.1.2 (ha.2.trans hm.2.2)⟩,
    ⟨by simpa only [Rat.cast_max] using hk,hm.2.2⟩⟩

inductive ClippedTree (n : ℕ) where
  | empty
  | row (index : Fin n)
  | split (ll lh hl hh : ClippedTree n)

def ClippedTree.Valid {n : ℕ} (rows : Fin n → RationalBox) : ClippedTree n → RationalBox → Prop
  | .empty,b => let c:=clipSpectralBox b; c.right<c.left ∨ c.top<c.bottom
  | .row i,b => (rows i).includes (clipSpectralBox b)
  | .split ll lh hl hh,b =>
      ll.Valid rows ((clipSpectralBox b).child false false) ∧
      lh.Valid rows ((clipSpectralBox b).child false true) ∧
      hl.Valid rows ((clipSpectralBox b).child true false) ∧
      hh.Valid rows ((clipSpectralBox b).child true true)

lemma clipSpectralBox_nonneg {b : RationalBox} (hb : 0 ≤ b.bottom) :
    0 ≤ (clipSpectralBox b).bottom := hb.trans (le_max_left _ _)

lemma RationalBox.child_nonneg {b : RationalBox} (hb : 0 ≤ b.bottom) (ht : 0 ≤ b.top) (x y : Bool) :
    0 ≤ (b.child x y).bottom ∧ 0 ≤ (b.child x y).top := by
  cases x <;> cases y <;> dsimp [RationalBox.child] <;> constructor <;> linarith

/-- Recursive clipping and all four closed children preserve complete coverage. -/
theorem ClippedTree.covers {n : ℕ} (tree : ClippedTree n) (rows : Fin n → RationalBox)
    (b : RationalBox) (hv : tree.Valid rows b) (hb : 0 ≤ b.bottom) (ht : 0 ≤ b.top)
    {a k : ℝ} (hm : b.contains a k) (ha : k^3 ≤ a ∧ a ≤ k) :
    ∃ i : Fin n,(rows i).contains a k := by
  induction tree generalizing b with
  | empty =>
    have hc := clipSpectralBox_preserves hb hm ha
    rcases hv with hv|hv
    · have hh : ((clipSpectralBox b).right:ℝ)<(clipSpectralBox b).left := by exact_mod_cast hv
      exact False.elim (by linarith [hc.1.1,hc.1.2])
    · have hh : ((clipSpectralBox b).top:ℝ)<(clipSpectralBox b).bottom := by exact_mod_cast hv
      exact False.elim (by linarith [hc.2.1,hc.2.2])
  | row i => exact ⟨i,RationalBox.includes_contains hv (clipSpectralBox_preserves hb hm ha)⟩
  | split ll lh hl hh ill ilh ihl ihh =>
    let c:=clipSpectralBox b
    have hc : c.contains a k := clipSpectralBox_preserves hb hm ha
    have hc0 : 0 ≤ c.bottom := clipSpectralBox_nonneg hb
    have hct : 0 ≤ c.top := ht
    by_cases hax : a ≤ ((c.left+c.right)/2:ℚ)
    · by_cases hk : k ≤ ((c.bottom+c.top)/2:ℚ)
      · exact ill _ hv.1 ((c.child_nonneg hc0 hct false false).1)
          ((c.child_nonneg hc0 hct false false).2) ⟨⟨hc.1.1,hax⟩,⟨hc.2.1,hk⟩⟩
      · exact ilh _ hv.2.1 ((c.child_nonneg hc0 hct false true).1)
          ((c.child_nonneg hc0 hct false true).2) ⟨⟨hc.1.1,hax⟩,⟨(lt_of_not_ge hk).le,hc.2.2⟩⟩
    · by_cases hk : k ≤ ((c.bottom+c.top)/2:ℚ)
      · exact ihl _ hv.2.2.1 ((c.child_nonneg hc0 hct true false).1)
          ((c.child_nonneg hc0 hct true false).2) ⟨⟨(lt_of_not_ge hax).le,hc.1.2⟩,⟨hc.2.1,hk⟩⟩
      · exact ihh _ hv.2.2.2 ((c.child_nonneg hc0 hct true true).1)
          ((c.child_nonneg hc0 hct true true).2) ⟨⟨(lt_of_not_ge hax).le,hc.1.2⟩,⟨(lt_of_not_ge hk).le,hc.2.2⟩⟩

inductive RationalPartition (n : ℕ) where
  | leaf (index : Fin n)
  | split (point : ℚ) (left right : RationalPartition n)

def RationalPartition.Valid {n : ℕ} (intervals : Fin n → ℚ×ℚ) :
    RationalPartition n → ℚ → ℚ → Prop
  | .leaf i,lo,hi => (intervals i).1 ≤ lo ∧ hi ≤ (intervals i).2
  | .split p left right,lo,hi => left.Valid intervals lo p ∧ right.Valid intervals p hi

theorem RationalPartition.covers {n : ℕ} (tree : RationalPartition n)
    (intervals : Fin n → ℚ×ℚ) (lo hi : ℚ) (hv : tree.Valid intervals lo hi)
    {x : ℝ} (hx : x∈Icc (lo:ℝ) (hi:ℝ)) :
    ∃ i : Fin n,x∈Icc ((intervals i).1:ℝ) ((intervals i).2:ℝ) := by
  induction tree generalizing lo hi with
  | leaf i =>
    have h1 : ((intervals i).1:ℝ) ≤ lo := by exact_mod_cast hv.1
    have h2 : (hi:ℝ) ≤ (intervals i).2 := by exact_mod_cast hv.2
    exact ⟨i,⟨h1.trans hx.1,hx.2.trans h2⟩⟩
  | split p left right il ir =>
    by_cases hp : x ≤ (p:ℝ)
    · exact il lo p hv.1 ⟨hx.1,hp⟩
    · exact ir p hi hv.2 ⟨(lt_of_not_ge hp).le,hx.2⟩

end
end SingularValueBounds.KL.Certificates
