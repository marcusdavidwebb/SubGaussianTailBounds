import SingularValueBounds.KL.Statement
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# Finite polynomial certificates imply whole-domain bounds (P08)

Supplement S1.2: Bernstein, subdivision and critical-point rules. All
certificate fields are finite rational polynomial identities/comparisons.
The real-variable implications are proved here, not assumed from Python.
-/

open scoped BigOperators Polynomial
open Polynomial Set

namespace SingularValueBounds.KL.Certificates
noncomputable section

def bernsteinWeight (n i : ℕ) (u : ℝ) : ℝ :=
  (n.choose i : ℝ) * u ^ i * (1 - u) ^ (n - i)

theorem bernsteinWeight_nonneg (n i : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ bernsteinWeight n i u := by
  unfold bernsteinWeight
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hu0 _))
    (pow_nonneg (sub_nonneg.mpr hu1) _)

theorem bernsteinWeight_sum (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∑ i : Fin (n + 1), bernsteinWeight n i u = 1 := by
  simpa only [bernstein_apply, bernsteinWeight] using bernstein.probability n ⟨u, hu0, hu1⟩

theorem bernstein_sum_nonneg (n : ℕ) (b : Fin (n + 1) → ℝ)
    (hb : ∀ i, 0 ≤ b i) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ ∑ i, b i * bernsteinWeight n i u :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hb i) (bernsteinWeight_nonneg n i hu0 hu1)

theorem bernstein_sum_bounds (n : ℕ) (b : Fin (n + 1) → ℝ) {lo hi u : ℝ}
    (hb : ∀ i, lo ≤ b i ∧ b i ≤ hi) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    lo ≤ ∑ i, b i * bernsteinWeight n i u ∧
      ∑ i, b i * bernsteinWeight n i u ≤ hi := by
  have hs := bernsteinWeight_sum n hu0 hu1
  constructor
  · calc lo = ∑ i : Fin (n + 1), lo * bernsteinWeight n i u := by rw [← Finset.mul_sum, hs, mul_one]
         _ ≤ _ := Finset.sum_le_sum fun i _ =>
           mul_le_mul_of_nonneg_right (hb i).1 (bernsteinWeight_nonneg n i hu0 hu1)
  · calc _ ≤ ∑ i : Fin (n + 1), hi * bernsteinWeight n i u :=
           Finset.sum_le_sum fun i _ =>
             mul_le_mul_of_nonneg_right (hb i).2 (bernsteinWeight_nonneg n i hu0 hu1)
         _ = hi := by rw [← Finset.mul_sum, hs, mul_one]

def realEval (p : ℚ[X]) (x : ℝ) : ℝ := p.eval₂ (Rat.castHom ℝ) x

def bernsteinExpansion (n : ℕ) (b : Fin (n + 1) → ℚ) : ℚ[X] :=
  ∑ i, C (b i) * bernsteinPolynomial ℚ n i

/-- A finite polynomial identity and a finite list of coefficient signs. -/
structure BernsteinCertificate (p : ℚ[X]) (n : ℕ) (b : Fin (n + 1) → ℚ) : Prop where
  identity : p = bernsteinExpansion n b
  nonnegative : ∀ i, 0 ≤ b i

theorem realEval_expansion (n : ℕ) (b : Fin (n + 1) → ℚ) (x : ℝ) :
    realEval (bernsteinExpansion n b) x =
      ∑ i, (b i : ℝ) * bernsteinWeight n i x := by
  simp [realEval, bernsteinExpansion, Polynomial.eval₂_finset_sum, Polynomial.eval₂_pow, Polynomial.eval₂_sub, bernsteinPolynomial, bernsteinWeight]

theorem BernsteinCertificate.nonneg {p : ℚ[X]} {n : ℕ} {b : Fin (n + 1) → ℚ}
    (h : BernsteinCertificate p n b) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ realEval p x := by
  rw [h.identity, realEval_expansion]
  exact bernstein_sum_nonneg n (fun i => (b i : ℝ)) (fun i => by exact_mod_cast h.nonnegative i) hx0 hx1

theorem bernstein_certificate_bounds {p : ℚ[X]} {n : ℕ} {b : Fin (n + 1) → ℚ}
    (hid : p = bernsteinExpansion n b) {lo hi : ℚ}
    (hb : ∀ i, lo ≤ b i ∧ b i ≤ hi) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (lo : ℝ) ≤ realEval p x ∧ realEval p x ≤ (hi : ℝ) := by
  rw [hid, realEval_expansion]
  apply bernstein_sum_bounds n (fun i => (b i : ℝ))
  · intro i
    constructor
    · exact_mod_cast (hb i).1
    · exact_mod_cast (hb i).2
  · exact hx.1
  · exact hx.2

theorem realEval_rat (p : ℚ[X]) (x : ℚ) : realEval p (x : ℝ) = ((p.eval x : ℚ) : ℝ) := by
  exact Polynomial.eval₂_at_apply (p := p) (Rat.castHom ℝ) x

def affine (a width : ℚ) : ℚ[X] := C a + C width * X

theorem affine_coordinate {a width x : ℝ} (hw : 0 < width)
    (hx : x ∈ Icc a (a + width)) : (x - a) / width ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr hx.1) hw.le
  · apply (div_le_iff₀ hw).2
    linarith [hx.2]

theorem realEval_affine_comp (p : ℚ[X]) (a width : ℚ) (x : ℝ)
    (hw : width ≠ 0) :
    realEval (p.comp (affine a width)) ((x - a) / width) = realEval p x := by
  have hw' : (width : ℝ) ≠ 0 := by exact_mod_cast hw
  simp only [realEval, Polynomial.eval₂_comp, affine, Polynomial.eval₂_add,
    Polynomial.eval₂_C, Polynomial.eval₂_mul, Polynomial.eval₂_X, Rat.coe_castHom]
  congr 1
  field_simp <;> ring

theorem BernsteinCertificate.nonneg_interval {p : ℚ[X]} {n : ℕ}
    {b : Fin (n + 1) → ℚ} {a width : ℚ}
    (h : BernsteinCertificate (p.comp (affine a width)) n b) (hw : 0 < width)
    {x : ℝ} (hx : x ∈ Icc (a : ℝ) ((a : ℝ) + width)) : 0 ≤ realEval p x := by
  have hw' : (0 : ℝ) < width := by exact_mod_cast hw
  have hc := affine_coordinate hw' hx
  rw [← realEval_affine_comp p a width x (ne_of_gt hw)]
  exact h.nonneg hc.1 hc.2

/-- Evaluation of a rational bivariate polynomial, inner variable first. -/
def realEval₂ (p : Polynomial (Polynomial ℚ)) (x y : ℝ) : ℝ :=
  p.eval₂ (Polynomial.eval₂RingHom (Rat.castHom ℝ) x) y

def tensorExpansion (n m : ℕ) (b : Fin (n + 1) → Fin (m + 1) → ℚ) :
    Polynomial (Polynomial ℚ) :=
  ∑ i, ∑ j, C (C (b i j) * bernsteinPolynomial ℚ n i) *
    bernsteinPolynomial (Polynomial ℚ) m j

structure TensorCertificate (p : Polynomial (Polynomial ℚ)) (n m : ℕ)
    (b : Fin (n + 1) → Fin (m + 1) → ℚ) : Prop where
  identity : p = tensorExpansion n m b
  nonnegative : ∀ i j, 0 ≤ b i j

theorem realEval₂_tensor (n m : ℕ) (b : Fin (n + 1) → Fin (m + 1) → ℚ) (x y : ℝ) :
    realEval₂ (tensorExpansion n m b) x y =
      ∑ i, ∑ j, (b i j : ℝ) * bernsteinWeight n i x * bernsteinWeight m j y := by
  simp [realEval₂, tensorExpansion, Polynomial.eval₂_finset_sum, Polynomial.eval₂_pow, Polynomial.eval₂_sub, bernsteinPolynomial, bernsteinWeight, mul_assoc]

theorem TensorCertificate.nonneg {p : Polynomial (Polynomial ℚ)} {n m : ℕ}
    {b : Fin (n + 1) → Fin (m + 1) → ℚ} (h : TensorCertificate p n m b)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ realEval₂ p x y := by
  rw [h.identity, realEval₂_tensor]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (by exact_mod_cast h.nonnegative i j)
      (bernsteinWeight_nonneg n i hx.1 hx.2)) (bernsteinWeight_nonneg m j hy.1 hy.2)

def tensorAffine (p : Polynomial (Polynomial ℚ)) (a width c height : ℚ) :
    Polynomial (Polynomial ℚ) :=
  (p.map (Polynomial.compRingHom (affine a width))).comp
    (C (C c) + C (C height) * X)

theorem realEval₂_affine (p : Polynomial (Polynomial ℚ)) (a width c height : ℚ)
    (x y : ℝ) :
    realEval₂ (tensorAffine p a width c height) x y =
      realEval₂ p ((a : ℝ) + width * x) ((c : ℝ) + height * y) := by
  have he : (Polynomial.eval₂RingHom (Rat.castHom ℝ) x).comp
      (Polynomial.compRingHom (affine a width)) =
        Polynomial.eval₂RingHom (Rat.castHom ℝ) ((a : ℝ) + width * x) := by
    ext q <;> simp [Polynomial.coe_eval₂RingHom, Polynomial.coe_compRingHom,
      RingHom.comp_apply, affine, Polynomial.eval₂_comp]
  simp only [realEval₂, tensorAffine, Polynomial.eval₂_comp, Polynomial.eval₂_add,
    Polynomial.eval₂_C, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_map]
  rw [he]
  simp [Polynomial.coe_eval₂RingHom]

theorem TensorCertificate.nonneg_rectangle {p : Polynomial (Polynomial ℚ)} {n m : ℕ}
    {b : Fin (n + 1) → Fin (m + 1) → ℚ} {a width c height : ℚ}
    (h : TensorCertificate (tensorAffine p a width c height) n m b)
    (hw : 0 < width) (hh : 0 < height) {x y : ℝ}
    (hx : x ∈ Icc (a : ℝ) ((a : ℝ) + width))
    (hy : y ∈ Icc (c : ℝ) ((c : ℝ) + height)) : 0 ≤ realEval₂ p x y := by
  have hw' : (0 : ℝ) < width := by exact_mod_cast hw
  have hh' : (0 : ℝ) < height := by exact_mod_cast hh
  have hc := h.nonneg (affine_coordinate hw' hx) (affine_coordinate hh' hy)
  rw [realEval₂_affine] at hc
  have ex : (a : ℝ) + width * ((x - a) / width) = x := by field_simp <;> ring
  have ey : (c : ℝ) + height * ((y - c) / height) = y := by field_simp <;> ring
  rwa [ex, ey] at hc

/-- Degree elevation may be checked as finitely many rational basis
identities. Positivity of the resulting coefficients is a Lean consequence. -/
theorem degree_elevation {n m : ℕ} (b : Fin (n + 1) → ℚ)
    (w : Fin (n + 1) → Fin (m + 1) → ℚ)
    (hid : ∀ (i : Fin (n + 1)), bernsteinPolynomial ℚ n i =
      ∑ j, C (w i j) * bernsteinPolynomial ℚ m j)
    (hb : ∀ i, 0 ≤ b i) (hw : ∀ i j, 0 ≤ w i j) :
    BernsteinCertificate (bernsteinExpansion n b) m (fun j => ∑ i, b i * w i j) := by
  constructor
  · unfold bernsteinExpansion
    simp_rw [hid, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [← mul_assoc, ← Polynomial.C_mul]
    rw [← Finset.sum_mul, ← map_sum]
  · intro j
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hb i) (hw i j)

/-- A closed interval subdivision retains all boundary points. -/
inductive IntervalTree : ℚ → ℚ → Type where
  | leaf (a b : ℚ) : IntervalTree a b
  | split {a b : ℚ} (c : ℚ) (hac : a ≤ c) (hcb : c ≤ b)
      (left : IntervalTree a c) (right : IntervalTree c b) : IntervalTree a b

def IntervalTree.leaves {a b : ℚ} : IntervalTree a b → List (ℚ × ℚ)
  | .leaf a b => [(a, b)]
  | .split _ _ _ left right => left.leaves ++ right.leaves

theorem IntervalTree.covers {a b : ℚ} (tree : IntervalTree a b) {x : ℝ}
    (hx : x ∈ Icc (a : ℝ) (b : ℝ)) :
    ∃ cell ∈ tree.leaves, x ∈ Icc (cell.1 : ℝ) (cell.2 : ℝ) := by
  induction tree with
  | leaf a b => exact ⟨(a,b), by simp [IntervalTree.leaves], hx⟩
  | @split a b c hac hcb left right ihl ihr =>
    by_cases hxc : x ≤ (c : ℝ)
    · obtain ⟨cell, hc, h⟩ := ihl ⟨hx.1, hxc⟩
      exact ⟨cell, by simp [IntervalTree.leaves, hc], h⟩
    · obtain ⟨cell, hc, h⟩ := ihr ⟨(lt_of_not_ge hxc).le, hx.2⟩
      exact ⟨cell, by simp [IntervalTree.leaves, hc], h⟩

theorem IntervalTree.transfer {a b : ℚ} (tree : IntervalTree a b) (P : ℝ → Prop)
    (hleaf : ∀ cell ∈ tree.leaves, ∀ x ∈ Icc (cell.1 : ℝ) (cell.2 : ℝ), P x)
    {x : ℝ} (hx : x ∈ Icc (a : ℝ) (b : ℝ)) : P x := by
  obtain ⟨cell, hc, hxc⟩ := tree.covers hx
  exact hleaf cell hc x hxc

inductive BinaryTree where
  | leaf
  | split (left right : BinaryTree)

def BinaryTree.leaves : BinaryTree → ℚ → ℚ → List (ℚ × ℚ)
  | .leaf, a, b => [(a,b)]
  | .split left right, a, b =>
    left.leaves a ((a+b)/2) ++ right.leaves ((a+b)/2) b

theorem BinaryTree.covers (tree : BinaryTree) (a b : ℚ) {x : ℝ}
    (hx : x ∈ Icc (a : ℝ) (b : ℝ)) :
    ∃ cell ∈ tree.leaves a b, x ∈ Icc (cell.1 : ℝ) (cell.2 : ℝ) := by
  induction tree generalizing a b with
  | leaf => exact ⟨(a,b), by simp [BinaryTree.leaves], hx⟩
  | split left right il ir =>
    by_cases hm : x ≤ ((a+b)/2 : ℚ)
    · obtain ⟨cell, hc, hxc⟩ := il a ((a+b)/2) ⟨hx.1,hm⟩
      exact ⟨cell, by simp [BinaryTree.leaves,hc], hxc⟩
    · obtain ⟨cell, hc, hxc⟩ := ir ((a+b)/2) b ⟨(lt_of_not_ge hm).le,hx.2⟩
      exact ⟨cell, by simp [BinaryTree.leaves,hc], hxc⟩

def bernsteinCoefficients (p : ℚ[X]) (n : ℕ) (i : Fin (n + 1)) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), p.coeff k * ((i.val.choose k : ℚ) / n.choose k)

theorem clipping_iff {a b c d x : ℝ} :
    x ∈ Icc (max a c) (min b d) ↔ x ∈ Icc a b ∧ x ∈ Icc c d := by
  simp only [mem_Icc, max_le_iff, le_min_iff]
  tauto

theorem degenerate_interval {a x : ℝ} (hx : x ∈ Icc a a) : x = a :=
  le_antisymm hx.2 hx.1

/-- Degenerate leaves are checked at their sole rational endpoint. -/
def IntervalCertificate (p : ℚ[X]) (a b : ℚ) (n : ℕ) (coeff : Fin (n + 1) → ℚ) : Prop :=
  (a = b ∧ 0 ≤ p.eval a) ∨
    (a < b ∧ BernsteinCertificate (p.comp (affine a (b - a))) n coeff)

theorem IntervalCertificate.nonneg {p : ℚ[X]} {a b : ℚ} {n : ℕ}
    {coeff : Fin (n + 1) → ℚ} (h : IntervalCertificate p a b n coeff)
    {x : ℝ} (hx : x ∈ Icc (a : ℝ) (b : ℝ)) : 0 ≤ realEval p x := by
  rcases h with ⟨rfl, ha⟩ | ⟨hab, hc⟩
  · rw [degenerate_interval hx, realEval_rat]
    exact_mod_cast ha
  · apply hc.nonneg_interval (sub_pos.mpr hab)
    simpa only [Rat.cast_sub, add_sub_cancel] using hx

theorem rectangle_coverage {a b c d : ℚ} (xs : IntervalTree a b) (ys : IntervalTree c d)
    {x y : ℝ} (hx : x ∈ Icc (a : ℝ) (b : ℝ)) (hy : y ∈ Icc (c : ℝ) (d : ℝ)) :
    ∃ xc ∈ xs.leaves, ∃ yc ∈ ys.leaves,
      x ∈ Icc (xc.1 : ℝ) (xc.2 : ℝ) ∧ y ∈ Icc (yc.1 : ℝ) (yc.2 : ℝ) := by
  obtain ⟨xc, hxc, hxx⟩ := xs.covers hx
  obtain ⟨yc, hyc, hyy⟩ := ys.covers hy
  exact ⟨xc, hxc, yc, hyc, hxx, hyy⟩

structure RationalBox where
  left : ℚ
  right : ℚ
  bottom : ℚ
  top : ℚ

def RationalBox.contains (box : RationalBox) (x y : ℝ) : Prop :=
  x ∈ Icc (box.left : ℝ) (box.right : ℝ) ∧
    y ∈ Icc (box.bottom : ℝ) (box.top : ℝ)

theorem RationalBox.degenerate_left {box : RationalBox} (h : box.left = box.right)
    {x y : ℝ} (hxy : box.contains x y) : x = (box.left : ℝ) := by
  apply degenerate_interval
  simpa only [← h] using hxy.1

theorem RationalBox.degenerate_bottom {box : RationalBox} (h : box.bottom = box.top)
    {x y : ℝ} (hxy : box.contains x y) : y = (box.bottom : ℝ) := by
  apply degenerate_interval
  simpa only [← h] using hxy.2

/-- A zero-width rectangle is a one-variable problem, including its closed
endpoints. Thus normalization never divides by a zero width. -/
theorem RationalBox.transfer_degenerate_left {box : RationalBox} (h : box.left = box.right)
    (P : ℝ → ℝ → Prop)
    (hy : ∀ y ∈ Icc (box.bottom : ℝ) (box.top : ℝ), P box.left y)
    {x y : ℝ} (hxy : box.contains x y) : P x y := by
  rw [box.degenerate_left h hxy]
  exact hy y hxy.2

theorem RationalBox.transfer_degenerate_bottom {box : RationalBox} (h : box.bottom = box.top)
    (P : ℝ → ℝ → Prop)
    (hx : ∀ x ∈ Icc (box.left : ℝ) (box.right : ℝ), P x box.bottom)
    {x y : ℝ} (hxy : box.contains x y) : P x y := by
  rw [box.degenerate_bottom h hxy]
  exact hx x hxy.1

def RationalBox.child (box : RationalBox) (ix iy : Bool) : RationalBox :=
  let xm := (box.left + box.right) / 2
  let ym := (box.bottom + box.top) / 2
  ⟨if ix then xm else box.left, if ix then box.right else xm,
    if iy then ym else box.bottom, if iy then box.top else ym⟩

/-- A finite adaptive four-way subdivision; its shape is external data. -/
inductive QuadTree where
  | leaf
  | split (ll lh hl hh : QuadTree)

def QuadTree.leaves : QuadTree → RationalBox → List RationalBox
  | .leaf, box => [box]
  | .split ll lh hl hh, box =>
    ll.leaves (box.child false false) ++ lh.leaves (box.child false true) ++
      hl.leaves (box.child true false) ++ hh.leaves (box.child true true)

theorem QuadTree.covers (tree : QuadTree) (box : RationalBox) {x y : ℝ}
    (hxy : box.contains x y) :
    ∃ leaf ∈ tree.leaves box, leaf.contains x y := by
  induction tree generalizing box with
  | leaf => exact ⟨box, by simp [QuadTree.leaves], hxy⟩
  | split ll lh hl hh ill ilh ihl ihh =>
    have hxmid : ((box.left + box.right) / 2 : ℚ) = (box.left + box.right) / 2 := rfl
    by_cases hx : x ≤ ((box.left + box.right) / 2 : ℚ)
    · by_cases hy : y ≤ ((box.bottom + box.top) / 2 : ℚ)
      · obtain ⟨leaf, hm, hc⟩ := ill (box.child false false)
          ⟨⟨hxy.1.1,hx⟩,⟨hxy.2.1,hy⟩⟩
        exact ⟨leaf, by simp [QuadTree.leaves, hm], hc⟩
      · obtain ⟨leaf, hm, hc⟩ := ilh (box.child false true)
          ⟨⟨hxy.1.1,hx⟩,⟨(lt_of_not_ge hy).le,hxy.2.2⟩⟩
        exact ⟨leaf, by simp [QuadTree.leaves, hm], hc⟩
    · by_cases hy : y ≤ ((box.bottom + box.top) / 2 : ℚ)
      · obtain ⟨leaf, hm, hc⟩ := ihl (box.child true false)
          ⟨⟨(lt_of_not_ge hx).le,hxy.1.2⟩,⟨hxy.2.1,hy⟩⟩
        exact ⟨leaf, by simp [QuadTree.leaves, hm], hc⟩
      · obtain ⟨leaf, hm, hc⟩ := ihh (box.child true true)
          ⟨⟨(lt_of_not_ge hx).le,hxy.1.2⟩,⟨(lt_of_not_ge hy).le,hxy.2.2⟩⟩
        exact ⟨leaf, by simp [QuadTree.leaves, hm], hc⟩

/-- Tensor coefficient conversion is a finite rational computation. Its
polynomial identity is an explicit certificate field, never an oracle. -/
def tensorCoefficients (p : Polynomial (Polynomial ℚ)) (n m : ℕ)
    (i : Fin (n + 1)) (j : Fin (m + 1)) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
    (p.coeff l).coeff k * ((i.val.choose k : ℚ) / n.choose k) *
      ((j.val.choose l : ℚ) / m.choose l)

def BoxCertificate (p : Polynomial (Polynomial ℚ)) (n m : ℕ) (box : RationalBox) : Prop :=
  box.left < box.right ∧ box.bottom < box.top ∧
    let q := tensorAffine p box.left (box.right - box.left) box.bottom (box.top - box.bottom)
    TensorCertificate q n m (tensorCoefficients q n m)

theorem BoxCertificate.nonneg {p : Polynomial (Polynomial ℚ)} {n m : ℕ}
    {box : RationalBox} (h : BoxCertificate p n m box) {x y : ℝ}
    (hxy : box.contains x y) : 0 ≤ realEval₂ p x y := by
  apply h.2.2.nonneg_rectangle (sub_pos.mpr h.1) (sub_pos.mpr h.2.1)
  · simpa only [Rat.cast_sub, add_sub_cancel] using hxy.1
  · simpa only [Rat.cast_sub, add_sub_cancel] using hxy.2

theorem QuadTree.nonneg {p : Polynomial (Polynomial ℚ)} {n m : ℕ}
    (tree : QuadTree) (box : RationalBox)
    (hc : ∀ leaf ∈ tree.leaves box, BoxCertificate p n m leaf)
    {x y : ℝ} (hxy : box.contains x y) : 0 ≤ realEval₂ p x y := by
  obtain ⟨leaf, hm, hxy⟩ := tree.covers box hxy
  exact (hc leaf hm).nonneg hxy

/-- General finite-cell implication, with no restriction on the property
certified on each cell. This supports independently subdivided rectangles. -/
theorem finite_cover_transfer {ι : Type*} (cells : Finset ι) (domain : Set (ℝ × ℝ))
    (box : ι → Set (ℝ × ℝ)) (P : ℝ × ℝ → Prop)
    (hcover : domain ⊆ ⋃ i ∈ cells, box i)
    (hcell : ∀ i ∈ cells, ∀ z ∈ box i, P z) : ∀ z ∈ domain, P z := by
  intro z hz
  obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (hcover hz)
  exact hcell i hi z hzi

theorem polynomial_monotone {p : ℝ[X]} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, 0 ≤ p.derivative.eval x) : MonotoneOn p.eval (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b) p.continuous.continuousOn
    (fun _ _ => p.differentiableAt.differentiableWithinAt)
  intro x hx
  rw [interior_Icc] at hx
  simpa only [p.deriv] using hd x ⟨hx.1.le, hx.2.le⟩

theorem polynomial_strictMono {p : ℝ[X]} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, 0 < p.derivative.eval x) : StrictMonoOn p.eval (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) p.continuous.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  simpa only [p.deriv] using hd x ⟨hx.1.le, hx.2.le⟩

/-- The root-finding implication uses IVT and a proved derivative sign;
no numerical root finder is trusted as an analytic assertion. -/
theorem polynomial_unique_root {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (ha : p.eval a ≤ 0) (hb : 0 ≤ p.eval b)
    (hd : ∀ x ∈ Icc a b, 0 < p.derivative.eval x) :
    ∃! r, r ∈ Icc a b ∧ p.eval r = 0 := by
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc hab p.continuous.continuousOn ⟨ha, hb⟩
  refine ⟨r, ⟨hr, he⟩, ?_⟩
  intro s hs
  exact (polynomial_strictMono hd).injOn hs.1 hr (hs.2.trans he.symm)

/-- A critical-point argument only needs three monotonic pieces. This is
the printed lower-plateau minimum test, allowing the two roots to be isolated
by finite derivative certificates rather than trusting a root finder. -/
theorem three_piece_minimum {f : ℝ → ℝ} {a r s b floor : ℝ}
    (har : a ≤ r) (hrs : r ≤ s) (hsb : s ≤ b)
    (hfirst : MonotoneOn f (Icc a r)) (hmiddle : AntitoneOn f (Icc r s))
    (hlast : MonotoneOn f (Icc s b)) (ha : floor ≤ f a) (hs : floor ≤ f s)
    {x : ℝ} (hx : x ∈ Icc a b) : floor ≤ f x := by
  by_cases hxr : x ≤ r
  · exact ha.trans (hfirst ⟨le_rfl,har⟩ ⟨hx.1,hxr⟩ hx.1)
  · by_cases hxs : x ≤ s
    · exact hs.trans (hmiddle ⟨(lt_of_not_ge hxr).le,hxs⟩ ⟨hrs,le_rfl⟩ hxs)
    · exact hs.trans (hlast ⟨le_rfl,hsb⟩ ⟨(lt_of_not_ge hxs).le,hx.2⟩
        (lt_of_not_ge hxs).le)

theorem polynomial_bounds_interval {p : ℚ[X]} {n : ℕ} {b : Fin (n + 1) → ℚ}
    {a width lo hi : ℚ}
    (hid : p.comp (affine a width) = bernsteinExpansion n b)
    (hb : ∀ i, lo ≤ b i ∧ b i ≤ hi) (hw : 0 < width)
    {x : ℝ} (hx : x ∈ Icc (a : ℝ) ((a : ℝ) + width)) :
    (lo : ℝ) ≤ realEval p x ∧ realEval p x ≤ (hi : ℝ) := by
  have hc := affine_coordinate (by exact_mod_cast hw : (0 : ℝ) < width) hx
  have h := bernstein_certificate_bounds hid hb hc
  rwa [realEval_affine_comp p a width x (ne_of_gt hw)] at h

theorem rational_polynomial_unique_root {p : ℚ[X]} {a width ε : ℚ}
    {n : ℕ} {b : Fin (n + 1) → ℚ} (hw : 0 < width) (hε : 0 < ε)
    (hid : p.derivative.comp (affine a width) = bernsteinExpansion n b)
    (hb : ∀ i, ε ≤ b i ∧ b i ≤ b 0 + ∑ j, |b j|)
    (ha : p.eval a ≤ 0) (hc : 0 ≤ p.eval (a + width)) :
    ∃! r, r ∈ Icc (a : ℝ) ((a : ℝ) + width) ∧ realEval p r = 0 := by
  have hwidth : (0 : ℝ) < width := by exact_mod_cast hw
  have hr := polynomial_unique_root (p := p.map (Rat.castHom ℝ))
    (a := (a : ℝ)) (b := (a : ℝ) + width)
    (le_add_of_nonneg_right hwidth.le)
  have he (x : ℝ) : (p.map (Rat.castHom ℝ)).eval x = realEval p x := by
    simp [realEval, Polynomial.eval_map]
  simp_rw [← he]
  apply hr
  · rw [he, realEval_rat]
    exact_mod_cast ha
  · rw [he, ← Rat.cast_add, realEval_rat]
    exact_mod_cast hc
  · intro x hx
    have h := (polynomial_bounds_interval hid hb hw hx).1
    have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    have he' : (p.map (Rat.castHom ℝ)).derivative.eval x = realEval p.derivative x := by
      simp [realEval, Polynomial.derivative_map, Polynomial.eval_map]
    rw [he']
    exact hε'.trans_le h

end
end SingularValueBounds.KL.Certificates
