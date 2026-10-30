import SingularValueBounds.KL.Barrier.Norms

/-! # Norm bounds for the new upper comparison

The two normalized norm estimates in supplementary equation
`eq:app-up-comparison-norms`, and the concentrated-spectrum improvement.
The estimates concern the coefficient-two comparison, including the
one-dimensional zero case.
-/
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def normalizedUpperMean (x : ι → ℝ) : ℝ := ∑ i, x i ^ 3

def normalizedUpperEigenvalue (x : ι → ℝ) (i : ι) : ℝ :=
  x i + normalizedUpperMean x * x i ^ 2 - 2 * x i ^ 3

lemma normalized_upper_coordinate_le_one {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (h2 : ∑ i, x i ^ 2 = 1) (i : ι) : x i ≤ 1 := by
  have hs := Finset.single_le_sum (s := Finset.univ) (fun j _ => sq_nonneg (x j))
    (Finset.mem_univ i)
  rw [h2] at hs
  nlinarith [hx i]

lemma normalized_upper_mean_bounds {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (h2 : ∑ i, x i ^ 2 = 1) :
    0 ≤ normalizedUpperMean x ∧ normalizedUpperMean x ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun i _ => pow_nonneg (hx i) _), ?_⟩
  calc
    normalizedUpperMean x ≤ ∑ i, x i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [mul_le_mul_of_nonneg_left (normalized_upper_coordinate_le_one hx h2 i)
        (sq_nonneg (x i))]
    _ = 1 := h2

lemma upper_norm_polynomial_antitone :
    AntitoneOn (fun u : ℝ => 1 - 2 * u ^ 2 - u ^ 4 + 2 * u ^ 3) (Set.Icc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
  · fun_prop
  · fun_prop
  · intro u hu
    have hd : HasDerivAt (fun u : ℝ => 1 - 2 * u ^ 2 - u ^ 4 + 2 * u ^ 3)
        (-2 * u * (2 - 3 * u + 2 * u ^ 2)) u := by
      convert! ((hasDerivAt_const u (1 : ℝ)).sub
        ((hasDerivAt_id u).pow 2 |>.const_mul 2)).sub
          ((hasDerivAt_id u).pow 4) |>.add
            ((hasDerivAt_id u).pow 3 |>.const_mul 2) using 1 <;> simp only [id_eq] <;> ring
    rw [hd.deriv]
    have hu0 : 0 ≤ u := (interior_subset hu).1
    have hp : 0 ≤ 2 - 3 * u + 2 * u ^ 2 := by nlinarith [sq_nonneg (u - 3 / 4)]
    nlinarith [mul_nonneg hu0 hp]

/-- The norm-square estimate, proved by weighted Cauchy--Schwarz applied
rowwise to the nonnegative symmetric comparison matrix. -/
theorem normalized_upper_frobenius_bound {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (h2 : ∑ i, x i ^ 2 = 1) :
    (∑ i, normalizedUpperEigenvalue x i ^ 2) ≤
      1 - normalizedUpperMean x ^ 2 - normalizedUpperMean x ^ 2 * (1 - normalizedUpperMean x) ^ 2 := by
  let p := fun i => x i ^ 2
  let s2 := ∑ i, p i ^ 2
  let s3 := ∑ i, p i ^ 3
  let A := fun i j => (if i = j then 1 - 2 * p i else 0) + p i * p j
  have hp0 : ∀ i, 0 ≤ p i := fun i => sq_nonneg _
  have hp1 : ∀ i, p i ≤ 1 := by
    intro i
    have hs := Finset.single_le_sum (s := Finset.univ) (fun j _ => sq_nonneg (x j))
      (Finset.mem_univ i)
    simpa only [h2] using hs
  have hpSum : ∑ i, p i = 1 := h2
  have hA : ∀ i j, 0 ≤ A i j := by
    intro i j
    dsimp [A]
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      nlinarith [sq_nonneg (1 - p i)]
    · simp only [hij, ite_false, zero_add]
      exact mul_nonneg (hp0 i) (hp0 j)
  have hrow : ∀ i, (∑ j, A i j) = 1 - p i := by
    intro i
    dsimp [A]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hpSum]
    simp
    ring
  have hAx : ∀ i, (∑ j, A i j * x j) = normalizedUpperEigenvalue x i := by
    intro i
    dsimp [A]
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    simp only [mul_assoc]
    rw [← Finset.mul_sum]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hcube : (∑ j, p j * x j) = normalizedUpperMean x := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp [p, normalizedUpperMean]
      ring
    rw [hcube]
    dsimp [normalizedUpperEigenvalue, p]
    ring
  have hAp : ∀ i, (∑ j, A i j * p j) = (1 - 2 * p i) * p i + p i * s2 := by
    intro i
    dsimp [A]
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    simp only [mul_assoc]
    rw [← Finset.mul_sum]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcs : ∀ i, normalizedUpperEigenvalue x i ^ 2 ≤
      (1 - p i) * ((1 - 2 * p i) * p i + p i * s2) := by
    intro i
    have hc : (∑ j, A i j * x j) ^ 2 ≤
        (∑ j, A i j) * (∑ j, A i j * p j) := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
      · intro j _
        exact hA i j
      · intro j _
        exact mul_nonneg (hA i j) (hp0 j)
      · intro j _
        dsimp [p]
        ring
    simpa only [hrow, hAx, hAp] using hc
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcs i)
  have heq : (∑ i, (1 - p i) * ((1 - 2 * p i) * p i + p i * s2)) =
      1 - 2 * s2 - s2 ^ 2 + 2 * s3 := by
    calc
      _ = (∑ i, p i) - 3 * (∑ i, p i ^ 2) - (∑ i, p i ^ 2) * s2 +
          2 * (∑ i, p i ^ 3) + s2 * (∑ i, p i) := by
        simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [hpSum]; dsimp [s2, s3]; ring
  rw [heq] at hsum
  have hs20 : 0 ≤ s2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hs21 : s2 ≤ 1 := by
    calc
      s2 ≤ ∑ i, p i := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [hp0 i, hp1 i]
      _ = 1 := hpSum
  let u := Real.sqrt s2
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = s2 := Real.sq_sqrt hs20
  have hu1 : u ≤ 1 := by nlinarith
  have hpU : ∀ i, p i ≤ u := by
    intro i
    have hi := Finset.single_le_sum (s := Finset.univ) (fun j _ => sq_nonneg (p j))
      (Finset.mem_univ i)
    change p i ^ 2 ≤ s2 at hi
    nlinarith [hp0 i]
  have hs3 : s3 ≤ u ^ 3 := by
    have hs : s3 ≤ u * s2 := by
      calc
        s3 ≤ ∑ i, u * p i ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          nlinarith [mul_le_mul_of_nonneg_right (hpU i) (sq_nonneg (p i))]
        _ = u * s2 := by rw [← Finset.mul_sum]
    nlinarith
  have ha := normalized_upper_mean_bounds hx h2
  have hac : normalizedUpperMean x ^ 2 ≤ s2 := by
    have hc : (∑ i, x i * p i) ^ 2 ≤ (∑ i, x i ^ 2) * (∑ i, p i ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have he : (∑ i, x i * p i) = normalizedUpperMean x := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [p]
      ring
    rw [he, h2, one_mul] at hc
    exact hc
  have hau : normalizedUpperMean x ≤ u := by nlinarith
  have hmono := upper_norm_polynomial_antitone ⟨ha.1, ha.2⟩ ⟨hu0, hu1⟩ hau
  dsimp only at hmono
  have hu4 : u ^ 4 = s2 ^ 2 := by nlinarith [congrArg (fun a : ℝ => a ^ 2) hu2]
  nlinarith

private def goldenUpperPolynomial (r u : ℝ) : ℝ :=
  (47 + 29 * r) + (152 + 94 * r) * u + (354 + 248 * r) * u ^ 2 +
  (306 + 212 * r) * u ^ 3 + (300 + 175 * r) * u ^ 4 +
  (126 + 82 * r) * u ^ 5 + (111 + 67 * r) * u ^ 6 +
  (22 + 14 * r) * u ^ 7 + (18 + 11 * r) * u ^ 8

private lemma golden_upper_factor (u r : ℝ) (hr : r ^ 2 + r = 1) :
    125 * (((18 + 11 * r) / 125) * (1 + u ^ 2) ^ 5 - u ^ 2 * (1 + u) ^ 2) =
      (u - r) ^ 2 * goldenUpperPolynomial r u := by
  have hr2 : r ^ 2 = 1 - r := by linarith
  have hr3 : r ^ 3 = 2 * r - 1 := by
    nlinarith [congrArg (fun a : ℝ => a * r) hr2]
  unfold goldenUpperPolynomial
  ring_nf
  rw [hr3, hr2]
  ring

/-- The rational function majorizing a single normalized eigenvalue has the
stated strict rational bound. The maximum certificate is a polynomial square
factor with nonnegative coefficients, proved exactly in the kernel. -/
lemma upper_normalized_rational_max {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 * (1 + u) ^ 2 / (1 + u ^ 2) ^ 5 < (1241 : ℝ) / 6250 := by
  let r := (Real.sqrt 5 - 1) / 2
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have hr0 : 0 ≤ r := by dsimp [r]; nlinarith
  have hr : r ^ 2 + r = 1 := by dsimp [r]; nlinarith
  have hr1 : r < 31 / 50 := by dsimp [r]; nlinarith
  have hp : 0 ≤ goldenUpperPolynomial r u := by unfold goldenUpperPolynomial; positivity
  have hid := golden_upper_factor u r hr
  have hn := mul_nonneg (sq_nonneg (u - r)) hp
  have hden : 0 < (1 + u ^ 2) ^ 5 := by positivity
  have hb : u ^ 2 * (1 + u) ^ 2 / (1 + u ^ 2) ^ 5 ≤ (18 + 11 * r) / 125 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hid, hn]
  exact hb.trans_lt (by linarith)

/-- Isolate one coordinate in the normalized cube sum. -/
lemma normalized_upper_mean_le_complement {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (h2 : ∑ i, x i ^ 2 = 1) (i : ι) :
    normalizedUpperMean x ≤ x i ^ 3 + Real.sqrt (1 - x i ^ 2) ^ 3 := by
  let y := Real.sqrt (1 - x i ^ 2)
  let e := Finset.univ.erase i
  have hxi := normalized_upper_coordinate_le_one hx h2 i
  have hysq : y ^ 2 = 1 - x i ^ 2 := Real.sq_sqrt (by nlinarith [hx i])
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hrest : (∑ j ∈ e, x j ^ 2) = 1 - x i ^ 2 := by
    have he := Finset.sum_erase_add (Finset.univ : Finset ι) (fun j => x j ^ 2)
      (Finset.mem_univ i)
    change (∑ j ∈ e, x j ^ 2) + x i ^ 2 = ∑ j, x j ^ 2 at he
    linarith
  have hxy : ∀ j ∈ e, x j ≤ y := by
    intro j hj
    have hj2 := Finset.single_le_sum (s := e) (fun k _ => sq_nonneg (x k)) hj
    rw [hrest] at hj2
    nlinarith [hx j]
  have hrest3 : (∑ j ∈ e, x j ^ 3) ≤ y ^ 3 := by
    calc
      _ ≤ ∑ j ∈ e, y * x j ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        nlinarith [mul_le_mul_of_nonneg_right (hxy j hj) (sq_nonneg (x j))]
      _ = y * (1 - x i ^ 2) := by rw [← Finset.mul_sum, hrest]
      _ = y ^ 3 := by rw [← hysq]; ring
  have he := Finset.sum_erase_add (Finset.univ : Finset ι) (fun j => x j ^ 3)
    (Finset.mem_univ i)
  change (∑ j ∈ e, x j ^ 3) + x i ^ 3 = normalizedUpperMean x at he
  change normalizedUpperMean x ≤ x i ^ 3 + y ^ 3
  linarith

/-- The strict `223/500` bound for each normalized comparison eigenvalue. -/
theorem normalized_upper_eigenvalue_lt {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (h2 : ∑ i, x i ^ 2 = 1) (i : ι) :
    normalizedUpperEigenvalue x i < (223 : ℝ) / 500 := by
  let v := x i
  let y := Real.sqrt (1 - v ^ 2)
  have hv0 : 0 ≤ v := hx i
  have hv1 : v ≤ 1 := normalized_upper_coordinate_le_one hx h2 i
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hy2 : y ^ 2 = 1 - v ^ 2 := Real.sq_sqrt (by nlinarith)
  have ha := normalized_upper_mean_le_complement hx h2 i
  have hb : normalizedUpperEigenvalue x i ≤ v * y ^ 3 * (v + y) := by
    have hh := mul_le_mul_of_nonneg_right ha (sq_nonneg v)
    dsimp [normalizedUpperEigenvalue]
    change v + normalizedUpperMean x * v ^ 2 - 2 * v ^ 3 ≤ _
    have hid : v * y ^ 3 * (v + y) = v + v ^ 2 * (v ^ 3 + y ^ 3) - 2 * v ^ 3 := by
      nlinarith [congrArg (fun a : ℝ => a * v) hy2,
        congrArg (fun a : ℝ => a * v ^ 3) hy2,
        congrArg (fun a : ℝ => a * (v * y ^ 2)) hy2]
    rw [hid]
    nlinarith only [hh]
  by_cases hy : y = 0
  · rw [hy] at hb
    norm_num at hb ⊢
    linarith
  have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy)
  let u := v / y
  have hu : 0 ≤ u := div_nonneg hv0 hy0
  have hden : 1 + u ^ 2 = 1 / y ^ 2 := by
    dsimp [u]
    field_simp [hy]
    nlinarith
  have hid : (v * y ^ 3 * (v + y)) ^ 2 = u ^ 2 * (1 + u) ^ 2 / (1 + u ^ 2) ^ 5 := by
    rw [hden]
    dsimp [u]
    field_simp [hy]
    ring
  have hmax := upper_normalized_rational_max hu
  rw [← hid] at hmax
  have hf0 : 0 ≤ v * y ^ 3 * (v + y) := by positivity
  have hrat : (1241 : ℝ) / 6250 < ((223 : ℝ) / 500) ^ 2 := by norm_num
  nlinarith

/-- A large coordinate forces all normalized comparison eigenvalues below
`21/50`; a largest-coordinate hypothesis is unnecessary. -/
theorem normalized_upper_eigenvalue_le_of_concentrated {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (h2 : ∑ i, x i ^ 2 = 1)
    {k : ι} (hk : (37 : ℝ) / 40 ≤ x k) (i : ι) :
    normalizedUpperEigenvalue x i ≤ (21 : ℝ) / 50 := by
  have ha := (normalized_upper_mean_bounds hx h2).2
  have hb : normalizedUpperEigenvalue x i ≤ x i + x i ^ 2 - 2 * x i ^ 3 := by
    have hm := mul_le_mul_of_nonneg_right ha (sq_nonneg (x i))
    dsimp [normalizedUpperEigenvalue]
    linarith
  by_cases hik : i = k
  · subst i
    have h1 := normalized_upper_coordinate_le_one hx h2 k
    have hprod := mul_nonneg (sq_nonneg (1 - x k))
      (show 0 ≤ 2 * x k + 3 by linarith [hx k])
    nlinarith
  have hpair : x i ^ 2 + x k ^ 2 ≤ 1 := by
    have hki : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hik, Finset.mem_univ _⟩
    have hsingle := Finset.single_le_sum (s := Finset.univ.erase i)
      (fun j _ => sq_nonneg (x j)) hki
    have he := Finset.sum_erase_add (Finset.univ : Finset ι) (fun j => x j ^ 2)
      (Finset.mem_univ i)
    rw [h2] at he
    linarith
  have hsmall : x i ≤ (381 : ℝ) / 1000 := by nlinarith [hx i, hx k]
  have hsquare : x i ^ 2 ≤ ((381 : ℝ) / 1000) ^ 2 := by nlinarith [hx i]
  have hcross : x i * ((381 : ℝ) / 1000) ≤ ((381 : ℝ) / 1000) ^ 2 := by nlinarith
  have hbracket : 0 ≤ 1 + ((381 : ℝ) / 1000 + x i) -
      2 * (((381 : ℝ) / 1000) ^ 2 + ((381 : ℝ) / 1000) * x i + x i ^ 2) := by
    nlinarith [hx i]
  have hprod := mul_nonneg (sub_nonneg.mpr hsmall) hbracket
  nlinarith

end
end SingularValueBounds.KL
