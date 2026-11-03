import SingularValueBounds.KL.Upper.GeneralMeanNumericalData
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! Exact integer evaluation of the rational resolvents in general entropy nodes.
The original rational functions remain the specifications. Clearing powers of
the positive canonical denominator leaves integer polynomials and one final
rational division. Polynomial identities bound the final common divisors by 4
and 72, so normalization uses gcds with those fixed constants. The public
identities hold for every rational input, including
zero denominators of the resolvent itself under Lean's usual division convention.
-/

namespace SingularValueBounds.KL.Certificates

private theorem resolventUpperQ_fraction (n d : ℚ) (hd : d ≠ 0) :
    resolventUpperQ (n/d) =
      (n^3*d+11*n^2*d^2+26*n*d^3+6*d^4) /
        (n*(n^3+12*n^2*d+36*n*d^2+24*d^3)) := by
  unfold resolventUpperQ
  have hnum : (n/d)^3+11*(n/d)^2+26*(n/d)+6 =
      (n^3+11*n^2*d+26*n*d^2+6*d^3)/d^3 := by
    field_simp [hd]
  have hden : (n/d)*((n/d)^3+12*(n/d)^2+36*(n/d)+24) =
      (n*(n^3+12*n^2*d+36*n*d^2+24*d^3))/d^4 := by
    field_simp [hd]
  rw [hnum,hden]
  by_cases h : n*(n^3+12*n^2*d+36*n*d^2+24*d^3) = 0
  · simp only [h, zero_div, div_zero]
  · field_simp [hd,h]

private theorem resolventLowerQ_fraction (n d : ℚ) (hd : d ≠ 0) :
    resolventLowerQ (n/d) =
      (n^2*d+8*n*d^2+11*d^3)/(n^3+9*n^2*d+18*n*d^2+6*d^3) := by
  unfold resolventLowerQ
  have hnum : (n/d)^2+8*(n/d)+11 = (n^2+8*n*d+11*d^2)/d^2 := by
    field_simp [hd]
  have hden : (n/d)^3+9*(n/d)^2+18*(n/d)+6 =
      (n^3+9*n^2*d+18*n*d^2+6*d^3)/d^3 := by
    field_simp [hd]
  rw [hnum,hden]
  by_cases h : n^3+9*n^2*d+18*n*d^2+6*d^3 = 0
  · simp only [h, zero_div, div_zero]
  · field_simp [hd,h]

/-- A polynomial identity and coprimality cancel the canonical denominator. -/
private theorem lower_gcd_dvd (n d : ℤ) (h : IsCoprime n d) :
    Int.gcd (n^2*d+8*n*d^2+11*d^3) (n^3+9*n^2*d+18*n*d^2+6*d^3) ∣ 4 := by
  let N := n^2*d+8*n*d^2+11*d^3
  let E := n^3+9*n^2*d+18*n*d^2+6*d^3
  let g : ℤ := Int.gcd N E
  have hN : g ∣ N := Int.gcd_dvd_left N E
  have hE : g ∣ E := Int.gcd_dvd_right N E
  have hEd : IsCoprime E d := by
    convert (h.pow_left (m:=3)).add_mul_left_left (9*n^2+18*n*d+6*d^2) using 1 <;> (try dsimp [E]) <;> first | rfl | ring
  have hgd := hEd.of_isCoprime_of_dvd_left hE
  have hbez : g ∣ 4*d^5 := by
    have h1 := dvd_mul_of_dvd_right hN (n^2+4*n*d+2*d^2)
    have h2 := dvd_mul_of_dvd_right hE (d*(n+3*d))
    convert dvd_sub h1 h2 using 1 <;> (try dsimp [N,E]) <;> first | rfl | ring
  have h4 : g ∣ (4:ℤ) := (hgd.pow_right (n:=5)).dvd_of_dvd_mul_right hbez
  dsimp [g, N, E] at h4
  exact_mod_cast h4

/-- The upper fraction has a uniform common-divisor bound as well. -/
private theorem upper_gcd_dvd (n d : ℤ) (h : IsCoprime n d) :
    Int.gcd (n^3*d+11*n^2*d^2+26*n*d^3+6*d^4)
      (n*(n^3+12*n^2*d+36*n*d^2+24*d^3)) ∣ 72 := by
  let N := n^3*d+11*n^2*d^2+26*n*d^3+6*d^4
  let E := n*(n^3+12*n^2*d+36*n*d^2+24*d^3)
  let P := n^2+5*n*d+2*d^2
  let Q := n^2+6*n*d+6*d^2
  let H := d*(n^2+11*n*d+26*d^2)
  let g : ℤ := Int.gcd N E
  have hN : g ∣ N := Int.gcd_dvd_left N E
  have hE : g ∣ E := Int.gcd_dvd_right N E
  have hEd : IsCoprime E d := by
    convert (h.pow_left (m:=4)).add_mul_left_left (12*n^3+36*n^2*d+24*n*d^2) using 1 <;> (try dsimp [E]) <;> first | rfl | ring
  have hgd := hEd.of_isCoprime_of_dvd_left hE
  have hbez : g ∣ 72*d^10 := by
    have h1 := dvd_mul_of_dvd_right hN (12*d^6+n*Q*H)
    have h2 := dvd_mul_of_dvd_right hE (d*P*H)
    convert dvd_sub h1 h2 using 1 <;> (try dsimp [N,E,P,Q,H]) <;> first | rfl | ring
  have h72 : g ∣ (72:ℤ) := (hgd.pow_right (n:=10)).dvd_of_dvd_mul_right hbez
  dsimp [g, N, E] at h72
  exact_mod_cast h72

private noncomputable def resolventNormalizeBound (num : ℤ) (den : ℕ) (den_nz : den ≠ 0)
    (bound : ℕ) (h : num.natAbs.gcd den ∣ bound) : ℚ :=
  let g := (num.natAbs.gcd bound).gcd den
  have hg : g = num.natAbs.gcd den := by
    dsimp [g]
    rw [Nat.gcd_comm num.natAbs bound, Nat.gcd_assoc, Nat.gcd_eq_right h]
  Rat.maybeNormalize num den g (Rat.normalize.dvd_num hg) (Rat.normalize.dvd_den hg)
    (Rat.normalize.den_nz den_nz hg) (Rat.normalize.reduced den_nz hg)

private theorem resolventNormalizeBound_eq (num : ℤ) (den : ℕ) (den_nz : den ≠ 0)
    (bound : ℕ) (h : num.natAbs.gcd den ∣ bound) :
    resolventNormalizeBound num den den_nz bound h = Rat.normalize num den den_nz := by
  have hg : (num.natAbs.gcd bound).gcd den = num.natAbs.gcd den := by
    rw [Nat.gcd_comm num.natAbs bound, Nat.gcd_assoc, Nat.gcd_eq_right h]
  simp only [resolventNormalizeBound, hg, Rat.normalize]

private noncomputable def resolventDivideBound (num den : ℤ) (bound : ℕ)
    (h : Int.gcd num den ∣ bound) : ℚ :=
  match den with
  | .ofNat d =>
    if hd : d = 0 then 0
    else resolventNormalizeBound num d hd bound (by exact h)
  | .negSucc d =>
    resolventNormalizeBound (-num) (d+1) (by omega) bound (by simpa only [Int.gcd_def, Int.natAbs_neg, Int.natAbs_negSucc] using h)

private theorem resolventDivideBound_eq (num den : ℤ) (bound : ℕ)
    (h : Int.gcd num den ∣ bound) : resolventDivideBound num den bound h = Rat.divInt num den := by
  cases den with
  | ofNat d =>
    by_cases hd : d = 0
    · simp [resolventDivideBound, hd]
    · simp only [resolventDivideBound, hd, ↓reduceDIte, Rat.divInt, mkRat]
      exact resolventNormalizeBound_eq num d hd bound h
  | negSucc d =>
    simp only [resolventDivideBound, resolventNormalizeBound_eq, Rat.divInt]

noncomputable def integerResolventUpper : ℚ → ℚ
  | .mk' n d hd hr =>
    let di : ℤ := d
    resolventDivideBound (n^3*di+11*n^2*di^2+26*n*di^3+6*di^4)
      (n*(n^3+12*n^2*di+36*n*di^2+24*di^3)) 72
      (upper_gcd_dvd n di (Rat.isCoprime_num_den (Rat.mk' n d hd hr)))

noncomputable def integerResolventLower : ℚ → ℚ
  | .mk' n d hd hr =>
    let di : ℤ := d
    resolventDivideBound (n^2*di+8*n*di^2+11*di^3)
      (n^3+9*n^2*di+18*n*di^2+6*di^3) 4
      (lower_gcd_dvd n di (Rat.isCoprime_num_den (Rat.mk' n d hd hr)))

theorem resolventUpperQ_eq_integer (x : ℚ) :
    resolventUpperQ x = integerResolventUpper x := by
  cases x using Rat.rec with
  | mk' n d hd hr =>
    simp only [integerResolventUpper, resolventDivideBound_eq, Rat.divInt_eq_div]
    push_cast
    have hd' : (d:ℚ) ≠ 0 := by exact_mod_cast hd
    have hx : (n:ℚ)/(d:ℚ) = Rat.mk' n d hd hr := Rat.num_div_den (Rat.mk' n d hd hr)
    rw [← hx]
    exact resolventUpperQ_fraction (n:ℚ) (d:ℚ) hd'

theorem resolventLowerQ_eq_integer (x : ℚ) :
    resolventLowerQ x = integerResolventLower x := by
  cases x using Rat.rec with
  | mk' n d hd hr =>
    simp only [integerResolventLower, resolventDivideBound_eq, Rat.divInt_eq_div]
    push_cast
    have hd' : (d:ℚ) ≠ 0 := by exact_mod_cast hd
    have hx : (n:ℚ)/(d:ℚ) = Rat.mk' n d hd hr := Rat.num_div_den (Rat.mk' n d hd hr)
    rw [← hx]
    exact resolventLowerQ_fraction (n:ℚ) (d:ℚ) hd'

end SingularValueBounds.KL.Certificates
