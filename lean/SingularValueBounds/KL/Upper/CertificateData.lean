import SingularValueBounds.KL.Upper.CertificateTrees

/-! # Concrete finite polynomial conditions for P16 and P17

These conditions contain only finitely many identities and comparisons of
rational coefficients. Their exact inputs and all subdivision leaves are
checked by `check_polynomial_interface.py`. No real-variable estimate occurs
in either numerical condition. -/
open Polynomial
open scoped Polynomial BigOperators
namespace SingularValueBounds.KL.Certificates
noncomputable section

def ratePolynomial (v correction : ℚ) : ℚ[X] :=
  let V := C v * X
  let W := C 2 * X^2 + C v * X + C (2*v-2)
  let A := C (v-1) * (1+X)
  let D := W^2-V^2
  (C correction*A+V)*W^11*D - 2*A*
    ((∑ j ∈ Finset.range 6, C (1/(2*(j:ℚ)+1))*V^(2*j+1)*W^(10-2*j)*D) +
      C (1/13)*V^13)

def RateCertificateConditions : Prop :=
  ∀ i : Fin 15, ∀ cell ∈ (rateTrees i).leaves 0 ((rateRows i).1-1),
    IntervalCertificate (ratePolynomial (rateRows i).1 (rateRows i).2)
      cell.1 cell.2 27
      (bernsteinCoefficients
        ((ratePolynomial (rateRows i).1 (rateRows i).2).comp
          (affine cell.1 (cell.2-cell.1))) 27)

theorem rate_polynomial_nonneg (h : RateCertificateConditions) (i : Fin 15)
    {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) ((rateRows i).1-1)) :
    0 ≤ realEval (ratePolynomial (rateRows i).1 (rateRows i).2) y := by
  obtain ⟨cell, hm, hc⟩ := (rateTrees i).covers 0 ((rateRows i).1-1) (by simpa using hy)
  exact (h i cell hm).nonneg hc

def majorantBQ (i : Fin 6) : ℚ[X] :=
  match i.val with
  | 0 => C (13/6)
  | 1 => C (13/6)-C 4*(X-C (1/4))^2
  | 2 => C (13/5)
  | 3 => C (13/6)-C 4*(X-C (1/4))^2-C (1/30)
  | 4 => C (13/6)-C (1/40)
  | _ => let v := X-C (7/20)
         C (413/200)-C (1339/1000)*v-C (10009/1000)*v^2-C (25197/1000)*v^3

def majorantAQ (i : Fin 6) : ℚ[X] :=
  match i.val with
  | 0 => 1+C 9*X
  | 1 => C 20*X-C 2
  | 2 => C 24*X-C (22/3)
  | 3 => C 20*X-C 2
  | 4 => 1+C 9*X
  | _ => let v := X-C (7/20)
         C (816/125)+C (7307/200)*v+C (9971/100)*v^2+C (18903/250)*v^3

def comparisonZQ : Polynomial (Polynomial ℚ) :=
  2*(X+C X*X^2-2*X^3)

def padeDQ (z : Polynomial (Polynomial ℚ)) : Polynomial (Polynomial ℚ) :=
  1-C (C (16/7))*z+C (C (12/7))*z^2-C (C (16/35))*z^3+C (C (1/35))*z^4

def padeNQ (z : Polynomial (Polynomial ℚ)) : Polynomial (Polynomial ℚ) :=
  z-C (C (25/14))*z^2+C (C (19/21))*z^3-C (C (47/420))*z^4

def majorantHQ (i : Fin 6) : Polynomial (Polynomial ℚ) :=
  2*X+C (majorantBQ i)*X^2-C (majorantAQ i)*X^2*(X-C X)

def majorantCleared (i : Fin 6) : Polynomial (Polynomial ℚ) :=
  majorantHQ i * padeDQ comparisonZQ - padeNQ comparisonZQ

def majorantQuotient (i : Fin 6) : Polynomial (Polynomial ℚ) :=
  (majorantCleared i).divX.divX

def MajorantCertificateConditions : Prop :=
  ∀ i : Fin 6,
    majorantCleared i = X^2 * majorantQuotient i ∧
    ∀ leaf ∈ (majorantTrees i).leaves (majorantBoxes i),
      BoxCertificate (majorantQuotient i) (majorantDegrees i).1 (majorantDegrees i).2 leaf

theorem majorant_quotient_nonneg (h : MajorantCertificateConditions) (i : Fin 6)
    {a x : ℝ} (hax : (majorantBoxes i).contains a x) :
    0 ≤ realEval₂ (majorantQuotient i) a x :=
  (majorantTrees i).nonneg (majorantBoxes i) (h i).2 hax

theorem majorant_cleared_nonneg (h : MajorantCertificateConditions) (i : Fin 6)
    {a x : ℝ} (hax : (majorantBoxes i).contains a x) :
    0 ≤ realEval₂ (majorantCleared i) a x := by
  rw [(h i).1]
  change 0 ≤ (X^2*majorantQuotient i).eval₂
    (Polynomial.eval₂RingHom (Rat.castHom ℝ) a) x
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  exact mul_nonneg (sq_nonneg x) (majorant_quotient_nonneg h i hax)

end
end SingularValueBounds.KL.Certificates
