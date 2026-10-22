import SingularValueBounds.KL.Lower.CertificateTrees
import SingularValueBounds.KL.Certificates.Enclosures
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Finite Taylor/Bernstein implications for the three concentrated lower
scalar determinant inequalities. All arithmetic premises are rational and finite.
The proof bounds the same scalar functions as the printed critical-point proof. -/
open scoped Polynomial BigOperators
open Polynomial Set
namespace SingularValueBounds.KL.LowerCertificates
open SingularValueBounds.KL.Certificates
noncomputable section
set_option maxHeartbeats 1000000

def plateauD (u A c : ℚ) : ℚ[X] := 1-C u*(X+C A*X^2-C c*X^3)
def plateauPsi (u v w : ℚ) : ℚ[X] := C u*X+C (2*v)*X^2-C (2*w)*X^4
def polynomialExpTaylor (N : ℕ) (p : ℚ[X]) : ℚ[X] :=
  ∑ j ∈ Finset.range (N+1), C ((Nat.factorial j:ℚ)⁻¹)*p^j

def plateauQ (u A v w c : ℚ) : ℚ[X] :=
  (plateauD u A c*polynomialExpTaylor 24 (plateauPsi u v w)-1).divX.divX

structure PlateauScalarCertificate (u A v w c stop : ℚ) (qt dt : BinaryTree) : Prop where
  u_pos : 0 < u
  w_nonneg : 0 ≤ w
  w_le_v : w ≤ v
  stop_pos : 0 < stop
  stop_le : stop ≤ 1
  factorization : X^2*plateauQ u A v w c =
    plateauD u A c*polynomialExpTaylor 24 (plateauPsi u v w)-1
  q_cells : ∀ cell ∈ qt.leaves 0 stop,
    IntervalCertificate (plateauQ u A v w c) cell.1 cell.2 97
      (bernsteinCoefficients ((plateauQ u A v w c).comp (affine cell.1 (cell.2-cell.1))) 97)
  d_cells : ∀ cell ∈ dt.leaves 0 stop,
    IntervalCertificate (plateauD u A c-C (1/1000000)) cell.1 cell.2 3
      (bernsteinCoefficients ((plateauD u A c-C (1/1000000)).comp (affine cell.1 (cell.2-cell.1))) 3)

theorem polynomialExpTaylor_eval (N : ℕ) (p : ℚ[X]) (r : ℝ) :
    realEval (polynomialExpTaylor N p) r = expTaylor N (realEval p r) := by
  simp [polynomialExpTaylor,expTaylor,realEval,Polynomial.eval₂_finset_sum,Polynomial.eval₂_mul,
    Polynomial.eval₂_C,Polynomial.eval₂_pow,div_eq_mul_inv,mul_comm]

theorem PlateauScalarCertificate.scalar {u A v w c stop : ℚ} {qt dt : BinaryTree}
    (h : PlateauScalarCertificate u A v w c stop qt dt) {r : ℝ}
    (hr : r ∈ Icc (0:ℝ) (stop:ℝ)) :
    0 < 1-(u:ℝ)*(r+(A:ℝ)*r^2-(c:ℝ)*r^3) ∧
    0 ≤ (u:ℝ)*r+2*(v:ℝ)*r^2-2*(w:ℝ)*r^4+
      Real.log (1-(u:ℝ)*(r+(A:ℝ)*r^2-(c:ℝ)*r^3)) := by
  have hdcell := dt.covers 0 stop (by simpa using hr)
  obtain ⟨dc,hdc,hrd⟩ := hdcell
  have hd := (h.d_cells dc hdc).nonneg hrd
  have hqcell := qt.covers 0 stop (by simpa using hr)
  obtain ⟨qc,hqc,hrq⟩ := hqcell
  have hq := (h.q_cells qc hqc).nonneg hrq
  have hde : realEval (plateauD u A c) r =
      1-(u:ℝ)*(r+(A:ℝ)*r^2-(c:ℝ)*r^3) := by
    simp [plateauD,realEval,Polynomial.eval₂_sub,Polynomial.eval₂_add,
      Polynomial.eval₂_mul,Polynomial.eval₂_pow]
  have hpe : realEval (plateauPsi u v w) r = (u:ℝ)*r+2*(v:ℝ)*r^2-2*(w:ℝ)*r^4 := by
    simp [plateauPsi,realEval,Polynomial.eval₂_sub,Polynomial.eval₂_add,
      Polynomial.eval₂_mul,Polynomial.eval₂_pow]
  have hdpos : 0 < realEval (plateauD u A c) r := by
    have hdc' : realEval (plateauD u A c-C (1/1000000)) r =
        realEval (plateauD u A c) r-1/1000000 := by
      simp [realEval,Polynomial.eval₂_sub]
    rw [hdc'] at hd
    linarith
  have hfactor := congrArg (fun p : ℚ[X] => realEval p r) h.factorization
  simp only [realEval,Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_X,
    Polynomial.eval₂_sub,Polynomial.eval₂_one] at hfactor
  change r^2*realEval (plateauQ u A v w c) r =
    realEval (plateauD u A c) r*realEval (polynomialExpTaylor 24 (plateauPsi u v w)) r-1 at hfactor
  rw [polynomialExpTaylor_eval] at hfactor
  have hpsi : 0 ≤ realEval (plateauPsi u v w) r := by
    rw [hpe]
    have hu : (0:ℝ) < u := by exact_mod_cast h.u_pos
    have hw : (0:ℝ) ≤ w := by exact_mod_cast h.w_nonneg
    have hv : (w:ℝ) ≤ v := by exact_mod_cast h.w_le_v
    have hr1 : r ≤ 1 := hr.2.trans (by exact_mod_cast h.stop_le)
    have hr2 : r^2 ≤ 1 := by nlinarith [hr.1]
    have hvr : 0 ≤ (v:ℝ)-(w:ℝ)*r^2 := by nlinarith [mul_le_mul_of_nonneg_left hr2 hw]
    nlinarith [mul_nonneg hr.1 hu.le,mul_nonneg (sq_nonneg r) hvr]
  have ht := expTaylor_le_exp 24 hpsi
  have hexp : 1 ≤ realEval (plateauD u A c) r*Real.exp (realEval (plateauPsi u v w) r) := by
    nlinarith [mul_nonneg (sq_nonneg r) hq,
      mul_le_mul_of_nonneg_left ht hdpos.le]
  have hl := Real.log_le_log (by norm_num : (0:ℝ) < 1) hexp
  rw [Real.log_one,Real.log_mul hdpos.ne' (Real.exp_ne_zero _),Real.log_exp] at hl
  rw [hde] at hdpos hl
  rw [hpe] at hl
  exact ⟨hdpos,by linarith⟩

theorem scalar_log_interpolation {d0 d1 p0 p1 a b : ℝ}
    (hd0 : 0 < d0) (hd1 : 0 < d1) (h0 : 0 ≤ p0+Real.log d0)
    (h1 : 0 ≤ p1+Real.log d1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    0 < a*d0+b*d1 ∧ 0 ≤ a*p0+b*p1+Real.log (a*d0+b*d1) := by
  have hd : 0 < a*d0+b*d1  := by
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0,hb1] using hd1
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hd0)
        (mul_nonneg hb hd1.le)
  have hl := strictConcaveOn_log_Ioi.concaveOn.2 hd0 hd1 ha hb hab
  simp only [smul_eq_mul] at hl
  exact ⟨hd,by nlinarith⟩

def PlateauCertificateConditions : Prop :=
  PlateauScalarCertificate (1207/1000) (6/5) (1631/1000) (26/25) (17/10) (147/200)
    plateauQTree0 plateauDTree0 ∧
  PlateauScalarCertificate (1207/1000) (1211/1000) (167/100) (26/25) (17/10) (147/200)
    plateauQTree1 plateauDTree1 ∧
  PlateauScalarCertificate (6/5) (74/55) (27/16) (21/20) (19/10) 1
    plateauQTree2 plateauDTree2

end
end SingularValueBounds.KL.LowerCertificates
