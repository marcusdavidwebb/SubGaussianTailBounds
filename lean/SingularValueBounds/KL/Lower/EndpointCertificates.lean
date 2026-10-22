import SingularValueBounds.KL.Lower.EndpointMixed
import SingularValueBounds.KL.Certificates.Polynomial

/-! # Finite rational endpoint lower-cost certificates

These are the two rows and four rectangles per row of supplementary S1.5.
The conditions contain only rational polynomial identities and signs.
-/

open Polynomial
open scoped Polynomial BigOperators
namespace SingularValueBounds.KL.Certificates
noncomputable section

def endpointTheta (i : Fin 2) : ℚ := if i = 0 then 9/20 else 1/4
def endpointXi (_ : Fin 2) : ℚ := 8/5
def endpointChi (i : Fin 2) : ℚ := if i = 0 then 2 else 12/5
def endpointOmega (i : Fin 2) : ℚ := if i = 0 then 3/10 else 9/20
def endpointKLo (i : Fin 2) : ℚ := if i = 0 then 73/100 else 3/4
def endpointKHi (i : Fin 2) : ℚ := if i = 0 then 3/4 else 7/9

def endpointAPoly (i : Fin 2) : ℚ[X] :=
  C (endpointTheta i)*X+C ((1-endpointTheta i)*(73/55))
def endpointC (i : Fin 2) : ℚ := endpointTheta i+(1-endpointTheta i)*(103/55)

def endpointGPoly (i : Fin 2) : Polynomial (Polynomial ℚ) :=
  let A := endpointAPoly i
  let c := endpointC i
  let ξ := endpointXi i
  C (C (1/ξ)*A+C (1-c))*X +
    C (A+C (ξ/2)+C (1/(2*ξ))*(A^2-C (2*c)))*X^2 -
    C (C c+C (c/ξ)*A)*X^3+C (C (c^2/(2*ξ)))*X^4

def endpointNPoly (i : Fin 2) : Polynomial (Polynomial ℚ) :=
  let A := endpointAPoly i
  let c := endpointC i
  let χ := endpointChi i
  C (C (2/χ)*A-C c)*X +
    C (C χ+C (1/χ)*(A^2-C (2*c)))*X^2 -
    C (C (2*c/χ)*A)*X^3+C (C (c^2/χ))*X^4

def endpointOPoly (i : Fin 2) : Polynomial (Polynomial ℚ) :=
  C (endpointAPoly i+C (1/(2*endpointXi i))+X^2*(endpointGPoly i).eval X) +
    C (1-X^2)*endpointGPoly i

def endpointNMajorantPoly (i : Fin 2) : Polynomial (Polynomial ℚ) :=
  let A := endpointAPoly i
  let c := endpointC i
  let d := X*(1+A*X-C c*X^2)
  C (A-C c*X^3+2*X^2*d+C (1/endpointChi i)*(1-X^2)) +
    C (1-X^2)*endpointNPoly i

def endpointMarginPoly (i : Fin 2) : Polynomial (Polynomial ℚ) :=
  C (C (73/50))-C (C (endpointOmega i))*endpointOPoly i -
    C (C (1-endpointOmega i))*endpointNMajorantPoly i

def endpointBox (i : Fin 2) (j : Fin 4) : RationalBox :=
  ⟨endpointKLo i, endpointKHi i, 7*j.val/40, 7*(j.val+1)/40⟩

def EndpointTableConditions : Prop :=
  ∀ (i : Fin 2) (j : Fin 4), BoxCertificate (endpointMarginPoly i) 6 4 (endpointBox i j)

theorem endpoint_x_cells_cover {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (7/10)) :
    ∃ j : Fin 4, x ∈ Set.Icc ((7*j.val/40 : ℚ) : ℝ) ((7*(j.val+1)/40 : ℚ) : ℝ) := by
  by_cases h0 : x ≤ 7/40
  · exact ⟨⟨0, by decide⟩, by norm_num; exact ⟨hx.1,h0⟩⟩
  by_cases h1 : x ≤ 7/20
  · exact ⟨⟨1, by decide⟩, by norm_num; constructor <;> linarith⟩
  by_cases h2 : x ≤ 21/40
  · exact ⟨⟨2, by decide⟩, by norm_num; constructor <;> linarith⟩
  · exact ⟨⟨3, by decide⟩, by norm_num; constructor <;> linarith [hx.2]⟩

theorem endpoint_margin_nonneg (h : EndpointTableConditions) (i : Fin 2)
    {k x : ℝ} (hk : k ∈ Set.Icc (endpointKLo i : ℝ) (endpointKHi i : ℝ))
    (hx : x ∈ Set.Icc (0 : ℝ) (7/10)) : 0 ≤ realEval₂ (endpointMarginPoly i) k x := by
  obtain ⟨j,hj⟩ := endpoint_x_cells_cover hx
  apply (h i j).nonneg
  exact ⟨hk,hj⟩

def endpointFarG : ℚ[X] :=
  C (1/32)*X+C (1849/1280)*X^2-C (399/128)*X^3+C (245/256)*X^4

def endpointFarDerivative : ℚ[X] :=
  C (7/50)-C (3/32)*X-C (1849/320)*X^2+C (1995/128)*X^3-C (735/128)*X^4

def endpointFarLo (j : Fin 4) : ℚ :=
  if j.val = 0 then 0 else if j.val = 1 then 1/4 else if j.val = 2 then 3/8 else 1/2
def endpointFarHi (j : Fin 4) : ℚ :=
  if j.val = 0 then 1/4 else if j.val = 1 then 3/8 else if j.val = 2 then 1/2 else 1

def EndpointFarConditions : Prop :=
  (∀ j : Fin 4, IntervalCertificate (C (7/100)-endpointFarG)
    (endpointFarLo j) (endpointFarHi j) 4
    (bernsteinCoefficients ((C (7/100)-endpointFarG).comp
      (affine (endpointFarLo j) (endpointFarHi j-endpointFarLo j))) 4)) ∧
  IntervalCertificate endpointFarDerivative (3/4) 1 4
    (bernsteinCoefficients (endpointFarDerivative.comp (affine (3/4) (1/4))) 4)

theorem endpoint_far_g_le (h : EndpointFarConditions) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : realEval endpointFarG x ≤ 7/100 := by
  have hc : ∃ j : Fin 4, x ∈ Set.Icc (endpointFarLo j : ℝ) (endpointFarHi j : ℝ) := by
    by_cases h0 : x ≤ 1/4
    · exact ⟨⟨0, by decide⟩, by norm_num [endpointFarLo,endpointFarHi]; exact ⟨hx.1,h0⟩⟩
    by_cases h1 : x ≤ 3/8
    · exact ⟨⟨1, by decide⟩, by norm_num [endpointFarLo,endpointFarHi]; constructor <;> linarith⟩
    by_cases h2 : x ≤ 1/2
    · exact ⟨⟨2, by decide⟩, by norm_num [endpointFarLo,endpointFarHi]; constructor <;> linarith⟩
    · exact ⟨⟨3, by decide⟩, by norm_num [endpointFarLo,endpointFarHi]; constructor <;> linarith [hx.2]⟩
  obtain ⟨j,hj⟩ := hc
  have he := (h.1 j).nonneg hj
  simpa [realEval, sub_nonneg] using he

theorem endpoint_far_derivative_nonneg (h : EndpointFarConditions) {k : ℝ}
    (hk : k ∈ Set.Icc (3/4 : ℝ) 1) : 0 ≤ realEval endpointFarDerivative k :=
  h.2.nonneg (by simpa using hk)

end
end SingularValueBounds.KL.Certificates
