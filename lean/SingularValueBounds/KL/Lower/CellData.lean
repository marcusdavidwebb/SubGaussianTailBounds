import SingularValueBounds.KL.Certificates.Enclosures

/-! The 681 finite higher-moment cells, with exact rational rounding. -/
open scoped BigOperators
namespace SingularValueBounds.KL.LowerCertificates
open SingularValueBounds.KL.Certificates
open SingularValueBounds.KL.Certificates.NumericalCertificateConditions
noncomputable section

def roundUpQ (x : ℚ) : ℚ := (⌈x*10^12⌉:ℚ)/10^12
def roundDownQ (x : ℚ) : ℚ := (⌊x*10^12⌋:ℚ)/10^12
def logUpperQ (x : ℚ) : ℚ := roundUpQ (logTaylorUpperQ 24 ((x-1)/(x+1)))
def generalLowerProfileQ (k : ℚ) : ℚ :=
  min (4137/1000) (max (3/2) (57/40+23/10*k+47/20*k^2-3/10*k^3))
def momentDq (k p : ℚ) : ℚ := 1+2*p*k^2-4*k^4
def momentBq (k p : ℚ) : ℚ := 2*k^2+1/(p-2*k^2)
def momentEllQ (k p : ℚ) : ℚ := roundUpQ (logUpperQ (momentDq k p)/(2*k^2))
def momentVQ (ell : ℚ) : ℚ := roundDownQ (1/expTaylorUpperQ 40 ell)
def momentLogMinusOneQ (ell : ℚ) : ℚ :=
  if 8 ≤ ell then ell else ell-∑ r ∈ Finset.range 6,(momentVQ ell)^(r+1)/(r+1:ℚ)
def lowerMPartialQ (N : ℕ) (q : ℚ) : ℚ :=
  ∑ r ∈ Finset.range N,2*q^(r+2)/((r+2:ℚ)*(r+3:ℚ))
def lowerCellPower (j : ℕ) : ℚ :=
  let mid := (2*j+1:ℚ)/2000
  if j < 650 then 37/10+13/(10*mid)-mid^2/2 else 12-10*mid

structure MomentCellCertificate (a b p : ℚ) : Prop where
  a_pos : 0 < a
  a_le_b : a ≤ b
  b_le : b ≤ 711/1000
  power : 19/4 ≤ p
  u_domain : (4*p/((p-1)*generalLowerProfileQ a))*b < 1
  shape : a^2 < lowerMPartialQ 59 ((4*p/((p-1)*generalLowerProfileQ b))*a)
  ell_pos : 0 < momentEllQ a p
  v_nonneg : momentEllQ a p < 8 → 0 ≤ momentVQ (momentEllQ a p)
  v_lt : momentEllQ a p < 8 → momentVQ (momentEllQ a p) < 1
  v_exp : momentEllQ a p < 8 → momentVQ (momentEllQ a p)*expTaylorUpperQ 40 (momentEllQ a p) ≤ 1
  entropy :
    (p-1)*(logUpperQ (1/(1-(4*p/((p-1)*generalLowerProfileQ a))*b))-
        (4*p/((p-1)*generalLowerProfileQ a))*b)/(2*b^2)+
      momentLogMinusOneQ (momentEllQ a p)+p*logUpperQ (p*momentBq b p)+
      1/(expTaylorQ 24 (p-1/20)-1) < 3*p

def MomentCellConditions : Prop :=
  (∀ j : Fin 681, MomentCellCertificate ((j.val+30:ℚ)/1000)
    ((j.val+31:ℚ)/1000) (lowerCellPower (j.val+30))) ∧
  MomentCellCertificate (3/100) (3/100) 50

end
end SingularValueBounds.KL.LowerCertificates
