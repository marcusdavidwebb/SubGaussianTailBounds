import SingularValueBounds.KL.Upper.GeneralMeanCellData
import SingularValueBounds.KL.Upper.CertificateData

/-! Finite rational contracts for all 1330 joint spectral witnesses. -/
open Polynomial
open scoped Polynomial
namespace SingularValueBounds.KL.Certificates
noncomputable section

def GeneralMeanRow.box (r : GeneralMeanRow) : RationalBox := ⟨r.alo,r.ahi,r.klo,r.khi⟩
def generalMeanSeed (ki : Fin 48) (ai : Fin 42) : RationalBox :=
  ⟨(generalMeanAIntervals ai).1,(generalMeanAIntervals ai).2,(ki.val+32:ℚ)/80,(ki.val+33:ℚ)/80⟩
def GeneralMeanRow.rateCompatible (r : GeneralMeanRow) : Prop :=
  (r.q ≤ 2 ∧ r.C=0) ∨ ∃ j : Fin 15,r.q=(rateRows j).1 ∧ r.C=(rateRows j).2

def generalMeanNormQ (B : ℚ) : ℚ[X] := -2*X+C B*(1-X^2-X^2*(1-X)^2)
def generalMeanJointCleared (J : ℚ) (i : Fin 6) : Polynomial (Polynomial ℚ) :=
  C (C J-majorantBQ i)*padeDQ comparisonZQ+majorantCleared i

def GeneralMeanRowConditions (r : GeneralMeanRow) : Prop :=
  0 ≤ r.klo ∧ r.khi ≤ 1 ∧ 0 ≤ r.alo ∧ r.ahi ≤ 1 ∧ r.rateCompatible ∧
  if hi : r.majorant.val<6 then
    let i : Fin 6:=⟨r.majorant.val,hi⟩
    (majorantBoxes i).left ≤ r.alo ∧ r.ahi ≤ (majorantBoxes i).right ∧
      r.khi ≤ (majorantBoxes i).top ∧
    BoxCertificate (generalMeanJointCleared r.J i) (if i.val=5 then 8 else 6) 15 r.box
  else
    ((r.majorant.val=6 ∧ (5/6:ℚ) ≤ r.alo) ∨ (r.majorant.val=7 ∧ (37/40:ℚ) ≤ r.klo)) ∧
    BoxCertificate (C (C r.J-generalMeanNormQ (if r.majorant.val=6 then 671/100 else 563/100))) 4 0 r.box

/-- All fields are bounded rational comparisons, finite tree checks or coefficient certificates. -/
def GeneralMeanCellConditions : Prop :=
  generalMeanAPartition.Valid generalMeanAIntervals 0 1 ∧
  (∀ ki : Fin 48,∀ ai : Fin 42,(generalMeanClippedTrees ki ai).Valid
    (fun i=>(generalMeanRows i).box) (generalMeanSeed ki ai)) ∧
  (∀ i : Fin 1330,GeneralMeanRowConditions (generalMeanRows i))

def generalMeanSmallRow : GeneralMeanRow :=
  ⟨0,2/5,0,2/5,257/120,11/4,193/100,79/10000,⟨4,by decide⟩⟩

lemma generalMeanSmallRow_rateCompatible : generalMeanSmallRow.rateCompatible := by
  right
  refine ⟨⟨11,by decide⟩,?_,?_⟩ <;> norm_num [generalMeanSmallRow,rateRows]

end
end SingularValueBounds.KL.Certificates
