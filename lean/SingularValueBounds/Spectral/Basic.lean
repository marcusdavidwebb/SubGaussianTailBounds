import SingularValueBounds.Core.MeasurableMatrix

/-! # Symmetric matrices and the resolvent objective of Proposition 2.1 -/

open scoped Matrix BigOperators

namespace SingularValueBounds

noncomputable section

abbrev SymmetricMatrix (ι : Type*) [Fintype ι] :=
  {H : Matrix ι ι ℝ // H.IsHermitian}

instance symmetricMatrixBorelSpace {ι : Type*} [Fintype ι] [DecidableEq ι] :
    BorelSpace (SymmetricMatrix ι) :=
  inferInstanceAs (BorelSpace ({H : Matrix ι ι ℝ | H.IsHermitian} : Set (Matrix ι ι ℝ)))

namespace SymmetricMatrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def zero : SymmetricMatrix ι := ⟨0, Matrix.isHermitian_zero⟩

def neg (H : SymmetricMatrix ι) : SymmetricMatrix ι := ⟨-H.1, H.2.neg⟩

def translate (H : SymmetricMatrix ι) (a : ℝ) : SymmetricMatrix ι :=
  ⟨H.1 + a • (1 : Matrix ι ι ℝ), H.2.add (by simp [Matrix.IsHermitian])⟩

def addOuter (H : SymmetricMatrix ι) (x : ι → ℝ) : SymmetricMatrix ι :=
  ⟨H.1 + Matrix.vecMulVec x x, H.2.add (outer_posSemidef x).isHermitian⟩

def gap (H : SymmetricMatrix ι) (u : ℝ) : Matrix ι ι ℝ :=
  u • (1 : Matrix ι ι ℝ) - H.1

def resolvent (H : SymmetricMatrix ι) (u : ℝ) : Matrix ι ι ℝ := (gap H u)⁻¹

def objective (η : ℝ) (H : SymmetricMatrix ι) (u : ℝ) : ℝ :=
  u + Matrix.trace (resolvent H u) / η ^ 2

def feasible (φ : ℝ) (H : SymmetricMatrix ι) (u : ℝ) : Prop :=
  (gap H u).PosDef ∧ Matrix.trace (resolvent H u) ≤ φ

end SymmetricMatrix

end
end SingularValueBounds
