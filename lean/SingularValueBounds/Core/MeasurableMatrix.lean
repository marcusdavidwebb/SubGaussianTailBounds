import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.Matrix
import SingularValueBounds.Core.Matrix

/-! # Measurable real matrices and their inverse -/

namespace SingularValueBounds

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

instance matrixMeasurableSpace : MeasurableSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (MeasurableSpace (ι → ι → ℝ))

instance matrixBorelSpace : BorelSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (BorelSpace (ι → ι → ℝ))

instance matrixSecondCountableTopology : SecondCountableTopology (Matrix ι ι ℝ) :=
  inferInstanceAs (SecondCountableTopology (ι → ι → ℝ))

theorem measurable_matrix_inverse : Measurable (fun R : Matrix ι ι ℝ => R⁻¹) := by
  have hc : Continuous (fun R : Matrix ι ι ℝ => R) := continuous_id
  have h := hc.matrix_det.measurable.inv.smul hc.matrix_adjugate.measurable
  change Measurable (fun R : Matrix ι ι ℝ => R.det⁻¹ • R.adjugate) at h
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv] using h

end
end SingularValueBounds
