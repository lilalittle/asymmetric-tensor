import AsymmetricTensor
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
A small proved regression supporting the roadmap's selected next task.
This is the actual U_hat specialization; no volume law is postulated.
-/
namespace AsymmetricTensor.RoadmapEvidence

noncomputable def rotationalExample : T2 := U_hat 1 1 0 0 0 0 0 1 1

theorem rotationalExample_eq :
    rotationalExample = !![-1, 0, 0, 0; 0, 1, -1, 0; 0, 1, 1, 0; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rotationalExample, U_hat]

theorem rotationalExample_anti_skew :
    (antiPart rotationalExample).transpose = -antiPart rotationalExample := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, antiPart]
  ring

theorem rotationalExample_anti_trace : Matrix.trace (antiPart rotationalExample) = 0 := by
  simp [Matrix.trace, Matrix.diag, antiPart]

theorem rotationalExample_det : Matrix.det rotationalExample = -2 := by
  rw [rotationalExample_eq]
  norm_num [Matrix.det_succ_row_zero, Matrix.det_fin_three, Fin.sum_univ_succ]

theorem rotationalExample_not_isochoric : Matrix.det rotationalExample ≠ -1 := by
  rw [rotationalExample_det]
  norm_num

#print axioms rotationalExample_eq
#print axioms rotationalExample_anti_skew
#print axioms rotationalExample_anti_trace
#print axioms rotationalExample_det
#print axioms rotationalExample_not_isochoric

end AsymmetricTensor.RoadmapEvidence
