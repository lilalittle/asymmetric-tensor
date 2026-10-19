import AsymmetricTensor
import ProofAudit
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
A small proved regression supporting the roadmap's selected next task.
This is the actual U_hat specialization; no volume law is postulated.
-/
namespace AsymmetricTensor.RoadmapEvidence

-- Explicit Clebsch gradients preserve the unit-z rotational specialization.
noncomputable def rotationalExample : T2 :=
  U_hat 1 1 0 0 0 (v_perp_covec 0 1 0) (v_perp_covec 1 0 0) 1

theorem alignedClebsch_vorticity (w : ℝ) :
    Omega_x_clebsch (v_perp_covec 0 w 0) (v_perp_covec 1 0 0) = 0 ∧
    Omega_y_clebsch (v_perp_covec 0 w 0) (v_perp_covec 1 0 0) = 0 ∧
    Omega_z_clebsch (v_perp_covec 0 w 0) (v_perp_covec 1 0 0) = w := by
  norm_num [Omega_x_clebsch, Omega_y_clebsch, Omega_z_clebsch,
    omega_clebsch_2form, wedge_covec, v_perp_covec]

theorem rotationalExample_eq :
    rotationalExample = !![-1, 0, 0, 0; 0, 1, -1, 0; 0, 1, 1, 0; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotationalExample, U_hat, Omega_x_clebsch, Omega_y_clebsch,
      Omega_z_clebsch, omega_clebsch_2form, wedge_covec, v_perp_covec]

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

#print axioms alignedClebsch_vorticity
#print axioms rotationalExample_eq
#print axioms rotationalExample_anti_skew
#print axioms rotationalExample_anti_trace
#print axioms rotationalExample_det
#print axioms rotationalExample_not_isochoric

end AsymmetricTensor.RoadmapEvidence

-- The counterexample must not acquire the U_hat_dynamic conservation postulate or
-- positivity axioms. Exact transitive sets are reviewed, not merely printed.
#audit_theorem AsymmetricTensor.RoadmapEvidence.alignedClebsch_vorticity custom []
#audit_theorem AsymmetricTensor.RoadmapEvidence.rotationalExample_eq custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.RoadmapEvidence.rotationalExample_anti_skew custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.RoadmapEvidence.rotationalExample_anti_trace custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.RoadmapEvidence.rotationalExample_det custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.RoadmapEvidence.rotationalExample_not_isochoric custom [AsymmetricTensor.c]
