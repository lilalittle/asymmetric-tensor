import AsymmetricTensor
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ProofAudit

open AsymmetricTensor Filter Set
open scoped Topology

/-! Issue #12: admissible-domain, true-limit, totalized-value, and determinant regressions. -/

example : SubcriticalPressure 1 (3 / 4) := by norm_num [SubcriticalPressure]
example : ¬ SubcriticalPressure 1 1 := by norm_num [SubcriticalPressure]
example : ¬ SubcriticalPressure 1 (-1) := by norm_num [SubcriticalPressure]
example : ¬ SubcriticalPressure 0 0 := by norm_num [SubcriticalPressure]

example : pressureAdmittance 1 (3 / 4) = 1 / 2 := by
  norm_num [pressureAdmittance, Real.sqrt_div]
example : pressureAdmittance 1 2 = 0 := by norm_num [pressureAdmittance]
example : 1 / pressureAdmittance 1 (3 / 4) ^ 2 = 4 := by
  rw [pressure_admittance_inverse_sq (by norm_num [SubcriticalPressure])]
  norm_num

example (a : AdmissibleAdmittance) : a.val ≠ 0 := ne_of_gt a.property.1
example (alpha tp : ℝ) : U_hat 0 alpha 0 0 0 0 0 0 tp = 0 :=
  unloaded_tensor_at_zero alpha tp
example : U_hat (1 / 100) 1 0 0 0 0 0 0 1 1 1 = 10000 := by
  norm_num [U_hat]

-- Exact boundary evaluation and divergent punctured limit are different propositions.
example : 1 / (0 : ℝ) ^ 2 = 0 := totalized_inverse_sq_at_zero 0 rfl
example : Tendsto (fun a : ℝ => 1 / a ^ 2) (𝓝[Ioc 0 1] 0) atTop :=
  admissible_inverse_sq_tendsto_at_top
example : ¬ Tendsto (fun a : ℝ => 1 / a ^ 2) (𝓝[>] 0) (𝓝 0) :=
  inverse_sq_has_no_finite_limit 0
example : Tendsto (fun p : ℝ => 1 / pressureAdmittance P_c p ^ 2)
    (𝓝[Ico 0 P_c] P_c) atTop :=
  pressure_admittance_inverse_sq_tendsto_at_top P_c P_c_pos

-- Actual determinant zero at the aligned boundary allows a nonzero rotation square.
example : Matrix.det (U_hat 0 1 0 0 0 0 0 1 1) = 0 ∧ (1 * 1 * 1 : ℝ) ^ 2 ≠ 0 :=
  boundary_determinant_does_not_force_zero_rotation
example : Matrix.det (U_hat 0 1 0 0 0 0 0 1 1) ≠ -1 := by
  rw [aligned_boundary_determinant]
  norm_num

-- Both directions of denominator clearing require nonzero admittance.
example : (-(1 / (1 / 2 : ℝ) ^ 4) - 0 ^ 2 +
      (1 / (1 / 2 : ℝ) ^ 4) * 1 ^ 2 = 0) ↔
    (1 : ℝ) ^ 2 - (1 / 2) ^ 4 * 0 ^ 2 = 1 :=
  cavitation_formula_iff_of_ne_zero (1 / 2) 1 0 (by norm_num)
example : (-(1 / (0 : ℝ) ^ 4) - 0 ^ 2 + (1 / (0 : ℝ) ^ 4) * 0 ^ 2 = 0) ∧
    ¬ ((0 : ℝ) ^ 2 - 0 ^ 4 * 0 ^ 2 = 1) :=
  cavitation_formula_not_equivalent_at_zero

-- Deprecated names retain their exact algebraic meaning for downstream migration.
example : 1 / (0 : ℝ) ^ 2 = 0 := legal_cavitation_collapse 0 rfl
example : (0 * 1 * 1 : ℝ) ^ 2 = 0 :=
  cavitated_determinant_lock 0 1 0 0 1 rfl (by norm_num)

#audit_theorem AsymmetricTensor.subcritical_gap_bounds custom []
#audit_theorem AsymmetricTensor.pressure_admittance_bounds custom []
#audit_theorem AsymmetricTensor.pressure_admittance_sq custom []
#audit_theorem AsymmetricTensor.pressure_admittance_exp_log custom []
#audit_theorem AsymmetricTensor.continuous_admissible_tensor custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.inverse_sq_tendsto_at_top custom []
#audit_theorem AsymmetricTensor.admissible_inverse_sq_tendsto_at_top custom []
#audit_theorem AsymmetricTensor.subcritical_pressure_tendsto_at_top custom []
#audit_theorem AsymmetricTensor.pressure_admittance_inverse_sq_tendsto_at_top custom []
#audit_theorem AsymmetricTensor.inverse_sq_has_no_finite_limit custom []
#audit_theorem AsymmetricTensor.tensor_spatial_diagonal_tendsto_at_top custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.tensor_has_no_finite_limit custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.inverse_derived_scalar_strain_tendsto custom []
#audit_theorem AsymmetricTensor.normalized_spatial_diagonal_tendsto_one custom []
#audit_theorem AsymmetricTensor.normalized_tensor_tendsto custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.unloaded_tensor_at_zero custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.aligned_boundary_determinant custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.boundary_determinant_does_not_force_zero_rotation custom
  [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.cavitation_formula_iff_of_ne_zero custom []
#audit_theorem AsymmetricTensor.cavitation_formula_not_equivalent_at_zero custom []
#audit_theorem AsymmetricTensor.totalized_formula_not_boundary_determinant custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.totalized_inverse_sq_at_zero custom []
#audit_theorem AsymmetricTensor.totalized_cavitation_formula_at_zero custom [AsymmetricTensor.c]

-- Preserve the full-matrix conclusions and the fixed-load parameter order.
example (alpha vx vy vz ox oy oz tp : ℝ) (value : T2) :
    ¬ Tendsto (fun a : ℝ => U_hat a alpha vx vy vz ox oy oz tp) (𝓝[>] 0) (𝓝 value) :=
  tensor_has_no_finite_limit alpha vx vy vz ox oy oz tp value
example (alpha vx vy vz ox oy oz tp : ℝ) :
    Tendsto (fun a : ℝ => a ^ 2 • U_hat a alpha vx vy vz ox oy oz tp)
      (𝓝[>] 0) (𝓝 (Matrix.diagonal (fun i : Fin 4 => if i = 0 then 0 else 1))) :=
  normalized_tensor_tendsto alpha vx vy vz ox oy oz tp

#print axioms subcritical_gap_bounds
#print axioms continuous_admissible_tensor
#print axioms inverse_sq_tendsto_at_top
#print axioms admissible_inverse_sq_tendsto_at_top
#print axioms pressure_admittance_inverse_sq_tendsto_at_top
#print axioms tensor_has_no_finite_limit
#print axioms normalized_tensor_tendsto
#print axioms boundary_determinant_does_not_force_zero_rotation
#print axioms cavitation_formula_iff_of_ne_zero

/-! PR #61 notation compatibility only: these checks use this main-based library,
not the v3.0 monolith, its changed parameter interfaces, or its axiom inventory. -/
namespace SaturationV3Notation

theorem positive_rpow_neg_two (a : ℝ) (ha : 0 < a) :
    a ^ (-2 : ℝ) = 1 / a ^ 2 := by
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg ha.le]
  norm_num [one_div]

theorem positive_rpow_neg_four (a : ℝ) (ha : 0 < a) :
    a ^ (-4 : ℝ) = 1 / a ^ 4 := by
  rw [show (-4 : ℝ) = -(4 : ℝ) by norm_num, Real.rpow_neg ha.le]
  norm_num [one_div]

theorem v3_spatial_rpow_tendsto_at_top :
    Tendsto (fun a : ℝ => a ^ (-2 : ℝ)) (𝓝[>] 0) atTop := by
  apply inverse_sq_tendsto_at_top.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (positive_rpow_neg_two a ha).symm

example : (0 : ℝ) ^ (-2 : ℝ) = 0 := Real.zero_rpow (by norm_num)
example : (0 : ℝ) ^ (-4 : ℝ) = 0 := Real.zero_rpow (by norm_num)

#audit_theorem SaturationV3Notation.positive_rpow_neg_two custom []
#audit_theorem SaturationV3Notation.positive_rpow_neg_four custom []
#audit_theorem SaturationV3Notation.v3_spatial_rpow_tendsto_at_top custom []
#print axioms positive_rpow_neg_two
#print axioms positive_rpow_neg_four
#print axioms v3_spatial_rpow_tendsto_at_top

end SaturationV3Notation
