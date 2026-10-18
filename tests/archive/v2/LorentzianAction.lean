import AsymmetricTensor

open AsymmetricTensor

/-! Issue #10: kernel-checked contraction, frame, domain, and API regressions.
Run after `lake build`: `lake env lean tests/LorentzianAction.lean`. -/

-- The original counterexample: Frobenius gives +2; η raising gives -2.
example : tensor_contract (electricBivector 1) (electricBivector 1) = 2 := by
  norm_num [tensor_contract, electricBivector]
example : contract2 minkowskiInv (electricBivector 1) (electricBivector 1) = -2 := by
  norm_num [electric_lorentzian_contraction]
example : contract2 minkowskiInv (magneticBivector 1) (magneticBivector 1) = 2 := by
  norm_num [magnetic_lorentzian_contraction]

-- Check a mixed field rather than only the separate basis witnesses.
example : contract2 minkowskiInv (electricBivector 2 + magneticBivector 3)
    (electricBivector 2 + magneticBivector 3) = 10 := by
  rw [contract2_minkowskiInv_components]
  norm_num [electricBivector, magneticBivector]
example : frobenius_contract (electricBivector 2 + magneticBivector 3)
    (electricBivector 2 + magneticBivector 3) = 26 := by
  norm_num [frobenius_contract, tensor_contract, electricBivector, magneticBivector]

example (U V : T2) : contract2 minkowskiInv (symPart U) (antiPart V) = 0 :=
  lorentzian_sym_anti_orthogonality U V
example (U : T2) : contract2 minkowskiInv U U =
    contract2 minkowskiInv (symPart U) (symPart U) +
    contract2 minkowskiInv (antiPart U) (antiPart U) :=
  lorentzian_matrix_action_separation U

-- Eq. (121) at nonzero admittance, independently of shear parameters.
example : contract2 minkowskiInv (U_sym 2 7 1 2 3 4 5 6 8)
    (U_sym 2 7 1 2 3 4 5 6 8) = 259 / 16 := by
  rw [symmetric_action_eq121 2 7 1 2 3 4 5 6 8 (by norm_num)]
  norm_num

-- Eq. (123), including ω normalization and an equal electric/magnetic null state.
example : contract2 minkowskiInv (spatialVorticity 2 3 4)
    (spatialVorticity 2 3 4) = 58 := by
  rw [spatial_vorticity_contraction]
  norm_num
example : contract2 minkowskiInv (U_anti 2 1 c 0 0 0 0 1 1)
    (U_anti 2 1 c 0 0 0 0 1 1) = 0 := by
  rw [antisymmetric_action_eq123, spatial_slip_norm, spatial_vorticity_contraction]
  field_simp [c_ne_zero]
  ring

-- Covariant u_0 = -1 and raised u^0 = +1; all selected-frame constraints hold.
example : restCovector 0 = -1 := rfl
example : minkowskiSign 0 * restCovector 0 = 1 := by
  norm_num [minkowskiSign, restCovector]
example (vx vy vz Ox Oy Oz : ℝ) :
    minkowskiPair restCovector restCovector = -1 ∧
    minkowskiPair restCovector (spatialSlipCovector vx vy vz) = 0 ∧
    (∀ ν, ∑ μ : Fin 4, minkowskiSign μ * restCovector μ * restSpatialMetric μ ν = 0) ∧
    (∀ ν, ∑ μ : Fin 4, minkowskiSign μ * restCovector μ * spatialVorticity Ox Oy Oz μ ν = 0) :=
  rest_frame_constraints vx vy vz Ox Oy Oz

-- p. 56 uses S⁻¹ for ONE raised index, which is different from η raising.
example : raiseFirst (symmetricMetricInv 2) (U_anti 2 1 c 0 0 0 0 1 1) 0 1 = 1 / 4 := by
  rw [mixed_electric_measurement]
  norm_num [c_ne_zero]
example : raiseFirst (symmetricMetricInv 2) (U_anti 2 1 c 0 0 0 0 1 1) 1 2 = -4 := by
  rw [mixed_magnetic_measurement]
  norm_num
example : symmetricMetricInv 0 * U_sym 0 0 0 0 0 0 0 0 0 ≠ (1 : T2) := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [Matrix.mul_apply, Fin.sum_univ_succ, symmetricMetricInv] at h00

-- Background subtraction in the exact first line of Eq. (124).
example : lorentzian_action_density minkowskiInv = 4 := by
  unfold lorentzian_action_density
  rw [contract2_minkowskiInv_components]
  norm_num [minkowskiInv, minkowskiSign]
example : kinematic_lagrangian_density minkowskiInv = 0 := by
  unfold kinematic_lagrangian_density lorentzian_action_density
  rw [contract2_minkowskiInv_components]
  norm_num [minkowskiInv, minkowskiSign]

-- Legacy types and new explicit Frobenius aliases remain interchangeable.
example (as a vx vy vz Ox Oy Oz tp : ℝ) :
    frobenius_contract (U_hat as a vx vy vz Ox Oy Oz tp) (U_hat as a vx vy vz Ox Oy Oz tp) =
      frobenius_contract (U_sym as a vx vy vz Ox Oy Oz tp) (U_sym as a vx vy vz Ox Oy Oz tp) +
      frobenius_contract (U_anti as a vx vy vz Ox Oy Oz tp) (U_anti as a vx vy vz Ox Oy Oz tp) :=
  unified_action_separation as a vx vy vz Ox Oy Oz tp

-- Fail hard if these repairs import the inconsistent legacy conservation axiom,
-- sorryAx, or any new scientific axiom. Exact physical-constant dependencies are
-- checked separately from ordinary Lean logical axioms.
open Lean Elab Command in
run_cmd do
  let logical := #[`propext, `Classical.choice, `Quot.sound]
  let checks : Array (Name × Array Name) := #[
    (`AsymmetricTensor.raiseBoth_minkowskiInv, #[]),
    (`AsymmetricTensor.minkowskiInv_sq, #[]),
    (`AsymmetricTensor.lorentzian_sym_anti_orthogonality, #[]),
    (`AsymmetricTensor.lorentzian_matrix_action_separation, #[]),
    (`AsymmetricTensor.pure_electric_negative, #[]),
    (`AsymmetricTensor.pure_magnetic_positive, #[]),
    (`AsymmetricTensor.rest_frame_constraints, #[]),
    (`AsymmetricTensor.restSpatialMetric_eq_background_projector, #[]),
    (`AsymmetricTensor.rest_symmetric_covariant_form, #[`AsymmetricTensor.c]),
    (`AsymmetricTensor.rest_antisymmetric_covariant_form, #[`AsymmetricTensor.c]),
    (`AsymmetricTensor.symmetric_action_eq121, #[`AsymmetricTensor.c]),
    (`AsymmetricTensor.antisymmetric_action_eq123, #[`AsymmetricTensor.c]),
    (`AsymmetricTensor.lorentzian_action_separation, #[`AsymmetricTensor.c]),
    (`AsymmetricTensor.symmetricMetricInv_left_inverse, #[`AsymmetricTensor.c]),
    (`AsymmetricTensor.mixed_electric_measurement, #[`AsymmetricTensor.c]),
    (`AsymmetricTensor.mixed_magnetic_measurement, #[`AsymmetricTensor.c]),
    (`AsymmetricTensor.kinematic_lagrangian_separation,
      #[`AsymmetricTensor.c, `AsymmetricTensor.l_p, `AsymmetricTensor.hbar])]
  for (decl, expected) in checks do
    let actual ← collectAxioms decl
    let custom := actual.filter fun ax => !logical.contains ax
    unless custom.size == expected.size && custom.all expected.contains do
      throwError "ACTION_AXIOM_AUDIT_FAILED: {decl}: expected {expected}, got {custom}"
    logInfo m!"ACTION_AXIOM_AUDIT_OK: {decl}: {custom}"
