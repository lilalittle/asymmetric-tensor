import AsymmetricTensor
import ProofAudit

/-!
Call-site regressions for the approved v5.7 source migration. These test the new
dimension basis, witnessed on-shell state, and explicitly restricted application
APIs. They do not restore the removed v5.0 interfaces or infer a physical model
from compilation. Full source/reference type comparison is a separate check.
-/

open AsymmetricTensor

namespace V57Migration

-- Constructor order and named projections are part of the intentional breaking
-- change from the old L/V/S fields. The derived and arithmetic instances remain.
example : UnitDim := UnitDim.mk 2 (-3) 4
example : DecidableEq UnitDim := inferInstance
example : Repr UnitDim := inferInstance
example : Mul UnitDim := inferInstance
example : Div UnitDim := inferInstance
example : HPow UnitDim ℤ UnitDim := inferInstance

theorem dimension_projections :
    (UnitDim.mk 2 (-3) 4).K = 2 ∧
    (UnitDim.mk 2 (-3) 4).Omega = -3 ∧
    (UnitDim.mk 2 (-3) 4).E = 4 := by
  exact ⟨rfl, rfl, rfl⟩

theorem nonunit_dimension_arithmetic :
    (UnitDim.mk 2 (-3) 4) * (UnitDim.mk (-1) 5 (-2)) = UnitDim.mk 1 2 2 ∧
    (UnitDim.mk 2 (-3) 4) / (UnitDim.mk (-1) 5 (-2)) = UnitDim.mk 3 (-8) 6 ∧
    (UnitDim.mk 2 (-3) 4) ^ (-2 : ℤ) = UnitDim.mk (-4) 6 (-8) := by
  exact ⟨rfl, rfl, rfl⟩

-- The old exponent tuple is transformed, not merely renamed. Test the supplied
-- forward map at mixed nonunit exponents and its general integer inverse.
theorem nonunit_legacy_basis :
    (u_l_p ^ (2 : ℤ)) * (u_c ^ (-3 : ℤ)) * (u_hbar ^ (4 : ℤ)) =
      UnitDim.mk 1 (-7) 4 := by
  simpa using unit_basis_isomorphism_LVS_KOE 2 (-3) 4

theorem curvature_basis_roundtrip (K Omega E : ℤ) :
    (u_l_p ^ (-K - Omega - E)) * (u_c ^ (Omega + E)) * (u_hbar ^ E) =
      UnitDim.mk K Omega E := by
  rw [unit_basis_isomorphism_LVS_KOE]
  congr 1 <;> ring

theorem physical_unit_migration :
    u_l_p.K = -1 ∧ u_c.Omega = 1 ∧ u_hbar.E = 1 ∧
    u_M_P = UnitDim.mk 2 (-2) 1 ∧
    u_G = UnitDim.mk (-5) 4 (-1) ∧
    u_SurfTension = UnitDim.mk 2 0 1 ∧
    u_Viscosity = UnitDim.mk 3 (-1) 1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in #[`AsymmetricTensor.UnitDim.L, `AsymmetricTensor.UnitDim.V,
      `AsymmetricTensor.UnitDim.S] do
    if (env.find? name).isSome then
      throwError "V57_DIMENSION_MIGRATION: obsolete projection {name} unexpectedly exists"
  logInfo "V57_DIMENSION_MIGRATION: K/Omega/E replaces L/V/S"

-- Reconstruct through the generated constructor with every field in its source
-- order. The conservation projection is a required dependent argument.
theorem dynamic_constructor_roundtrip (fields : DynamicClebschFields) :
    DynamicClebschFields.mk fields.alpha_s_f fields.alpha_f fields.h_phase_f
      fields.v_x_f fields.v_y_f fields.v_z_f fields.lambda_Omega_f
      fields.beta_Omega_f fields.conservation = fields := by
  cases fields
  rfl

theorem witnessed_state_exists : Nonempty DynamicClebschFields :=
  ⟨vacuum_clebsch_witness⟩

theorem vacuum_field_values (x : SpaceTime) :
    vacuum_clebsch_witness.alpha_s_f x = 1 ∧
    vacuum_clebsch_witness.alpha_f x = 0 ∧
    vacuum_clebsch_witness.h_phase_f x = 0 ∧
    vacuum_clebsch_witness.v_x_f x = 0 ∧
    vacuum_clebsch_witness.v_y_f x = 0 ∧
    vacuum_clebsch_witness.v_z_f x = 0 ∧
    vacuum_clebsch_witness.lambda_Omega_f x = 0 ∧
    vacuum_clebsch_witness.beta_Omega_f x = 0 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- No equality between the opaque active state and an arbitrary solution is
-- assumed or proved here. Its public scalar fields are precisely projections.
theorem active_field_projections (x : SpaceTime) :
    alpha_s_f x = dyn_state.alpha_s_f x ∧
    alpha_f x = dyn_state.alpha_f x ∧
    h_phase_f x = dyn_state.h_phase_f x ∧
    v_x_f x = dyn_state.v_x_f x ∧
    v_y_f x = dyn_state.v_y_f x ∧
    v_z_f x = dyn_state.v_z_f x ∧
    lambda_Omega_f x = dyn_state.lambda_Omega_f x ∧
    beta_Omega_f x = dyn_state.beta_Omega_f x := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem active_conservation_projection (x : SpaceTime) :
    metric_divergence U_hat_dynamic x = 0 :=
  dyn_state.conservation x

theorem schwinger_vectors_nonzero :
    schwinger_eigvec_plus ≠ 0 ∧ schwinger_eigvec_minus ≠ 0 := by
  constructor
  · intro h
    have h1 := congrFun h (1 : Fin 4)
    norm_num [schwinger_eigvec_plus] at h1
  · intro h
    have h1 := congrFun h (1 : Fin 4)
    norm_num [schwinger_eigvec_minus] at h1

-- Consume the entrywise bridge to obtain actual shifted-U_hat matrix-vector
-- equations. Keep every zero-slip/alignment premise; a 2x2 block is insufficient.
theorem shifted_tensor_eigenpairs
    (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ)
    (h_alpha_s : alpha_s = 1)
    (h_vx : v_x = 0) (h_vy : v_y = 0) (h_vz : v_z = 0)
    (h_Ox : Omega_x_clebsch d_lambda d_beta = 0)
    (h_Oy : Omega_y_clebsch d_lambda d_beta = 0)
    (h_Omega : alpha * t_p_val * Omega_z_clebsch d_lambda d_beta = 1) :
    Matrix.mulVec
      (fun i j : Fin 4 =>
        (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val i j : ℂ) -
          (if i = j then 1 + Complex.I else 0)) schwinger_eigvec_plus = 0 ∧
    Matrix.mulVec
      (fun i j : Fin 4 =>
        (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val i j : ℂ) -
          (if i = j then 1 - Complex.I else 0)) schwinger_eigvec_minus = 0 := by
  have hp := schwinger_zero_slip_aligned_bridge
    alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val (1 + Complex.I)
    h_alpha_s h_vx h_vy h_vz h_Ox h_Oy h_Omega
  have hm := schwinger_zero_slip_aligned_bridge
    alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val (1 - Complex.I)
    h_alpha_s h_vx h_vy h_vz h_Ox h_Oy h_Omega
  constructor
  · have hmatrix :
        (fun i j : Fin 4 =>
          (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val i j : ℂ) -
            (if i = j then 1 + Complex.I else 0)) =
          U_aligned_char_matrix 1 0 1 (1 + Complex.I) := by
      funext i j
      exact hp.1 i j
    rw [hmatrix]
    exact hp.2.1
  · have hmatrix :
        (fun i j : Fin 4 =>
          (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val i j : ℂ) -
            (if i = j then 1 - Complex.I else 0)) =
          U_aligned_char_matrix 1 0 1 (1 - Complex.I) := by
      funext i j
      exact hm.1 i j
    rw [hmatrix]
    exact hm.2.2

-- The new leading total-admittance argument and defining hypothesis must remain
-- explicit. Select combined temporal, clock, and pressure-only optical results.
theorem optical_specialization_call_site
    (alpha_s alpha_g alpha_a alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4)
    (t_p_val v_0 v_flow P_static P_dyn v_c n_idx : ℝ)
    (hag : alpha_g ≠ 0) (hv_sub : v_0 / c ≠ 1) (hv_plus : 1 + v_0 / c ≠ 0)
    (h_as : alpha_s = alpha_g * alpha_a)
    (h_ledger : P_c = P_static + P_dyn)
    (h_P_dyn : P_dyn = (1 / 2) * rho_tau * v_0^2)
    (h_ag_sq : alpha_g^2 = P_static / P_c)
    (h_freefall : v_flow = v_0) (h_aa_eq : alpha_a = alpha_g)
    (h_vc : v_c = c * alpha_g^2) (h_n : n_idx = c / v_c) :
    (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 0 0 =
      -(alpha_g^2 * alpha_a^2) ∧
    1 / alpha_s = (1 / alpha_g) * (1 / alpha_a) ∧
    n_idx = (U_hat alpha_g alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 1 := by
  have h := tensor_four_effects_unification
    alpha_s alpha_g alpha_a alpha v_x v_y v_z d_lambda d_beta
    t_p_val v_0 v_flow P_static P_dyn v_c n_idx
    hag hv_sub hv_plus h_as h_ledger h_P_dyn h_ag_sq h_freefall h_aa_eq h_vc h_n
  exact ⟨h.2.1, h.2.2.1.symm, h.2.2.2.2.2.2⟩

-- With alpha_g = alpha_a = 3/5, the combined tensor uses alpha_s = 9/25.
-- This nonunit example prevents silently substituting one tensor for the other.
theorem combined_and_pressure_diagonals_differ :
    (U_hat (9 / 25) 1 0 0 0 (fun _ => 0) (fun _ => 0) 1) 0 0 ≠
      (U_hat (3 / 5) 1 0 0 0 (fun _ => 0) (fun _ => 0) 1) 0 0 := by
  norm_num [U_hat]

-- Exercise the revised Frobenius prefactor at alpha = 2 and volume = 3.
-- Nonzero vorticity remains an explicit premise for strict positivity.
theorem nonunit_frobenius_mass (d_lambda d_beta : V4)
    (h_omega_ne : Omega_z_clebsch d_lambda d_beta ≠ 0) :
    let shear := (1 / 2) * P_c * 4 *
      (t_p^2 * (Omega_z_clebsch d_lambda d_beta)^2)
    (shear * 3) / c^2 =
      3 * rho_tau * t_p^2 * (Omega_z_clebsch d_lambda d_beta)^2 ∧
    0 < (shear * 3) / c^2 := by
  let shear := (1 / 2) * P_c * 4 *
    (t_p^2 * (Omega_z_clebsch d_lambda d_beta)^2)
  have h := phase_locked_frobenius_rest_mass_pos
    d_lambda d_beta 2 0 3 shear (shear * 3) ((shear * 3) / c^2)
    (by norm_num) (by norm_num) h_omega_ne
    (by dsimp [shear]; norm_num) rfl rfl
  change (shear * 3) / c^2 =
    3 * rho_tau * t_p^2 * (Omega_z_clebsch d_lambda d_beta)^2 ∧
    0 < (shear * 3) / c^2
  refine ⟨?_, h.2⟩
  calc (shear * 3) / c^2 = (rho_tau * 3 * 2^2 / 4) *
      (0^2 / c^2 + t_p^2 * (Omega_z_clebsch d_lambda d_beta)^2) := h.1
    _ = 3 * rho_tau * t_p^2 * (Omega_z_clebsch d_lambda d_beta)^2 := by ring

#audit_theorem V57Migration.curvature_basis_roundtrip custom []
#audit_theorem V57Migration.dynamic_constructor_roundtrip custom []
#audit_theorem V57Migration.witnessed_state_exists custom []
#audit_theorem V57Migration.active_conservation_projection custom []
#audit_theorem V57Migration.schwinger_vectors_nonzero custom []
#audit_theorem V57Migration.shifted_tensor_eigenpairs custom []
#audit_theorem V57Migration.optical_specialization_call_site custom []
#audit_theorem V57Migration.nonunit_frobenius_mass custom []

end V57Migration

#audit_current_module declared []
