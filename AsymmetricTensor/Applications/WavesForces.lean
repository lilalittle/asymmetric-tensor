import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Geometry.Manifold.Instances.Real

import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic

open Real
open BigOperators

namespace AsymmetricTensor

set_option linter.unusedSectionVars false
set_option autoImplicit false

-- ======================================================================
-- SECTION 13: TRANSVERSE WAVE MECHANICS, CHIRAL INDUCTION, AND PLASMA ATTENUATION
-- ======================================================================

-- Dimensional Audit: Transverse wave equation ((1 / c^2) * d^2 v_perp / dt^2 = nabla^2 v_perp) balances at ⟨-2, 1, 0⟩:
theorem unit_section13_wave_mechanics :
    (u_dimless / (u_c^(2:ℤ))) * (u_c / (u_t_p^(2:ℤ))) = u_Laplacian * u_c := by rfl

-- ----------------------------------------------------------------------
-- 13.1 Transverse Shear and Strain Propagation (Light)
-- ----------------------------------------------------------------------
lemma wave_equation_algebra (c_val : ℝ) (hc : (0 : ℝ) < c_val) (v_perp_accel v_perp_laplace : V_3D) :
  (1 / c_val^2) • v_perp_accel = v_perp_laplace →
  v_perp_accel = c_val^2 • v_perp_laplace := by
  intro h
  have hc_ne : c_val^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hc)
  have h1 : c_val^2 * (1 / c_val^2) = 1 := by
    have h_frac : c_val^2 * (1 / c_val^2) = c_val^2 / c_val^2 := by ring
    rw [h_frac]
    exact div_self hc_ne
  rw [← one_smul ℝ v_perp_accel, ← h1, mul_smul, h]

variable (v_perp_accel v_perp_laplace : V_3D)

-- Theorem 86: Transverse Electromagnetic Wave Propagation (∂_t^2 v_⊥ = c^2 ∇^2 v_⊥, Manuscript Section 13.1)
theorem transverse_wave_propagation
    (h_wave : (1 / c^2) • v_perp_accel = v_perp_laplace) :
    v_perp_accel = c^2 • v_perp_laplace := by
  exact wave_equation_algebra c c_pos v_perp_accel v_perp_laplace h_wave

-- ----------------------------------------------------------------------
-- 13.2 Metric Depletion and Chiral Induction (Manuscript Eqs. 176–177)
-- ----------------------------------------------------------------------

-- Dimensional Audit: Both the d'Alembertian wave operator ((1/c^2) ∂_t^2 v_⊥ - ∇^2 v_⊥)
-- and the chiral vorticity induction term ((1/c^2) (Ω_0 · ∂_t v_⊥)) have dimension u_Laplacian * u_c (⟨-2, 1, 0⟩):
theorem unit_section13_2_chiral_induction :
    (u_dimless / (u_c^(2:ℤ))) * (u_c / (u_t_p^(2:ℤ))) = u_Laplacian * u_c ∧
    (u_dimless / (u_c^(2:ℤ))) * (u_omega * (u_c / u_t_p)) = u_Laplacian * u_c ∧
    u_omega * (u_c / u_t_p) = u_c / (u_t_p^(2:ℤ)) := by
  refine ⟨rfl, rfl, rfl⟩

-- Theorem 166: Plasma Metric Depletion & Chiral Clebsch Wave Coupling (Manuscript Section 13.2)
-- Proves:
-- 1. When a transverse wave enters a plasma with depleted scalar admittance (`alpha_s^2 < 1`),
--    the ambient dynamic pressure `P_dyn = (1 - alpha_s^2) * P_c` is strictly positive (`0 < P_dyn`)
--    and the static pressure reserve `P_static = alpha_s^2 * P_c` is strictly depleted (`P_static < P_c`),
-- 2. Contracting the background Clebsch vorticity 2-form `Ω_0 = dλ_0 ∧ dβ_0` (`omega_clebsch_2form`)
--    against the temporal derivative of the transverse slip `(dt_vx, dt_vy, dt_vz)` extracts the
--    exact chiral cross-coupling `Ω_0y ∂_t v_z - Ω_0z ∂_t v_y`.
theorem plasma_metric_depletion_and_chiral_wave_coupling
    (alpha_s P_dyn P_static dt_vy dt_vz : ℝ) (d_lambda0 d_beta0 : V4)
    (h_depleted : alpha_s^2 < 1)
    (h_P_dyn : P_dyn = (1 - alpha_s^2) * P_c)
    (h_ledger : P_c = P_static + P_dyn) :
    0 < P_dyn ∧
    P_static < P_c ∧
    omega_clebsch_2form d_lambda0 d_beta0 1 2 * dt_vy +
      omega_clebsch_2form d_lambda0 d_beta0 1 3 * dt_vz =
    Omega_y_clebsch d_lambda0 d_beta0 * dt_vz -
      Omega_z_clebsch d_lambda0 d_beta0 * dt_vy := by
  have hPc : 0 < P_c := by
    dsimp [P_c]
    have hrho : 0 < rho_tau := rho_tau_pos
    have hc : 0 < c := c_pos
    positivity
  have h_sub : 0 < 1 - alpha_s^2 := by linarith
  have h_dyn_pos : 0 < P_dyn := by
    rw [h_P_dyn]
    exact mul_pos h_sub hPc
  refine ⟨h_dyn_pos, by linarith, ?_⟩
  dsimp [Omega_y_clebsch, Omega_z_clebsch, omega_clebsch_2form, wedge_covec]
  ring

-- Theorem 167: Chiral Induction Orthogonality & Polarization Rotation (Manuscript Section 13.2)
-- Proves directly from `omega_clebsch_2form` that the inner-product contraction of the temporal
-- velocity derivative 1-form `(dt_vx, dt_vy, dt_vz)` against the antisymmetric background Clebsch
-- vorticity 2-form `Ω_0 = dλ_0 ∧ dβ_0` is strictly orthogonal to `(dt_vx, dt_vy, dt_vz)`
-- (`∂_t v_⊥ · (Ω_0 · ∂_t v_⊥) = 0`), rotating the transverse polarization plane without altering
-- scalar wave energy, and verifies the `1 / c^2` wave-operator scaling.
theorem chiral_induction_orthogonality
    (d_lambda0 d_beta0 : V4) (dt_vx dt_vy dt_vz wave_op_i chiral_i : ℝ)
    (h_wave_eq : wave_op_i = (1 / c^2) * chiral_i) :
    dt_vx * (omega_clebsch_2form d_lambda0 d_beta0 1 2 * dt_vy +
             omega_clebsch_2form d_lambda0 d_beta0 1 3 * dt_vz) +
    dt_vy * (omega_clebsch_2form d_lambda0 d_beta0 2 1 * dt_vx +
             omega_clebsch_2form d_lambda0 d_beta0 2 3 * dt_vz) +
    dt_vz * (omega_clebsch_2form d_lambda0 d_beta0 3 1 * dt_vx +
             omega_clebsch_2form d_lambda0 d_beta0 3 2 * dt_vy) = 0 ∧
    c^2 * wave_op_i = chiral_i := by
  have hc : c ≠ 0 := c_ne_zero
  refine ⟨?_, ?_⟩
  · dsimp [omega_clebsch_2form, wedge_covec]
    ring
  · rw [h_wave_eq]
    field_simp [hc]

-- ----------------------------------------------------------------------
-- 13.3 Macroscopic Measurement Boundaries (Deterministic Eigenstates)
-- ----------------------------------------------------------------------
variable (P_dyn_trans P_dyn_0 theta : ℝ)

lemma malus_law_algebra (rho_val v_perp_val theta_val P_0_val : ℝ) :
  P_0_val = (1 / 2) * rho_val * v_perp_val^2 →
  (1 / 2) * rho_val * (v_perp_val * Real.cos theta_val)^2 = P_0_val * (Real.cos theta_val)^2 := by
  intro h
  have h1 : (1 / 2) * rho_val * (v_perp_val * Real.cos theta_val)^2 =
            ((1 / 2) * rho_val * v_perp_val^2) * (Real.cos theta_val)^2 := by ring
  rw [h1, ←h]

-- Theorem 87: Transverse Energy Transmission / Malus's Law (P_dyn^trans = P_dyn^(0) cos^2 θ, Manuscript Section 13.3)
theorem transverse_energy_transmission
    (v_perp_val : ℝ)
    (h_P_0 : P_dyn_0 = (1 / 2) * rho_tau * v_perp_val^2)
    (h_P_trans : P_dyn_trans = (1 / 2) * rho_tau * (v_perp_val * Real.cos theta)^2) :
    P_dyn_trans = P_dyn_0 * (Real.cos theta)^2 := by
  have h1 := malus_law_algebra rho_tau v_perp_val theta P_dyn_0 h_P_0
  rw [h_P_trans, h1]

-- Theorem 88: Exterior Derivative Measurement Torque Expansion (-d(cos θ v_⊥) = -cos θ dv_⊥ + sin θ (dθ ∧ v_⊥), Manuscript Section 13.3)
theorem measurement_torque_wedge_expansion
    (cos_theta_form sin_theta_form theta_form : Forms_0D) (v_perp_form : Forms_1D)
    (h_leibniz_1form : d1 (smul_form cos_theta_form v_perp_form) =
      wedge (d0 cos_theta_form) v_perp_form + smul_2form cos_theta_form (d1 v_perp_form))
    (h_chain_cos : wedge (d0 cos_theta_form) v_perp_form =
      - smul_2form sin_theta_form (wedge (d0 theta_form) v_perp_form)) :
    - d1 (smul_form cos_theta_form v_perp_form) =
    - smul_2form cos_theta_form (d1 v_perp_form) +
      smul_2form sin_theta_form (wedge (d0 theta_form) v_perp_form) := by
  rw [h_leibniz_1form, h_chain_cos]
  abel

-- Theorem 89: Deterministic Eigenstate Convergence / Wavefunction Collapse (sin θ = 0, Manuscript Section 13.3)
theorem eigenstate_convergence [NoZeroSMulDivisors ℝ Forms_2D]
    (theta_form : Forms_0D) (v_perp_form : Forms_1D)
    (h_steady : (0 : Forms_2D) =
      - (Real.cos theta) • (d1 v_perp_form) + (Real.sin theta) • wedge (d0 theta_form) v_perp_form)
    (h_dv_zero : d1 v_perp_form = 0)
    (h_wedge_ne_zero : wedge (d0 theta_form) v_perp_form ≠ 0) :
    Real.sin theta = 0 := by
  rw [h_dv_zero, smul_zero, zero_add] at h_steady
  cases smul_eq_zero.mp h_steady.symm with
  | inl h_sin => exact h_sin
  | inr h_w => exact False.elim (h_wedge_ne_zero h_w)

-- ----------------------------------------------------------------------
-- 13.4 Metric Yielding and Attenuation
-- ----------------------------------------------------------------------
variable (lambda_D L_0 P_dyn_val : ℝ)

lemma attenuation_length_algebra (L_val P_c_val P_dyn_val rho_val c_val : ℝ) :
  P_c_val = (1 / 2) * rho_val * c_val^2 →
  L_val * Real.sqrt (1 - P_dyn_val / P_c_val) =
  L_val * Real.sqrt (1 - P_dyn_val / ((1 / 2) * rho_val * c_val^2)) := by
  intro h
  rw [h]

-- Theorem 90: Debye Attenuation Length Envelope (λ_D = L_0 √(1 - P_dyn / P_c), Manuscript Section 13.4)
theorem debye_attenuation_length
    (h_lambda : lambda_D = L_0 * Real.sqrt (1 - P_dyn_val / P_c)) :
    lambda_D = L_0 * Real.sqrt (1 - P_dyn_val / ((1 / 2) * rho_tau * c^2)) := by
  have h_Pc_sub : P_c = (1 / 2) * rho_tau * c^2 := emergent_critical_pressure
  have h1 := attenuation_length_algebra L_0 P_c P_dyn_val rho_tau c h_Pc_sub
  rw [h_lambda, h1]

-- ======================================================================
-- SECTION 14: CONTINUOUS PRESSURE DYNAMICS (FUNDAMENTAL FORCES)
-- ======================================================================

-- Dimensional Audit: Isochoric flow (v = C / r^2), dynamic pressure (rho_tau C^2 / 2 r^4), action (E * T = hbar), and C^2 = kappa c / rho_tau:
theorem unit_section14_isochoric_and_action :
    u_C_isochoric / (u_l_p^(2:ℤ)) = u_c ∧
    (u_rho_tau * (u_C_isochoric^(2:ℤ))) / (u_l_p^(4:ℤ)) = u_P_c ∧
    u_Energy * u_t_p = u_hbar ∧
    (u_hbar * u_c) / u_rho_tau = u_C_isochoric^(2:ℤ) ∧
    (u_hbar * u_c) / (u_l_p^(4:ℤ)) = u_P_c := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ----------------------------------------------------------------------
-- 14.1 The Isochoric Velocity Scaling
-- ----------------------------------------------------------------------
variable (C : ℝ)

-- Theorem 91: Isochoric Velocity & Dynamic Pressure Scaling (P_dyn(r) = ρ_τ C^2 / 2r^4, Manuscript Section 14.1)
theorem isochoric_velocity_scaling (r : ℝ) (_hr : r ≠ 0)
    (h_v : v_val = C / r^2)
    (h_P_dyn : P_dyn_val = (1 / 2) * rho_tau * v_val^2) :
    P_dyn_val = (rho_tau * C^2) / (2 * r^4) := by
  have h1 : P_dyn_val = (1 / 2) * rho_tau * (C / r^2)^2 := by rw [h_P_dyn, h_v]
  have h2 : (C / r^2)^2 = C^2 / (r^2)^2 := by rw [div_pow]
  have h3 : (r^2)^2 = r^4 := by ring
  have h4 : P_dyn_val = (1 / 2) * rho_tau * (C^2 / r^4) := by
    rw [h2, h3] at h1
    exact h1
  have h5 : (1 / 2) * rho_tau * (C^2 / r^4) = (rho_tau * C^2) / (2 * r^4) := by ring
  rw [h5] at h4
  exact h4

-- ----------------------------------------------------------------------
-- 14.2 The Geometric Action Boundary (Deriving the Scalar)
-- ----------------------------------------------------------------------
variable (E_val T_val : ℝ)

-- Theorem 92: Geometric Action Constant Extraction (C^2 = κ c / (4π^2 ρ_τ), Manuscript Section 14.2)
theorem geometric_action_boundary (r : ℝ) (_hr : r ≠ 0) (kappa : ℝ)
    (h_S : kappa = E_val * T_val)
    (h_T : T_val = (2 * Real.pi * r) / c)
    (h_E : E_val = (2 * Real.pi * rho_tau * C^2) / r) :
    C^2 = (kappa * c) / (4 * Real.pi^2 * rho_tau) := by
  have hc : c ≠ 0 := ne_of_gt c_pos
  have hrho : rho_tau ≠ 0 := ne_of_gt rho_tau_pos
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h_denom : 4 * Real.pi^2 * rho_tau ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hpi)) hrho
  have h1 : kappa = ((2 * Real.pi * rho_tau * C^2) / r) * ((2 * Real.pi * r) / c) := by rw [h_S, h_E, h_T]
  have h2 : ((2 * Real.pi * rho_tau * C^2) / r) * ((2 * Real.pi * r) / c) = (4 * Real.pi^2 * rho_tau * C^2) / c := by
    have h2a : ((2 * Real.pi * rho_tau * C^2) / r) * ((2 * Real.pi * r) / c) =
               (4 * Real.pi^2 * rho_tau * C^2 * r) / (r * c) := by ring
    have h2b : (4 * Real.pi^2 * rho_tau * C^2 * r) / (r * c) =
               ((4 * Real.pi^2 * rho_tau * C^2) / c) * (r / r) := by ring
    have h2c : ((4 * Real.pi^2 * rho_tau * C^2) / c) * (r / r) =
               (4 * Real.pi^2 * rho_tau * C^2) / c := by rw [div_self _hr, mul_one]
    rw [h2a, h2b, h2c]
  rw [h2] at h1
  have h3a : kappa * c = (((4 * Real.pi^2 * rho_tau * C^2) / c)) * c := congrArg (· * c) h1
  have h3b : (((4 * Real.pi^2 * rho_tau * C^2) / c)) * c = (4 * Real.pi^2 * rho_tau * C^2) * (c / c) := by ring
  rw [h3b, div_self hc, mul_one] at h3a
  have h4a : C^2 * (4 * Real.pi^2 * rho_tau) = 4 * Real.pi^2 * rho_tau * C^2 := by ring
  have h4b : 4 * Real.pi^2 * rho_tau * C^2 = kappa * c := h3a.symm
  have h4 : C^2 * (4 * Real.pi^2 * rho_tau) = kappa * c := by rw [h4a, h4b]
  have h5 : (C^2 * (4 * Real.pi^2 * rho_tau)) / (4 * Real.pi^2 * rho_tau) =
            (kappa * c) / (4 * Real.pi^2 * rho_tau) := congrArg (· / (4 * Real.pi^2 * rho_tau)) h4
  have h6 : (C^2 * (4 * Real.pi^2 * rho_tau)) / (4 * Real.pi^2 * rho_tau) = C^2 := by
    have h_pull : (C^2 * (4 * Real.pi^2 * rho_tau)) / (4 * Real.pi^2 * rho_tau) =
                  C^2 * ((4 * Real.pi^2 * rho_tau) / (4 * Real.pi^2 * rho_tau)) := by ring
    rw [h_pull, div_self h_denom, mul_one]
  rw [h6] at h5
  exact h5

-- Theorem 93: Spatial Confinement Pressure Gradient (P(r) = κ c / (8π^2 r^4), Manuscript Section 14.2)
theorem spatial_confinement_gradient (r : ℝ) (hr : r ≠ 0) (kappa : ℝ)
    (h_P : P_dyn_val = (rho_tau * C^2) / (2 * r^4))
    (h_C : C^2 = (kappa * c) / (4 * Real.pi^2 * rho_tau)) :
    P_dyn_val = (kappa * c) / (8 * Real.pi^2 * r^4) := by
  have hrho : rho_tau ≠ 0 := ne_of_gt rho_tau_pos
  have h1 : rho_tau * C^2 = (rho_tau * (kappa * c)) / (rho_tau * (4 * Real.pi^2)) := by
    have h1a : rho_tau * C^2 = rho_tau * ((kappa * c) / (4 * Real.pi^2 * rho_tau)) := by rw [h_C]
    have h1b : rho_tau * ((kappa * c) / (4 * Real.pi^2 * rho_tau)) =
               (rho_tau * (kappa * c)) / (4 * Real.pi^2 * rho_tau) := by ring
    have h1c : (rho_tau * (kappa * c)) / (4 * Real.pi^2 * rho_tau) =
               (rho_tau * (kappa * c)) / (rho_tau * (4 * Real.pi^2)) := by ring
    rw [h1a, h1b, h1c]
  have h2 : (rho_tau * (kappa * c)) / (rho_tau * (4 * Real.pi^2)) = (kappa * c) / (4 * Real.pi^2) := by
    have h2a : (rho_tau * (kappa * c)) / (rho_tau * (4 * Real.pi^2)) =
               ((kappa * c) / (4 * Real.pi^2)) * (rho_tau / rho_tau) := by ring
    rw [h2a, div_self hrho, mul_one]
  rw [h2] at h1
  have h3 : P_dyn_val * (2 * r^4) = (kappa * c) / (4 * Real.pi^2) := by
    have h3a : P_dyn_val * (2 * r^4) = ((rho_tau * C^2) / (2 * r^4)) * (2 * r^4) := congrArg (· * (2 * r^4)) h_P
    have h3b : ((rho_tau * C^2) / (2 * r^4)) * (2 * r^4) = (rho_tau * C^2) * ((2 * r^4) / (2 * r^4)) := by ring
    rw [h3a, h3b, div_self (mul_ne_zero (by norm_num) (pow_ne_zero 4 hr)), mul_one, h1]
  have h4 : P_dyn_val = (P_dyn_val * (2 * r^4)) / (2 * r^4) := by
    have h_pull : (P_dyn_val * (2 * r^4)) / (2 * r^4) = P_dyn_val * ((2 * r^4) / (2 * r^4)) := by ring
    rw [h_pull, div_self (mul_ne_zero (by norm_num) (pow_ne_zero 4 hr)), mul_one]
  have h5 : (P_dyn_val * (2 * r^4)) / (2 * r^4) = ((kappa * c) / (4 * Real.pi^2)) / (2 * r^4) :=
    congrArg (· / (2 * r^4)) h3
  rw [h5] at h4
  have h6 : ((kappa * c) / (4 * Real.pi^2)) / (2 * r^4) = (kappa * c) / (8 * Real.pi^2 * r^4) := by
    have hpi_ne : 4 * Real.pi^2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 Real.pi_ne_zero)
    have h_pull1 : ((kappa * c) / (4 * Real.pi^2)) / (2 * r^4) =
                   (((kappa * c) / (4 * Real.pi^2)) * (4 * Real.pi^2)) / (2 * r^4 * (4 * Real.pi^2)) := by
      have hs : ((kappa * c) / (4 * Real.pi^2)) / (2 * r^4) =
                (((kappa * c) / (4 * Real.pi^2)) / (2 * r^4)) * ((4 * Real.pi^2) / (4 * Real.pi^2)) := by
        have h_self : (4 * Real.pi^2) / (4 * Real.pi^2) = 1 := div_self hpi_ne
        rw [h_self, mul_one]
      have ht : (((kappa * c) / (4 * Real.pi^2)) / (2 * r^4)) * ((4 * Real.pi^2) / (4 * Real.pi^2)) =
                (((kappa * c) / (4 * Real.pi^2)) * (4 * Real.pi^2)) / (2 * r^4 * (4 * Real.pi^2)) := by ring
      rw [hs, ht]
    have h_pull2 : (((kappa * c) / (4 * Real.pi^2)) * (4 * Real.pi^2)) / (2 * r^4 * (4 * Real.pi^2)) =
                   ((kappa * c) * ((4 * Real.pi^2) / (4 * Real.pi^2))) / (2 * r^4 * (4 * Real.pi^2)) := by ring
    have h_pull3 : ((kappa * c) * ((4 * Real.pi^2) / (4 * Real.pi^2))) / (2 * r^4 * (4 * Real.pi^2)) =
                   (kappa * c) / (2 * r^4 * (4 * Real.pi^2)) := by rw [div_self hpi_ne, mul_one]
    have h_pull4 : (kappa * c) / (2 * r^4 * (4 * Real.pi^2)) = (kappa * c) / (8 * Real.pi^2 * r^4) := by
      have h_denom : 2 * r^4 * (4 * Real.pi^2) = 8 * Real.pi^2 * r^4 := by ring
      rw [h_denom]
    rw [h_pull1, h_pull2, h_pull3, h_pull4]
  rw [h6] at h4
  exact h4

-- ----------------------------------------------------------------------
-- 14.3 The Kinematic Mass Boundary (κ ≡ h)
-- ----------------------------------------------------------------------
variable (kappa r m : ℝ)

lemma action_constant_identity (hc : (0 : ℝ) < c) (hm : m > 0) (_hr : r > 0)
    (h_energy : m * c^2 = kappa * c / (2 * Real.pi * r))
    (h_radius : r = hbar / (m * c)) :
    kappa = 2 * Real.pi * hbar := by
  have h1 : m ≠ 0 := ne_of_gt hm
  have h2 : c ≠ 0 := ne_of_gt hc
  have h4 : Real.pi ≠ 0 := Real.pi_ne_zero
  have h_mc : m * c ≠ 0 := mul_ne_zero h1 h2
  have hr_ne : r ≠ 0 := ne_of_gt _hr
  have h_denom : 2 * Real.pi * r ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) h4) hr_ne
  have eq1a : (kappa * c / (2 * Real.pi * r)) * (2 * Real.pi * r) =
              (m * c^2) * (2 * Real.pi * r) := congrArg (· * (2 * Real.pi * r)) h_energy.symm
  have eq1b : (kappa * c / (2 * Real.pi * r)) * (2 * Real.pi * r) =
              (kappa * c) * ((2 * Real.pi * r) / (2 * Real.pi * r)) := by ring
  rw [eq1b, div_self h_denom, mul_one] at eq1a
  have eq2a : r * (m * c) = (hbar / (m * c)) * (m * c) := congrArg (· * (m * c)) h_radius
  have eq2b : (hbar / (m * c)) * (m * c) = hbar * ((m * c) / (m * c)) := by ring
  rw [eq2b, div_self h_mc, mul_one] at eq2a
  have eq3 : (m * c^2) * (2 * Real.pi * r) = (2 * Real.pi * (r * (m * c))) * c := by ring
  rw [eq3, eq2a] at eq1a
  have h_kappa_c2 : (kappa * c) / c = (2 * Real.pi * hbar * c) / c := congrArg (· / c) eq1a
  have h_final : kappa = 2 * Real.pi * hbar := by
    have h_L : (kappa * c) / c = kappa * (c / c) := by ring
    have h_R : (2 * Real.pi * hbar * c) / c = (2 * Real.pi * hbar) * (c / c) := by ring
    rw [h_L, h_R, div_self h2, mul_one, mul_one] at h_kappa_c2
    exact h_kappa_c2
  exact h_final

/-- Fundamental continuum force profile `F(r) = ℏ c / r^2` (Manuscript Section 14.3). -/
noncomputable def F_fund (r : ℝ) : ℝ := (hbar * c) / r^2

-- Theorem 94: The Fundamental Force Limit (F(r) = κ c / (2π r^2) = ℏ c / r^2, Manuscript Section 14.3)
theorem fundamental_force_limit (_hr : r ≠ 0)
    (h_kappa : kappa = 2 * Real.pi * hbar) :
    (kappa * c) / (2 * Real.pi * r^2) = F_fund r := by
  dsimp [F_fund]
  rw [h_kappa]
  have h1 : ((2 * Real.pi * hbar) * c) / (2 * Real.pi * r^2) =
            (2 * Real.pi * (hbar * c)) / (2 * Real.pi * r^2) := by ring
  have h_pi_ne : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have h2 : (2 * Real.pi * (hbar * c)) / (2 * Real.pi * r^2) = (hbar * c) / r^2 := by
    have h_pull : (2 * Real.pi * (hbar * c)) / (2 * Real.pi * r^2) =
                  ((hbar * c) / r^2) * ((2 * Real.pi) / (2 * Real.pi)) := by ring
    rw [h_pull, div_self h_pi_ne, mul_one]
  rw [h1, h2]

-- ----------------------------------------------------------------------
-- 14.4 The Interaction Hierarchy (Force Projections)
-- ----------------------------------------------------------------------
variable (m_W m_e alpha_em : ℝ)

-- Dimensional Audit: Gravity (c^4 / G), Weak/Strong/EM projections (m^2 c^3 / hbar), Horizon floor (F / m), and Newtonian gravity all match:
theorem unit_section14_interaction_hierarchy :
    (u_c^(4:ℤ)) / u_G = u_Force ∧
    ((u_M_P^(2:ℤ)) * (u_c^(3:ℤ))) / u_hbar = u_Force ∧
    u_Force / u_M_P = u_accel ∧
    (u_G * u_M_P * u_M_P) / (u_l_p^(2:ℤ)) = u_Force := by
  refine ⟨rfl, rfl, rfl, rfl⟩

-- Theorem 95: Interaction Hierarchy I — Gravity at the Planck Core Boundary (F(l_p) = c^4 / G, Manuscript Section 14.4.I)
theorem interaction_hierarchy_gravity : F_fund l_p = c^4 / G := by
  have hc : c ≠ 0 := ne_of_gt c_pos
  have hbar_ne : hbar ≠ 0 := ne_of_gt hbar_pos
  have hl_p : l_p ≠ 0 := ne_of_gt l_p_pos
  have hG_ne : G ≠ 0 := ne_of_gt G_pos
  dsimp [F_fund, G]
  field_simp

-- Theorem 96: Interaction Hierarchy II — The Weak Interaction (F(R_W) = m_W^2 c^3 / ℏ, Manuscript Section 14.4.II)
theorem interaction_hierarchy_weak (R_W : ℝ) (_hm_W : m_W ≠ 0)
    (h_R_W : R_W = hbar / (m_W * c)) :
    F_fund R_W = (m_W^2 * c^3) / hbar := by
  have hbar_ne : hbar ≠ 0 := ne_of_gt hbar_pos
  dsimp [F_fund]
  rw [h_R_W]
  have h_pow : (hbar / (m_W * c))^2 = hbar^2 / (m_W * c)^2 := div_pow _ _ _
  rw [h_pow]
  have h_pull : (hbar * c) / (hbar^2 / (m_W * c)^2) = (hbar * c * (m_W * c)^2) / hbar^2 :=
    div_div_eq_mul_div _ _ _
  rw [h_pull]
  have h_num : hbar * c * (m_W * c)^2 = hbar * (m_W^2 * c^3) := by ring
  have h_den : hbar^2 = hbar * hbar := by ring
  rw [h_num, h_den]
  have h_final : (hbar * (m_W^2 * c^3)) / (hbar * hbar) = ((m_W^2 * c^3) / hbar) * (hbar / hbar) := by ring
  rw [h_final, div_self hbar_ne, mul_one]

-- Theorem 97: Interaction Hierarchy III — The Strong Interaction (F(L_crit) = m_e^2 c^3 / (α^2 ℏ), Manuscript Section 14.4.III)
theorem interaction_hierarchy_strong (L_crit : ℝ) (_hm_e : m_e ≠ 0) (_h_alpha : alpha_em ≠ 0)
    (h_L_crit : L_crit = (alpha_em * hbar) / (m_e * c)) :
    F_fund L_crit = (m_e^2 * c^3) / (alpha_em^2 * hbar) := by
  have hbar_ne : hbar ≠ 0 := ne_of_gt hbar_pos
  dsimp [F_fund]
  rw [h_L_crit]
  have h_pow : ((alpha_em * hbar) / (m_e * c))^2 = (alpha_em * hbar)^2 / (m_e * c)^2 := div_pow _ _ _
  rw [h_pow]
  have h_pull : (hbar * c) / ((alpha_em * hbar)^2 / (m_e * c)^2) =
                (hbar * c * (m_e * c)^2) / (alpha_em * hbar)^2 := div_div_eq_mul_div _ _ _
  rw [h_pull]
  have h_num : hbar * c * (m_e * c)^2 = hbar * (m_e^2 * c^3) := by ring
  have h_den : (alpha_em * hbar)^2 = hbar * (alpha_em^2 * hbar) := by ring
  rw [h_num, h_den]
  have h_final : (hbar * (m_e^2 * c^3)) / (hbar * (alpha_em^2 * hbar)) =
                 ((m_e^2 * c^3) / (alpha_em^2 * hbar)) * (hbar / hbar) := by ring
  rw [h_final, div_self hbar_ne, mul_one]

-- Theorem 98: Interaction Hierarchy IV — Electromagnetism at the Bohr Radius & α^4 Strong Ratio
-- (Resolves Issues #27 & #49, Manuscript Section 14.4.IV)
theorem interaction_hierarchy_em (a_0_val L_crit : ℝ) (hm_e : m_e ≠ 0) (h_alpha : alpha_em ≠ 0)
    (h_a_0 : a_0_val = hbar / (alpha_em * m_e * c))
    (h_L_crit : L_crit = (alpha_em * hbar) / (m_e * c)) :
    F_fund a_0_val = (alpha_em^2 * m_e^2 * c^3) / hbar ∧
    alpha_em * F_fund a_0_val = (alpha_em^3 * m_e^2 * c^3) / hbar ∧
    F_fund a_0_val / F_fund L_crit = alpha_em^4 := by
  have hbar_ne : hbar ≠ 0 := ne_of_gt hbar_pos
  have hc_ne : c ≠ 0 := c_ne_zero
  have h_em_base : F_fund a_0_val = (alpha_em^2 * m_e^2 * c^3) / hbar := by
    dsimp [F_fund]
    rw [h_a_0]
    field_simp

  have h_strong : F_fund L_crit = (m_e^2 * c^3) / (alpha_em^2 * hbar) :=
    interaction_hierarchy_strong m_e alpha_em L_crit hm_e h_alpha h_L_crit
  refine ⟨h_em_base, ?_, ?_⟩
  · rw [h_em_base]
    ring
  · rw [h_em_base, h_strong]
    field_simp

-- ----------------------------------------------------------------------
-- 14.5 The Macroscopic Baseline (The Horizon Floor)
-- ----------------------------------------------------------------------
variable (F_R_h m_h h_val R_h_0 : ℝ)

-- Theorem 99: Kinematic Horizon Acceleration Floor (a_0 = c^2 / (2π R_{h,0}), Manuscript Section 14.5)
theorem kinematic_acceleration_floor (hR_ne : R_h_0 > 0) (hh_ne : h_val > 0)
    (h_a0 : a_0 = F_R_h / m_h)
    (h_F : F_R_h = (h_val * c) / (2 * Real.pi * R_h_0^2))
    (h_m : m_h = h_val / (R_h_0 * c)) :
    a_0 = c^2 / (2 * Real.pi * R_h_0) := by
  have h1 : R_h_0 ≠ 0 := ne_of_gt hR_ne
  have h2 : h_val ≠ 0 := ne_of_gt hh_ne
  have h3 : c ≠ 0 := ne_of_gt c_pos
  have h4 : Real.pi ≠ 0 := Real.pi_ne_zero
  have eq_m1 : m_h * (R_h_0 * c) = (h_val / (R_h_0 * c)) * (R_h_0 * c) := congrArg (· * (R_h_0 * c)) h_m
  have eq_m2 : (h_val / (R_h_0 * c)) * (R_h_0 * c) = h_val * ((R_h_0 * c) / (R_h_0 * c)) := by ring
  rw [eq_m2, div_self (mul_ne_zero h1 h3), mul_one] at eq_m1
  have eq_F1 : F_R_h * (2 * Real.pi * R_h_0^2) =
               ((h_val * c) / (2 * Real.pi * R_h_0^2)) * (2 * Real.pi * R_h_0^2) :=
    congrArg (· * (2 * Real.pi * R_h_0^2)) h_F
  have eq_F2 : ((h_val * c) / (2 * Real.pi * R_h_0^2)) * (2 * Real.pi * R_h_0^2) =
               (h_val * c) * ((2 * Real.pi * R_h_0^2) / (2 * Real.pi * R_h_0^2)) := by ring
  rw [eq_F2, div_self (mul_ne_zero (mul_ne_zero (by norm_num) h4) (pow_ne_zero 2 h1)), mul_one] at eq_F1
  have h7 : m_h ≠ 0 := by
    intro hz
    have h_bad : 0 * (R_h_0 * c) = h_val := by rw [←eq_m1, hz]
    rw [zero_mul] at h_bad
    exact h2 h_bad.symm
  have eq_a1 : a_0 * m_h = (F_R_h / m_h) * m_h := congrArg (· * m_h) h_a0
  have eq_a2 : (F_R_h / m_h) * m_h = F_R_h * (m_h / m_h) := by ring
  rw [eq_a2, div_self h7, mul_one] at eq_a1
  have eqA1 : a_0 * m_h * (2 * Real.pi * R_h_0^2) = F_R_h * (2 * Real.pi * R_h_0^2) :=
    congrArg (· * (2 * Real.pi * R_h_0^2)) eq_a1
  rw [eq_F1] at eqA1
  have eqB1 : m_h * (R_h_0 * c) * c = h_val * c := congrArg (· * c) eq_m1
  have eqB2 : a_0 * m_h * (2 * Real.pi * R_h_0^2) = m_h * (R_h_0 * c) * c := by rw [eqA1, ←eqB1]
  have eqC1 : (a_0 * m_h * (2 * Real.pi * R_h_0^2)) / m_h = (m_h * (R_h_0 * c) * c) / m_h :=
    congrArg (· / m_h) eqB2
  have eqC2 : (a_0 * m_h * (2 * Real.pi * R_h_0^2)) / m_h = a_0 * (2 * Real.pi * R_h_0^2) * (m_h / m_h) := by ring
  have eqC3 : (m_h * (R_h_0 * c) * c) / m_h = ((R_h_0 * c) * c) * (m_h / m_h) := by ring
  rw [eqC2, eqC3, div_self h7, mul_one, mul_one] at eqC1
  have eqD1 : a_0 * (2 * Real.pi * R_h_0) * R_h_0 = a_0 * (2 * Real.pi * R_h_0^2) := by ring
  have eqD2 : c^2 * R_h_0 = (R_h_0 * c) * c := by ring
  have eqD3 : a_0 * (2 * Real.pi * R_h_0) * R_h_0 = c^2 * R_h_0 := by rw [eqD1, eqC1, ←eqD2]
  have eqE1 : (a_0 * (2 * Real.pi * R_h_0) * R_h_0) / R_h_0 = (c^2 * R_h_0) / R_h_0 :=
    congrArg (· / R_h_0) eqD3
  have eqE2 : (a_0 * (2 * Real.pi * R_h_0) * R_h_0) / R_h_0 = a_0 * (2 * Real.pi * R_h_0) * (R_h_0 / R_h_0) := by ring
  have eqE3 : (c^2 * R_h_0) / R_h_0 = c^2 * (R_h_0 / R_h_0) := by ring
  rw [eqE2, eqE3, div_self h1, mul_one, mul_one] at eqE1
  have h_pi_R : 2 * Real.pi * R_h_0 ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) h4) h1
  calc a_0 = a_0 * ((2 * Real.pi * R_h_0) / (2 * Real.pi * R_h_0)) := by rw [div_self h_pi_R, mul_one]
    _ = (a_0 * (2 * Real.pi * R_h_0)) / (2 * Real.pi * R_h_0) := by ring
    _ = c^2 / (2 * Real.pi * R_h_0) := by rw [eqE1]

-- ----------------------------------------------------------------------
-- 14.6 Macroscopic Combinatorial Aggregates (Newtonian Gravity)
-- ----------------------------------------------------------------------
variable (F_macro M_1 M_2 M_P_val : ℝ)

-- Theorem 100: Derivation of Universal Gravitation (F_macro = G M_1 M_2 / r^2, Manuscript Section 14.6)
theorem universal_gravitation_limit (hM_P : M_P_val > 0) (_hr : r > 0) (hG : G > 0)
    (h_F_macro : F_macro = (M_1 / M_P_val) * (M_2 / M_P_val) * ((hbar * c) / r^2))
    (h_M_P_sq : M_P_val^2 = (hbar * c) / G) :
    F_macro = (G * M_1 * M_2) / r^2 := by
  have hG_ne : G ≠ 0 := ne_of_gt hG
  have hM_P_ne : M_P_val ≠ 0 := ne_of_gt hM_P
  have eq1a : M_P_val^2 * G = ((hbar * c) / G) * G := congrArg (· * G) h_M_P_sq
  have eq1b : ((hbar * c) / G) * G = (hbar * c) * (G / G) := by ring
  rw [eq1b, div_self hG_ne, mul_one] at eq1a
  have step1 : F_macro = ((M_1 * M_2) / M_P_val^2) * ((hbar * c) / r^2) := by
    have h_sub : (M_1 / M_P_val) * (M_2 / M_P_val) = (M_1 * M_2) / M_P_val^2 := by ring
    rw [h_F_macro, h_sub]
  have step2 : ((M_1 * M_2) / M_P_val^2) * ((hbar * c) / r^2) = (M_1 * M_2 * (hbar * c)) / (M_P_val^2 * r^2) := by ring
  rw [step2] at step1
  have step3 : (M_1 * M_2 * (hbar * c)) / (M_P_val^2 * r^2) =
               (M_1 * M_2 * (M_P_val^2 * G)) / (M_P_val^2 * r^2) := by rw [←eq1a]
  rw [step3] at step1
  have step4 : (M_1 * M_2 * (M_P_val^2 * G)) / (M_P_val^2 * r^2) =
               (M_P_val^2 * (G * M_1 * M_2)) / (M_P_val^2 * r^2) := by ring
  rw [step4] at step1
  have step5 : (M_P_val^2 * (G * M_1 * M_2)) / (M_P_val^2 * r^2) =
               ((G * M_1 * M_2) / r^2) * (M_P_val^2 / M_P_val^2) := by ring
  rw [step5] at step1
  have step6 : ((G * M_1 * M_2) / r^2) * (M_P_val^2 / M_P_val^2) =
               ((G * M_1 * M_2) / r^2) * 1 := by rw [div_self (pow_ne_zero 2 hM_P_ne)]
  rw [step6, mul_one] at step1
  exact step1

end AsymmetricTensor
