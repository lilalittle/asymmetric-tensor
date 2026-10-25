/-
Copyright (c) 2026 Binyamin Tsadik Bair-Mosheh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Binyamin Tsadik Bair-Mosheh
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Tactic
public import AsymmetricTensor.Model
public import AsymmetricTensor.MatrixAlgebra

/-!
# Mass mechanism (topological tensor yield)

Module of Binyamin's v5.8 formalization. Declarations retained verbatim
from the author's single-file development.
-/

@[expose] public section

open Real BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars true

namespace AsymmetricTensor
-- ======================================================================
-- SECTION 8: THE MASS MECHANISM (TOPOLOGICAL TENSOR YIELD)
-- ======================================================================

-- ----------------------------------------------------------------------
-- 8.1 The Tensor Yield Criterion (The VEV Origin) (Manuscript Eqs. 113–118)
-- ----------------------------------------------------------------------
variable (S_ii P_static P_dyn_val v_val : ℝ)
variable (v_vev P_ambient : ℝ)

-- Dimensional Audit: VEV squared velocity (2 P_ambient / rho_tau = v_vev^2) and Lagrangian density (P_c * dimensionless = P_c):
theorem unit_section8_vev_and_lagrangian :
    u_P_c / u_rho_tau = u_c^(2:ℤ) ∧
    u_P_c * u_dimless = u_P_c := by
  constructor <;> rfl

-- Theorem 48: Spatial Diagonal Lorentz Compliance Expansion (S_ii = 1 / (1 - v^2/c^2), Manuscript Eq. 115)
lemma spatial_diagonal_lorentz_derivation
    (h_S_ii : S_ii = P_c / P_static)
    (h_Bernoulli : P_static = P_c - P_dyn_val)
    (h_P_dyn : P_dyn_val = (1 / 2) * rho_tau * v_val^2) :
    S_ii = 1 / (1 - v_val^2 / c^2) := by
  have hc2 : c^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt c_pos)
  have h_Pc_sub : P_c = (1 / 2) * rho_tau * c^2 := emergent_critical_pressure
  rw [h_S_ii, h_Bernoulli, h_Pc_sub, h_P_dyn]
  have hX : (1 / 2) * rho_tau ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt rho_tau_pos)
  have h_num : (1 / 2) * rho_tau * c^2 = ((1 / 2) * rho_tau) * c^2 := by ring
  have h_den : (1 / 2) * rho_tau * c^2 - (1 / 2) * rho_tau * v_val^2 = ((1 / 2) * rho_tau) * (c^2 - v_val^2) := by ring
  rw [h_num, h_den]
  have h_cancel : (((1 / 2) * rho_tau) * c^2) / (((1 / 2) * rho_tau) * (c^2 - v_val^2)) = c^2 / (c^2 - v_val^2) := by
    rw [mul_div_mul_left]
    exact hX
  rw [h_cancel]
  have h_den2 : c^2 - v_val^2 = c^2 * (1 - v_val^2 / c^2) := by
    have hs1 : c^2 * (1 - v_val^2 / c^2) = c^2 * 1 - c^2 * (v_val^2 / c^2) := by ring
    have hs2 : c^2 * (v_val^2 / c^2) = (c^2 / c^2) * v_val^2 := by ring
    rw [hs1, hs2, div_self hc2, one_mul, mul_one]
  rw [h_den2]
  have h_top : c^2 = c^2 * 1 := by ring
  nth_rw 1 [h_top]
  have h_final : (c^2 * 1) / (c^2 * (1 - v_val^2 / c^2)) = 1 / (1 - v_val^2 / c^2) := by
    rw [mul_div_mul_left]
    exact hc2
  rw [h_final]

-- Theorem 49: Vacuum Expectation Value Origin (v_vev^2 = 2 P_ambient / ρ_τ, Manuscript Eq. 117)
theorem tensor_vev_origin
    (h_yield : P_ambient = (1 / 2) * rho_tau * v_vev^2) :
    v_vev^2 = 2 * P_ambient / rho_tau := by
  have hrho : rho_tau ≠ 0 := ne_of_gt rho_tau_pos
  have h1 : 2 * P_ambient = rho_tau * v_vev^2 := by linarith
  have h2 : v_vev^2 = (rho_tau * v_vev^2) / rho_tau := by
    have h_c : (rho_tau * v_vev^2) / rho_tau = v_vev^2 * (rho_tau / rho_tau) := by ring
    rw [h_c, div_self hrho, mul_one]
  rw [h2, ←h1]

-- ----------------------------------------------------------------------
-- 8.2 The Topological Phase Lock (Mass Generation) (Manuscript Eq. 119)
-- ----------------------------------------------------------------------

-- Dimensional Audit: Phase-locked shear energy (P_c * V_τ) has dimension u_Energy,
-- and dividing by c^2 extracts discrete rest mass (u_M_P = ⟨2, -2, 1⟩):
theorem unit_section8_2_phase_lock :
    u_P_c * u_Volume = u_Energy ∧
    (u_P_c * u_Volume) / (u_c^(2:ℤ)) = u_M_P ∧
    (u_P_c / (u_c^(2:ℤ))) * u_Volume = u_M_P := by
  refine ⟨rfl, rfl, rfl⟩

-- Theorem 155: Topological Phase-Lock Cavitation Transition & `α_s`-Independent Vortex Core (Issues
-- #12 & #22)
-- Proves without instantiating `U_hat` spatial diagonals at `0`:
-- 1. Antisymmetric Sector Independence: `U_anti` is independent of `α_s` across all 16 entries
--    (`U_anti α_s ... i j = U_anti 1 ... i j`), so the Clebsch vortex core never divides by `α_s`,
-- 2. Cavitation Limit (`α_s = 0`): Temporal admittance vanishes (`U_hat(0,0) = 0`, `P_static = 0`),
-- while the antisymmetric Clebsch vortex off-diagonal `U_anti(2,1) = α t_p Ω_z` locks `P_dyn +
-- P_shear = P_c`.

theorem topological_phase_lock_cavitation
    (alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4)
    (t_p_val P_static P_dyn P_shear alpha_s : ℝ)
    (h_ledger : P_c = P_static + P_dyn + P_shear)
    (h_stat_admittance : P_static = alpha_s^2 * P_c)
    (h_cavitation : alpha_s = 0) :
    (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 0 0 = 0 ∧
    (∀ (as_ any_s : ℝ) (i j : Fin 4),
      U_anti as_ alpha v_x v_y v_z d_lambda d_beta t_p_val i j =
      U_anti any_s alpha v_x v_y v_z d_lambda d_beta t_p_val i j) ∧
    (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 2 1 =
      alpha * (t_p_val * Omega_z_clebsch d_lambda d_beta) ∧
    P_static = 0 ∧
    P_dyn + P_shear = P_c := by
  have h_stat_zero : P_static = 0 := by
    rw [h_stat_admittance, h_cavitation]
    ring
  refine ⟨?_, ?_, ?_, h_stat_zero, ?_⟩
  · dsimp [U_hat, Matrix.of_apply]
    rw [h_cavitation]
    norm_num
  · intro as_ any_s i j
    fin_cases i <;> fin_cases j <;>
      dsimp [U_anti, antiPart, U_hat, Matrix.of_apply] <;> ring
  · dsimp [U_anti, antiPart, U_hat, Matrix.of_apply]
    norm_num
  · linarith

-- Theorem 177: Constitutive Frobenius Shear Load vs. Lorentzian Action Normalization (Resolves Issue #10)
theorem frobenius_vs_lorentzian_shear_bridge
    (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) :
    (1 / 4) * P_c * tensor_contract
      (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)
      (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) =
    (1 / 2) * P_c * alpha^2 *
      ((v_x^2 + v_y^2 + v_z^2) / c^2 +
       t_p_val^2 * ((Omega_x_clebsch d_lambda d_beta)^2 +
                    (Omega_y_clebsch d_lambda d_beta)^2 +
                    (Omega_z_clebsch d_lambda d_beta)^2)) ∧
    (1 / 4) * P_c * lorentzian_contract
      (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)
      (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) =
    (1 / 2) * P_c * alpha^2 *
      (t_p_val^2 * ((Omega_x_clebsch d_lambda d_beta)^2 +
                    (Omega_y_clebsch d_lambda d_beta)^2 +
                    (Omega_z_clebsch d_lambda d_beta)^2) -
       (v_x^2 + v_y^2 + v_z^2) / c^2) := by
  refine ⟨?_, ?_⟩
  · dsimp [tensor_contract, U_anti, antiPart, U_hat, Matrix.of_apply]
    norm_num
    ring
  · dsimp [lorentzian_contract, U_anti, antiPart, U_hat, Matrix.of_apply]
    norm_num
    ring

-- Theorem 156a: Phase-Locked Frobenius Shear Rest Mass & Strict Positivity (Manuscript Section 8.2,
-- Part 1)
-- Proves:
-- 1. Frobenius Shear Mass Formula: From `P_shear = (1 / 2) * P_c * alpha^2 * (v_perp^2 / c^2 +
-- t_p^2 * Omega^2)`,
--    `E_locked = P_shear * V_tau`, and `m_0 = E_locked / c^2`, the invariant rest mass evaluates to
--    `m_0 = (rho_tau * V_tau * alpha^2 / 4) * (v_perp^2 / c^2 + t_p^2 * Omega^2)`,
-- 2. Strict Positivity: For `0 < V_tau`, `alpha ≠ 0`, and non-vanishing Clebsch vorticity
-- `Omega_z_clebsch d_lambda d_beta ≠ 0`, the generated rest mass is strictly positive (`0 < m_0`).
theorem phase_locked_frobenius_rest_mass_pos
    (d_lambda d_beta : V4) (alpha v_perp V_tau P_shear E_locked m_0 : ℝ)
    (hV : 0 < V_tau) (h_alpha_ne : alpha ≠ 0)
    (h_omega_ne : Omega_z_clebsch d_lambda d_beta ≠ 0)
    (h_P_shear : P_shear = (1 / 2) * P_c * alpha^2 *
      (v_perp^2 / c^2 + t_p^2 * (Omega_z_clebsch d_lambda d_beta)^2))
    (h_E_locked : E_locked = P_shear * V_tau)
    (h_mass : m_0 = E_locked / c^2) :
    m_0 = (rho_tau * V_tau * alpha^2 / 4) *
      (v_perp^2 / c^2 + t_p^2 * (Omega_z_clebsch d_lambda d_beta)^2) ∧
    0 < m_0 := by
  have hc_pos : 0 < c := c_pos
  have hc_ne : c ≠ 0 := c_ne_zero
  have hrho_pos : 0 < rho_tau := rho_tau_pos
  have h_tp_pos : 0 < t_p := by
    dsimp [t_p]
    exact div_pos l_p_pos c_pos
  have h_m0_frob : m_0 = (rho_tau * V_tau * alpha^2 / 4) *
      (v_perp^2 / c^2 + t_p^2 * (Omega_z_clebsch d_lambda d_beta)^2) := by
    rw [h_mass, h_E_locked, h_P_shear]
    dsimp [P_c]
    calc (1 / 2 * (1 / 2 * rho_tau * c^2) * alpha^2 *
          (v_perp^2 / c^2 + t_p^2 * (Omega_z_clebsch d_lambda d_beta)^2) * V_tau) / c^2
      _ = ((rho_tau * V_tau * alpha^2 / 4) *
          (v_perp^2 / c^2 + t_p^2 * (Omega_z_clebsch d_lambda d_beta)^2) * c^2) / c^2 := by ring
      _ = (rho_tau * V_tau * alpha^2 / 4) *
          (v_perp^2 / c^2 + t_p^2 * (Omega_z_clebsch d_lambda d_beta)^2) :=
        mul_div_cancel_right₀ _ (pow_ne_zero 2 hc_ne)
  have h_alpha_sq : 0 < alpha^2 := sq_pos_of_ne_zero h_alpha_ne
  have h_om_sq : 0 < (Omega_z_clebsch d_lambda d_beta)^2 := sq_pos_of_ne_zero h_omega_ne
  have h_term2_pos : 0 < t_p^2 * (Omega_z_clebsch d_lambda d_beta)^2 := by positivity
  have h_term1_nonneg : 0 ≤ v_perp^2 / c^2 := by positivity
  have h_sum_pos : 0 < v_perp^2 / c^2 + t_p^2 * (Omega_z_clebsch d_lambda d_beta)^2 := by linarith
  have h_pref_pos : 0 < rho_tau * V_tau * alpha^2 / 4 := by positivity
  refine ⟨h_m0_frob, ?_⟩
  rw [h_m0_frob]
  exact mul_pos h_pref_pos h_sum_pos

-- Theorem 156b: Tangential Phase-Lock (`v_vortex = r_c * Omega = c`) & Vortex Core Equivalence
-- (Manuscript Section 8.2, Part 2)
-- Proves:
-- 1. Tangential Phase-Lock: Deflecting the core velocity into tangential circulation at the
-- cavitation
-- radius (`v_vortex = r_c_val * Omega`) equates the Bernoulli dynamic pressure to the vortex core
-- energy density `P_vortex = (1 / 2) * rho_tau * (r_c_val * Omega)^2 = (1 / 2) * rho_tau *
-- v_vortex^2`,
-- 2. Equipartition Boundary Matching: Under `2 * r_c_val^2 * Omega^2 = alpha^2 * (v_perp^2 + c^2 *
-- t_p^2 * Omega^2)`,
--    the tangential vortex pressure equals the Frobenius shear pressure (`P_vortex = P_shear`),
-- 3. Universal Cavitation Speed (`v_vortex = c`): At `r_c_val * Omega = c`, `P_vortex = P_c` and
-- the
-- rest mass simplifies from `m_0 = (1 / 2) * rho_tau * V_tau * ((r_c_val * Omega) / c)^2` to `(1 /
-- 2) * rho_tau * V_tau`.
theorem tangential_phase_lock_vortex_equivalence
    (d_lambda d_beta : V4) (alpha v_vortex v_perp r_c_val V_tau P_shear P_vortex E_locked m_0 : ℝ)
    (h_v_lock : v_vortex = r_c_val * Omega_z_clebsch d_lambda d_beta)
    (h_cav_c : r_c_val * Omega_z_clebsch d_lambda d_beta = c)
    (h_P_shear : P_shear = (1 / 2) * P_c * alpha^2 *
      (v_perp^2 / c^2 + t_p^2 * (Omega_z_clebsch d_lambda d_beta)^2))
    (h_P_vortex : P_vortex = (1 / 2) * rho_tau * (r_c_val * Omega_z_clebsch d_lambda d_beta)^2)
    (h_match : 2 * r_c_val^2 * (Omega_z_clebsch d_lambda d_beta)^2 =
      alpha^2 * (v_perp^2 + c^2 * t_p^2 * (Omega_z_clebsch d_lambda d_beta)^2))
    (h_E_locked : E_locked = P_shear * V_tau)
    (h_mass : m_0 = E_locked / c^2) :
    P_vortex = (1 / 2) * rho_tau * v_vortex^2 ∧
    P_vortex = P_shear ∧
    P_vortex = P_c ∧
    m_0 = (1 / 2) * rho_tau * V_tau * ((r_c_val * Omega_z_clebsch d_lambda d_beta) / c)^2 ∧
    m_0 = (1 / 2) * rho_tau * V_tau := by
  have hc_ne : c ≠ 0 := c_ne_zero
  have h_pv_v0 : P_vortex = (1 / 2) * rho_tau * v_vortex^2 := by
    rw [h_P_vortex, ← h_v_lock]
  have h_pv_eq_ps : P_vortex = P_shear := by
    rw [h_P_vortex, h_P_shear]
    dsimp [P_c]
    have h_rhs : 1 / 2 * (1 / 2 * rho_tau * c^2) * alpha^2 *
        (v_perp^2 / c^2 + t_p^2 * (Omega_z_clebsch d_lambda d_beta)^2) =
        (1 / 4 * rho_tau) * (alpha^2 * ((v_perp^2 / c^2) * c^2 + c^2 * t_p^2 * (Omega_z_clebsch
          d_lambda d_beta)^2)) := by
      ring
    rw [h_rhs, div_mul_cancel₀ _ (pow_ne_zero 2 hc_ne), ← h_match]
    ring
  have h_pv_pc : P_vortex = P_c := by
    rw [h_P_vortex, h_cav_c]
    rfl
  have h_m0_rc : m_0 = (1 / 2) * rho_tau * V_tau *
      ((r_c_val * Omega_z_clebsch d_lambda d_beta) / c)^2 := by
    rw [h_mass, h_E_locked, ← h_pv_eq_ps, h_P_vortex]
    ring
  refine ⟨h_pv_v0, h_pv_eq_ps, h_pv_pc, h_m0_rc, ?_⟩
  rw [h_m0_rc, h_cav_c, div_self hc_ne]
  ring

-- Theorem 156c: The Micro–Macro Horizon Duality (`r_c * Omega_core = c ↔ R_h * H_0 = R_h *
-- Omega_max = c`)
-- (Manuscript Section 8.2 Table Equivalence & Section 11.6 Galactic Capture)
theorem micro_macro_horizon_duality
    (r_c m_0 Omega_core R_h H_0 R_max v_rot Omega_max a_0 r : ℝ)
    (h_rc_ne : r_c ≠ 0) (h_Rh_ne : R_h ≠ 0) (h_Rmax_ne : R_max ≠ 0)
    (h_rc_def : r_c = hbar / (m_0 * c))
    (h_om_core : Omega_core = c / r_c)
    (h_H0_def : H_0 = c / R_h)
    (h_capture : v_rot = H_0 * R_max)
    (h_om_max : Omega_max = v_rot / R_max)
    (h_a0 : a_0 = (c * H_0) / (2 * Real.pi)) :
    u_c / u_l_p = u_omega ∧
    r_c * Omega_core = c ∧
    Omega_core = (m_0 * c^2) / hbar ∧
    (1 - ((r_c * Omega_core) / c)^2) * P_c = 0 ∧
    Omega_max = H_0 ∧
    R_h * Omega_max = c ∧
    R_h * H_0 = c ∧
    r_c * Omega_core = R_h * Omega_max ∧
    a_0 = c^2 / (2 * Real.pi * R_h) ∧
    (R_h * Omega_max) * (1 - Real.exp (-r / R_h)) = c * (1 - Real.exp (-r / R_h)) := by
  have hc_ne : c ≠ 0 := c_ne_zero
  have h_inner_lock : r_c * Omega_core = c := by
    rw [h_om_core, mul_div_cancel₀ _ h_rc_ne]
  have h_compton_freq : Omega_core = (m_0 * c^2) / hbar := by
    rw [h_om_core, h_rc_def, div_div_eq_mul_div]
    ring
  have h_pstatic_zero : (1 - ((r_c * Omega_core) / c)^2) * P_c = 0 := by
    rw [h_inner_lock, div_self hc_ne]
    ring
  have h_om_eq_H0 : Omega_max = H_0 := by
    rw [h_om_max, h_capture, mul_div_cancel_right₀ _ h_Rmax_ne]
  have h_outer_H0 : R_h * H_0 = c := by
    rw [h_H0_def, mul_div_cancel₀ _ h_Rh_ne]
  have h_outer_max : R_h * Omega_max = c := by
    rw [h_om_eq_H0, h_outer_H0]
  have h_duality : r_c * Omega_core = R_h * Omega_max := by
    rw [h_inner_lock, h_outer_max]
  have h_a0_eq : a_0 = c^2 / (2 * Real.pi * R_h) := by
    rw [h_a0, h_H0_def]
    ring
  refine ⟨rfl, h_inner_lock, h_compton_freq, h_pstatic_zero, h_om_eq_H0,
          h_outer_max, h_outer_H0, h_duality, h_a0_eq, ?_⟩
  rw [h_outer_max]

-- ----------------------------------------------------------------------
-- 8.3 The Kinematic Lagrangian & Orthogonal Mass Extraction (Manuscript Eqs. 120–126)
-- ----------------------------------------------------------------------
variable (L_kin P_shear_val A_anti_trace : ℝ)
variable (v_macro_scalar : ℝ)

/-- Positive-definite Frobenius norm of `U_anti`, quantifying the stored transverse Clebsch shear load `P_shear` (Manuscript Eq. 125). -/
noncomputable def P_shear_hamiltonian (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) : ℝ :=
  (1 / 4) * P_c * tensor_contract
    (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)
    (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)

lemma tensor_contract_self_nonneg (A : T2) : 0 ≤ tensor_contract A A := by
  have h_sq : tensor_contract A A =
    (A 0 0)^2 + (A 0 1)^2 + (A 0 2)^2 + (A 0 3)^2 +
    (A 1 0)^2 + (A 1 1)^2 + (A 1 2)^2 + (A 1 3)^2 +
    (A 2 0)^2 + (A 2 1)^2 + (A 2 2)^2 + (A 2 3)^2 +
    (A 3 0)^2 + (A 3 1)^2 + (A 3 2)^2 + (A 3 3)^2 := by
    dsimp [tensor_contract]
    ring
  rw [h_sq]
  positivity

-- Theorem 50: Nonnegativity of Stored Frobenius Shear Load (P_shear ≥ 0, Manuscript Eq. 125)
theorem P_shear_hamiltonian_nonneg (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) :
    0 ≤ P_shear_hamiltonian alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val := by
  dsimp [P_shear_hamiltonian]
  have hPc : 0 < P_c := P_c_pos
  have h_frob : 0 ≤ tensor_contract
    (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)
    (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) :=
    tensor_contract_self_nonneg _
  positivity

theorem P_shear_pure_electric_limit (alpha_s alpha v_x t_p_val : ℝ) :
    P_shear_hamiltonian alpha_s alpha v_x 0 0 0 0 t_p_val =
    (1 / 2) * P_c * alpha^2 * (v_x / c)^2 := by
  have h_anti : tensor_contract
      (U_anti alpha_s alpha v_x 0 0 0 0 t_p_val)
      (U_anti alpha_s alpha v_x 0 0 0 0 t_p_val) =
      2 * alpha^2 * (v_x / c)^2 := by
    dsimp [tensor_contract, U_anti, antiPart, U_hat, Omega_x_clebsch, Omega_y_clebsch,
           Omega_z_clebsch, omega_clebsch_2form, wedge_covec, Matrix.of_apply]
    norm_num
    ring
  dsimp [P_shear_hamiltonian]
  rw [h_anti]
  ring

-- Theorem 51: Kinematic Lagrangian Trace Decomposition (L_kin = P_dyn + L_shear, Manuscript Eq. 124)
theorem orthogonal_mass_extraction
    (h_L_kin : L_kin = (1 / 4) * P_c * (4 * (v_macro_scalar^2 / c^2) + A_anti_trace))
    (h_P_dyn : P_dyn_val = (1 / 2) * rho_tau * v_macro_scalar^2)
    (h_P_shear : P_shear_val = (1 / 4) * P_c * A_anti_trace) :
    L_kin = P_dyn_val + P_shear_val := by
  have hc2 : c^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt c_pos)
  have h_Pc_sub : P_c = (1 / 2) * rho_tau * c^2 := emergent_critical_pressure
  have h1 : L_kin = (1 / 4) * P_c * (4 * (v_macro_scalar^2 / c^2)) + (1 / 4) * P_c * A_anti_trace := by
    rw [h_L_kin]; ring
  rw [h1, ←h_P_shear, h_Pc_sub]
  have h2 : (1 / 4) * ((1 / 2) * rho_tau * c^2) * (4 * (v_macro_scalar^2 / c^2)) =
            ((1 / 2) * rho_tau * v_macro_scalar^2 * c^2) / c^2 := by ring
  rw [h2]
  have h3 : ((1 / 2) * rho_tau * v_macro_scalar^2 * c^2) / c^2 =
            ((1 / 2) * rho_tau * v_macro_scalar^2) * (c^2 / c^2) := by ring
  rw [h3, div_self hc2, mul_one, ←h_P_dyn]

-- ----------------------------------------------------------------------
-- 8.4 The Topological Yield Transition (Planck Mass) (Manuscript Eqs. 127–129)
-- ----------------------------------------------------------------------
variable (M_val : ℝ)

-- Dimensional Audit: Compton radius (hbar / M c) and Schwarzschild radius (2 G M / c^2) both evaluate to Length ⟨-1, 0, 0⟩:
theorem unit_section8_compton_schwarzschild_intersection :
    u_hbar / (u_M_P * u_c) = u_l_p ∧
    (u_G * u_M_P) / (u_c^(2:ℤ)) = u_l_p ∧
    (u_M_P / u_M_P)^(2:ℤ) = u_dimless := by
  refine ⟨rfl, rfl, rfl⟩

lemma isolate_planck_yield_algebra (m_var : ℝ) (hm : m_var ≠ 0) :
  hbar / (m_var * c) = 2 * G * m_var / c^2 →
  m_var^2 = (M_P)^2 / 2 := by
  intro h_int
  have c_ne_zero : c ≠ 0 := ne_of_gt c_pos
  have hc2 : c^2 ≠ 0 := pow_ne_zero 2 c_ne_zero
  have G_ne_zero : G ≠ 0 := ne_of_gt G_pos
  have h_Mp : (M_P)^2 = hbar * c / G := M_P_sq_eq_hbar_c_div_G
  have h1 : (hbar / (m_var * c)) * (m_var * c) = (2 * G * m_var / c^2) * (m_var * c) := by rw [h_int]
  have hmc : m_var * c ≠ 0 := mul_ne_zero hm c_ne_zero
  have h2_part1 : (hbar / (m_var * c)) * (m_var * c) = hbar * ((m_var * c) / (m_var * c)) := by ring
  rw [h2_part1, div_self hmc, mul_one] at h1
  have h2_part2 : (2 * G * m_var / c^2) * (m_var * c) = (2 * G * m_var^2 * c) / (c * c) := by ring
  rw [h2_part2] at h1
  have h2_part3 : (2 * G * m_var^2 * c) / (c * c) = ((2 * G * m_var^2) / c) * (c / c) := by ring
  rw [h2_part3, div_self c_ne_zero, mul_one] at h1
  have h3_part1 : hbar * c / G = ((2 * G * m_var^2) / c) * c / G := by rw [←h1]
  have h3_part2 : ((2 * G * m_var^2) / c) * c = (2 * G * m_var^2) * (c / c) := by ring
  rw [h3_part2, div_self c_ne_zero, mul_one] at h3_part1
  have h3_part3 : (2 * G * m_var^2) / G = (2 * m_var^2) * (G / G) := by ring
  rw [h3_part3, div_self G_ne_zero, mul_one] at h3_part1
  have h4 : m_var^2 = (2 * m_var^2) / 2 := by ring
  rw [h4, ←h3_part1, ←h_Mp]

lemma positive_sqrt_reduction (m_var : ℝ) (hm_pos : m_var > 0) :
  m_var^2 = (M_P)^2 / 2 → m_var = M_P / Real.sqrt 2 := by
  intro h
  have h_pos : 0 ≤ M_P^2 := sq_nonneg M_P
  have h2 : Real.sqrt (m_var^2) = Real.sqrt ((M_P)^2 / 2) := by rw [h]
  rw [Real.sqrt_sq (le_of_lt hm_pos)] at h2
  have h_split : Real.sqrt ((M_P)^2 / 2) = Real.sqrt ((M_P)^2) / Real.sqrt 2 := by rw [Real.sqrt_div h_pos]
  rw [h_split] at h2
  have hMp_nonneg : 0 ≤ M_P := le_of_lt M_P_pos
  rw [Real.sqrt_sq hMp_nonneg] at h2
  exact h2

-- Theorem 52: The Topological Yield Mass Limit (M = M_P / √2, Manuscript Eq. 127)
theorem topological_yield_limit (hm : M_val ≠ 0) (hm_pos : M_val > 0)
    (h_intersection : hbar / (M_val * c) = 2 * G * M_val / c^2) :
    M_val = M_P / Real.sqrt 2 := by
  have h1 : M_val^2 = (M_P)^2 / 2 := isolate_planck_yield_algebra M_val hm h_intersection
  exact positive_sqrt_reduction M_val hm_pos h1

-- Theorem 53: Derived 50/50 Capacity Partition ((M / M_P)^2 = 1/2, Manuscript Eq. 127)
theorem derived_half_capacity_partition (hm : M_val ≠ 0)
    (h_intersection : hbar / (M_val * c) = 2 * G * M_val / c^2) :
    (M_val / M_P)^2 = 1 / 2 := by
  have h1 : M_val^2 = M_P^2 / 2 := isolate_planck_yield_algebra M_val hm h_intersection
  have hMp2 : M_P^2 ≠ 0 := pow_ne_zero 2 M_P_ne_zero
  calc (M_val / M_P)^2
    _ = M_val^2 / M_P^2 := div_pow M_val M_P 2
    _ = (M_P^2 / 2) / M_P^2 := by rw [h1]
    _ = (M_P^2 / M_P^2) / 2 := by ring
    _ = 1 / 2 := by rw [div_self hMp2]

-- Theorem 54: Structural Yield Partition & Mass-Yield Equivalence (α_yield = 1/√2, Manuscript Eq. 129)
theorem yield_partition (alpha_yield : ℝ)
    (h_yield : alpha_yield = Real.sqrt (1 - 1 / 2)) :
    alpha_yield = 1 / Real.sqrt 2 := by
  have h_one_pos : (0:ℝ) ≤ 1 := by norm_num
  have h1 : Real.sqrt (1 - 1 / 2) = Real.sqrt (1 / 2) := by norm_num
  have h2 : Real.sqrt (1 / 2) = Real.sqrt 1 / Real.sqrt 2 := by rw [Real.sqrt_div h_one_pos]
  rw [h_yield, h1, h2, Real.sqrt_one]

theorem mass_yield_equivalence (alpha_yield : ℝ)
    (h_mass : M_val = M_P / Real.sqrt 2)
    (h_yield : alpha_yield = 1 / Real.sqrt 2) :
    M_val / M_P = alpha_yield := by
  have h1 : M_val / M_P = (M_P / Real.sqrt 2) / M_P := by rw [h_mass]
  have h2 : (M_P / Real.sqrt 2) / M_P = (M_P / M_P) / Real.sqrt 2 := by ring
  rw [h2] at h1
  have h_Mp_pos : 0 < M_P := M_P_pos
  have h_Mp_ne_zero : M_P ≠ 0 := ne_of_gt h_Mp_pos
  rw [div_self h_Mp_ne_zero] at h1
  rw [←h_yield] at h1
  exact h1

end AsymmetricTensor
