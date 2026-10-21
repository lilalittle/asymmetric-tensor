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
-- SECTION 15: MACROSCOPIC LENSING (THE OPTICAL PRESSURE GRADIENT)
-- ======================================================================

-- Dimensional Audit: Wavelength redshift ratio (lambda_obs / lambda_emit), refractive index (n = c / v_c), and pressure ratio (P_dyn / P_c) are dimensionless:
theorem unit_section15_optical_refraction :
    u_l_p / u_l_p = u_dimless ∧
    u_c / u_c = u_dimless ∧
    u_P_c / u_P_c = u_dimless := by
  refine ⟨rfl, rfl, rfl⟩

-- ----------------------------------------------------------------------
-- 15.1 Cosmological Redshift as a Metric Capacity Ratio
-- ----------------------------------------------------------------------

-- Theorem 101: Cosmological Redshift Capacity Ratio (λ_obs / λ_emit = α_obs / α_emit, Manuscript Section 15.1)
theorem cosmological_redshift_ratio (lambda_obs lambda_emit alpha_obs alpha_emit lambda_0 : ℝ)
    (_h_emit_ne : lambda_emit ≠ 0) (_h_alpha_emit_ne : alpha_emit ≠ 0) (h_lambda_0_ne : lambda_0 ≠ 0)
    (h_obs : lambda_obs = alpha_obs * lambda_0)
    (h_emit : lambda_emit = alpha_emit * lambda_0) :
    lambda_obs / lambda_emit = alpha_obs / alpha_emit := by
  rw [h_obs, h_emit]
  exact mul_div_mul_right alpha_obs alpha_emit h_lambda_0_ne

-- ----------------------------------------------------------------------
-- 15.2 The Tensor Refractive Index
-- ----------------------------------------------------------------------

-- Theorem 102: The Tensor Refractive Index Limit (n(r) = (1 - P_dyn(r)/P_c)^(-1), Manuscript Section 15.2)
theorem tensor_refractive_index (P_dyn_val P_c_val v_c_r n_r alpha_sq : ℝ)
    (hc : c > 0) (h_alpha_pos : alpha_sq > 0)
    (h_alpha : alpha_sq = 1 - P_dyn_val / P_c_val)
    (h_vc : v_c_r = c * Real.sqrt (alpha_sq / (1 / alpha_sq)))
    (h_n : n_r = c / v_c_r) :
    n_r = 1 / (1 - P_dyn_val / P_c_val) := by
  have h1 : Real.sqrt (alpha_sq / (1 / alpha_sq)) = alpha_sq := by
    have h2 : alpha_sq / (1 / alpha_sq) = alpha_sq^2 := by
      have ha_neq : alpha_sq ≠ 0 := ne_of_gt h_alpha_pos
      field_simp [ha_neq]
    rw [h2]
    exact Real.sqrt_sq (le_of_lt h_alpha_pos)
  have h3 : v_c_r = c * alpha_sq := by
    rw [h_vc, h1]
  have h4 : n_r = 1 / alpha_sq := by
    have hc_ne : c ≠ 0 := ne_of_gt hc
    calc n_r = c / (c * alpha_sq) := by rw [h_n, h3]
      _ = (c * 1) / (c * alpha_sq) := by rw [mul_one c]
      _ = 1 / alpha_sq := by field_simp [hc_ne]
  rw [h_alpha] at h4
  exact h4

-- ----------------------------------------------------------------------
-- 15.3 The Macroscopic Pressure Substitution
-- ----------------------------------------------------------------------

-- Theorem 103: Macroscopic Refractive Index Substitution (n(r) = 1 / [exp(-r/ct)(2 - exp(-r/ct))], Manuscript Section 15.3)
theorem refractive_index_substitution (r_val ct_val : ℝ) :
    1 / (1 - (P_c * (1 - Real.exp (-r_val / ct_val))^2) / P_c) =
    1 / (Real.exp (-r_val / ct_val) * (2 - Real.exp (-r_val / ct_val))) := by
  have hPc_ne : P_c ≠ 0 := Pc_non_zero
  congr 1
  have h_cancel : (P_c * (1 - Real.exp (-r_val / ct_val))^2) / P_c = (1 - Real.exp (-r_val / ct_val))^2 := by
    have h_div : (P_c * (1 - Real.exp (-r_val / ct_val))^2) / P_c =
                 (1 - Real.exp (-r_val / ct_val))^2 * (P_c / P_c) := by ring
    rw [h_div, div_self hPc_ne, mul_one]
  rw [h_cancel]
  ring

-- Theorem 174: Unification of the Four Cosmological Tensor Effects
-- Explicitly distinguishes:
-- 1. The pressure-only background metric specialization `U_hat alpha_g ...` (`α_a = 1`, `α_s = α_g`),
--    whose diagonals `U_00 = -α_g^2` and `U_11 = 1/α_g^2` govern null-geodesic refraction
--    (`U_00 c^2 + U_11 v_c^2 = 0` and `n_idx = c / v_c = 1 / α_g^2`), and
-- 2. The combined total-admittance tensor `U_hat alpha_s ...` (`α_s = α_g * α_a`), whose temporal
--    diagonal is `U_00 = -(α_g * α_a)^2` and whose combined clock-dilation factor
--    `(1 / α_g) * (1 / α_a) = 1 / α_s` coincides with `1 / α_g^2 = (U_hat alpha_g ...) 1 1`
--    under the free-fall equal-admittance specialization (`v_flow = v_0 → α_a = α_g`).
theorem tensor_four_effects_unification
    (alpha_s alpha_g alpha_a alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4)
    (t_p_val v_0 v_flow P_static P_dyn v_c n_idx : ℝ)
    (hag : alpha_g ≠ 0) (hv_sub : v_0 / c ≠ 1) (hv_plus : 1 + v_0 / c ≠ 0)
    (h_as : alpha_s = alpha_g * alpha_a)
    (h_ledger : P_c = P_static + P_dyn)
    (h_P_dyn : P_dyn = (1 / 2) * rho_tau * v_0^2)
    (h_ag_sq : alpha_g^2 = P_static / P_c)
    (h_freefall : v_flow = v_0)
    (h_aa_eq : alpha_a = alpha_g)
    (h_vc : v_c = c * alpha_g^2)
    (h_n : n_idx = c / v_c) :
    alpha_g^2 = 1 - (v_0 / c)^2 ∧
    (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 0 0 = -(alpha_g^2 * alpha_a^2) ∧
    (1 / alpha_g) * (1 / alpha_a) = 1 / alpha_s ∧
    (1 / alpha_s) * (1 + v_flow / c) =
      (U_hat alpha_g alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 1 * (1 + v_0 / c) ∧
    (U_hat alpha_g alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 1 * (1 + v_0 / c) =
      1 / (1 - v_0 / c) ∧
    (U_hat alpha_g alpha v_x v_y v_z d_lambda d_beta t_p_val) 0 0 * c^2 +
      (U_hat alpha_g alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 1 * v_c^2 = 0 ∧
    n_idx = (U_hat alpha_g alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 1 := by
  have hc : c ≠ 0 := c_ne_zero
  have hPc : P_c ≠ 0 := Pc_non_zero
  have hag2 : alpha_g^2 ≠ 0 := pow_ne_zero 2 hag
  have h00_comb : (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 0 0 = -(alpha_g^2 * alpha_a^2) := by
    have h0 : (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 0 0 = -alpha_s^2 := by simp [U_hat]
    rw [h0, h_as]
    ring
  have h_inv_as : (1 / alpha_g) * (1 / alpha_a) = 1 / alpha_s := by
    rw [h_as]
    ring
  have h00 : (U_hat alpha_g alpha v_x v_y v_z d_lambda d_beta t_p_val) 0 0 = -alpha_g^2 := by
    simp [U_hat]
  have h11 : (U_hat alpha_g alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 1 = 1 / alpha_g^2 := by
    simp [U_hat]
  have h_ag1 : alpha_g^2 = 1 - (v_0 / c)^2 := by
    have h_p : P_static = (1 - (v_0 / c)^2) * P_c := by
      have h_pc_def : P_c = (1 / 2) * rho_tau * c^2 := rfl
      have h_vd : (v_0 / c)^2 * P_c = P_dyn := by
        rw [h_P_dyn, h_pc_def, div_pow]
        calc (v_0^2 / c^2) * (1 / 2 * rho_tau * c^2)
          _ = 1 / 2 * rho_tau * ((v_0^2 / c^2) * c^2) := by ring
          _ = 1 / 2 * rho_tau * v_0^2 := by rw [div_mul_cancel₀ _ (pow_ne_zero 2 hc)]
      linarith [h_ledger, h_vd]
    rw [h_ag_sq, h_p, mul_div_cancel_right₀ _ hPc]
  refine ⟨h_ag1, h00_comb, h_inv_as, ?_, ?_, ?_, ?_⟩
  · rw [h11, h_as, h_aa_eq, h_freefall]
    ring
  · rw [h11, h_ag1]
    have hv_sub' : 1 - v_0 / c ≠ 0 := sub_ne_zero.mpr (Ne.symm hv_sub)
    have h_diff : 1 - (v_0 / c)^2 = (1 - v_0 / c) * (1 + v_0 / c) := by ring
    have h_prod_ne : 1 - (v_0 / c)^2 ≠ 0 := by
      rw [h_diff]
      exact mul_ne_zero hv_sub' hv_plus
    have h_cancel : (1 / (1 - v_0 / c)) * (1 - (v_0 / c)^2) = 1 + v_0 / c := by
      calc (1 / (1 - v_0 / c)) * (1 - (v_0 / c)^2)
        _ = ((1 / (1 - v_0 / c)) * (1 - v_0 / c)) * (1 + v_0 / c) := by ring
        _ = 1 * (1 + v_0 / c) := by rw [one_div_mul_cancel hv_sub']
        _ = 1 + v_0 / c := by ring
    calc (1 / (1 - (v_0 / c)^2)) * (1 + v_0 / c)
      _ = (1 / (1 - (v_0 / c)^2)) * ((1 / (1 - v_0 / c)) * (1 - (v_0 / c)^2)) := by rw [← h_cancel]
      _ = ((1 / (1 - (v_0 / c)^2)) * (1 - (v_0 / c)^2)) * (1 / (1 - v_0 / c)) := by ring
      _ = 1 * (1 / (1 - v_0 / c)) := by rw [one_div_mul_cancel h_prod_ne]
      _ = 1 / (1 - v_0 / c) := by ring
  · rw [h00, h11, h_vc]
    calc -alpha_g^2 * c^2 + (1 / alpha_g^2) * (c * alpha_g^2)^2
      _ = -alpha_g^2 * c^2 + ((1 / alpha_g^2) * alpha_g^2) * (alpha_g^2 * c^2) := by ring
      _ = -alpha_g^2 * c^2 + 1 * (alpha_g^2 * c^2) := by rw [one_div_mul_cancel hag2]
      _ = 0 := by ring
  · rw [h11, h_n, h_vc, div_mul_eq_div_div, div_self hc]

-- ----------------------------------------------------------------------
-- 15.4 The Longitudinal Path Integral (Shapiro Delay) (Resolves Issue #26)
-- ----------------------------------------------------------------------

-- Theorem 103.5: Optical Path Retardation (n_avg > 1 → r_opt > r_true, Manuscript Section 15.4)
theorem optical_path_retardation (r_opt r_true n_avg : ℝ)
    (hr_true : 0 < r_true) (hn_gt_one : 1 < n_avg)
    (h_path : r_opt = n_avg * r_true) :
    r_true < r_opt ∧ 1 < r_opt / r_true := by
  have hr_ne : r_true ≠ 0 := ne_of_gt hr_true
  have h_diff : r_opt - r_true = (n_avg - 1) * r_true := by
    rw [h_path]
    ring
  have h_pos : 0 < (n_avg - 1) * r_true := mul_pos (by linarith) hr_true
  have h_lt : r_true < r_opt := by linarith
  have h_quot_pos : 0 < (r_opt - r_true) / r_true := div_pos (by linarith) hr_true
  have h_quot_eq : (r_opt - r_true) / r_true = r_opt / r_true - 1 := by
    field_simp
  refine ⟨h_lt, by linarith⟩

-- ----------------------------------------------------------------------
-- 15.5 The Magnitude Anomaly (Optical Expansion) (Resolves Issue #25)
-- ----------------------------------------------------------------------
variable (mu_obs mu_lin r_opt r_true z_val : ℝ)

/-- Base-10 astrophysical logarithm `log_10(x) = ln(x) / ln(10)`. -/
noncomputable def log10 (x : ℝ) : ℝ := Real.log x / Real.log 10

lemma logarithmic_magnitude_anomaly (mu_o mu_l r_o r_t z : ℝ)
    (hr_o : r_o > 0) (hr_t : r_t > 0) (hz : (1 + z) > 0) :
  mu_o = 5 * Real.log (r_o * (1 + z)) + 25 →
  mu_l = 5 * Real.log (r_t * (1 + z)) + 25 →
  mu_o - mu_l = 5 * Real.log (r_o / r_t) := by
  intro h_o h_l
  have h1 : mu_o - mu_l = 5 * (Real.log (r_o * (1 + z)) - Real.log (r_t * (1 + z))) := by
    calc
      mu_o - mu_l = (5 * Real.log (r_o * (1 + z)) + 25) - (5 * Real.log (r_t * (1 + z)) + 25) := by rw [h_o, h_l]
      _ = 5 * (Real.log (r_o * (1 + z)) - Real.log (r_t * (1 + z))) := by ring
  have h_log_sub : Real.log (r_o * (1 + z)) - Real.log (r_t * (1 + z)) =
                   Real.log ((r_o * (1 + z)) / (r_t * (1 + z))) :=
    (Real.log_div (mul_ne_zero (ne_of_gt hr_o) (ne_of_gt hz)) (mul_ne_zero (ne_of_gt hr_t) (ne_of_gt hz))).symm
  rw [h_log_sub] at h1
  have h_cancel : (r_o * (1 + z)) / (r_t * (1 + z)) = r_o / r_t := by
    have hz_ne : (1 + z) ≠ 0 := ne_of_gt hz
    exact mul_div_mul_right r_o r_t hz_ne
  rw [h_cancel] at h1
  exact h1

-- Theorem 104: The Optical Expansion Magnitude Anomaly (Δμ = 5 log_10(r_opt / r_true) > 0, Manuscript Section 15.5)
theorem magnitude_anomaly_divergence (hr_o : r_opt > 0) (hr_t : r_true > 0) (hz : (1 + z_val) > 0)
    (h_mu_obs : mu_obs = 5 * Real.log (r_opt * (1 + z_val)) + 25)
    (h_mu_lin : mu_lin = 5 * Real.log (r_true * (1 + z_val)) + 25) :
    mu_obs - mu_lin = 5 * Real.log (r_opt / r_true) := by
  exact logarithmic_magnitude_anomaly mu_obs mu_lin r_opt r_true z_val hr_o hr_t hz h_mu_obs h_mu_lin

theorem magnitude_anomaly_log10_pos (mu_obs_10 mu_lin_10 : ℝ)
    (hr_t : 0 < r_true) (h_retarded : r_true < r_opt) (hz : 0 < 1 + z_val)
    (h_obs10 : mu_obs_10 = 5 * log10 (r_opt * (1 + z_val)) + 25)
    (h_lin10 : mu_lin_10 = 5 * log10 (r_true * (1 + z_val)) + 25) :
    mu_obs_10 - mu_lin_10 = 5 * log10 (r_opt / r_true) ∧
    0 < mu_obs_10 - mu_lin_10 := by
  have hr_o : 0 < r_opt := lt_trans hr_t h_retarded
  have hr_t_ne : r_true ≠ 0 := ne_of_gt hr_t
  have h_log_sub : Real.log (r_opt * (1 + z_val)) - Real.log (r_true * (1 + z_val)) =
                   Real.log (r_opt / r_true) := by
    rw [← Real.log_div (mul_ne_zero (ne_of_gt hr_o) (ne_of_gt hz))
                       (mul_ne_zero hr_t_ne (ne_of_gt hz))]
    rw [mul_div_mul_right r_opt r_true (ne_of_gt hz)]
  have h_diff : mu_obs_10 - mu_lin_10 = 5 * log10 (r_opt / r_true) := by
    rw [h_obs10, h_lin10]
    dsimp [log10]
    calc (5 * (Real.log (r_opt * (1 + z_val)) / Real.log 10) + 25) -
         (5 * (Real.log (r_true * (1 + z_val)) / Real.log 10) + 25)
      _ = 5 * ((Real.log (r_opt * (1 + z_val)) - Real.log (r_true * (1 + z_val))) / Real.log 10) := by ring
      _ = 5 * (Real.log (r_opt / r_true) / Real.log 10) := by rw [h_log_sub]
  refine ⟨h_diff, ?_⟩
  rw [h_diff]
  dsimp [log10]
  have h_quot_pos : 0 < (r_opt - r_true) / r_true := div_pos (by linarith) hr_t
  have h_quot_eq : (r_opt - r_true) / r_true = r_opt / r_true - 1 := by
    field_simp
  have h_ratio_gt : 1 < r_opt / r_true := by linarith
  have h_log_pos : 0 < Real.log (r_opt / r_true) := Real.log_pos h_ratio_gt
  have h_log10_pos : 0 < Real.log 10 := Real.log_pos (by norm_num : (1 : ℝ) < 10)
  exact mul_pos (by norm_num) (div_pos h_log_pos h_log10_pos)

end AsymmetricTensor
