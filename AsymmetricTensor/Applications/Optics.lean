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

/-!
# Macroscopic lensing (optical pressure gradient)

Module of Binyamin's v5.0 formalization. Declarations retained verbatim
from the author's single-file development.
-/

@[expose] public section

open Real BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars true

namespace AsymmetricTensor
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
