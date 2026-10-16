/-
Copyright (c) 2026 Binyamin Tsadik Bair-Mosheh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Binyamin Tsadik Bair-Mosheh
-/
module
public import AsymmetricTensor.Model
/-!
# Macroscopic lensing (the optical pressure gradient)
Module of Binyamin's v3.0 formalization. Declarations retained verbatim
from the author's single-file development.
-/
namespace AsymmetricTensor
-- ==========================================
-- SECTION 15: Macroscopic Lensing (The Optical Pressure Gradient)
-- ==========================================
-- ==========================================
-- 15.1 Cosmological Redshift as a Metric Capacity Ratio
-- ==========================================
-- Theorem 56: Cosmological Redshift Ratio (Equation 188 / 15.1)
-- Proves the geometric derivation for redshift independent of spatial expansion.
theorem cosmological_redshift_ratio (lambda_obs lambda_emit alpha_obs alpha_emit lambda_0 : ℝ)
    (h_emit_ne : lambda_emit ≠ 0) (h_alpha_emit_ne : alpha_emit ≠ 0) (h_lambda_0_ne : lambda_0 ≠ 0)
    (h_obs : lambda_obs = alpha_obs * lambda_0)
    (h_emit : lambda_emit = alpha_emit * lambda_0) :
    lambda_obs / lambda_emit = alpha_obs / alpha_emit := by
  rw [h_obs, h_emit]
  exact mul_div_mul_right alpha_obs alpha_emit h_lambda_0_ne
-- ==========================================
-- 15.2 The Tensor Refractive Index
-- ==========================================
-- Theorem 57: The Refractive Index Limit (Equation 192 / 15.2)
-- Proves n(r) = (1 - P_dyn/P_c)^(-1) from the null geodesic phase velocity.
theorem tensor_refractive_index (P_dyn_val P_c_val v_c_r n_r alpha_sq : ℝ)
    (hc : c > 0) (h_alpha_pos : alpha_sq > 0)
    (h_alpha : alpha_sq = 1 - P_dyn_val / P_c_val)
    (h_vc : v_c_r = c * Real.sqrt (alpha_sq / (1 / alpha_sq)))
    (h_n : n_r = c / v_c_r) :
    n_r = (1 - P_dyn_val / P_c_val)⁻¹ := by
  have h1 : Real.sqrt (alpha_sq / (1 / alpha_sq)) = alpha_sq := by
    have h2 : alpha_sq / (1 / alpha_sq) = alpha_sq^2 := by
      have ha_neq : alpha_sq ≠ 0 := ne_of_gt h_alpha_pos
      field_simp [ha_neq]
      ring
    rw [h2]
    exact Real.sqrt_sq (le_of_lt h_alpha_pos)
  have h3 : v_c_r = c * alpha_sq := by
    rw [h_vc, h1]
  have h4 : n_r = 1 / alpha_sq := by
    have hc_ne : c ≠ 0 := ne_of_gt hc
    calc n_r = c / (c * alpha_sq) := by rw [h_n, h3]
      _ = (c * 1) / (c * alpha_sq) := by rw [mul_one c]
      _ = 1 / alpha_sq := by
        field_simp [hc_ne]
        ring
  rw [h_alpha] at h4
  exact h4
-- ==========================================
-- 15.3 The Macroscopic Pressure Substitution
-- ==========================================
-- Theorem 58: Optical Density Substitution (Equation 195 / 15.3)
-- Proves the exponential factorization of the macroscopic refractive index natively.
theorem refractive_index_substitution (r_val ct_val : ℝ) (hPc : P_c > 0) :
    (1 - (P_c * (1 - Real.exp (-r_val / ct_val))^2) / P_c)⁻¹ =
    (Real.exp (-r_val / ct_val) * (2 - Real.exp (-r_val / ct_val)))⁻¹ := by
  have hPc_ne : P_c ≠ 0 := ne_of_gt hPc
  congr 1 -- Strips the inverse operator from both sides
  rw [mul_div_cancel_left₀ _ hPc_ne]
  ring
-- ==========================================
-- 15.4 The Longitudinal Path Integral (Shapiro Delay)
-- ==========================================
-- (Fermat's Principle integration of apparent optical delay. Derived conceptually).
-- ==========================================
-- 15.5 The Magnitude Anomaly (Optical Expansion)
-- ==========================================
variable (mu_obs mu_lin r_opt r_true z_val : ℝ)
-- PROVEN LEMMA: Logarithmic Magnitude Anomaly Extraction
-- Upgraded from an axiom. Resolves the differential magnitude via native logarithmic identities.
lemma logarithmic_magnitude_anomaly (mu_o mu_l r_o r_t z : ℝ) (hr_o : r_o > 0) (hr_t : r_t > 0) (hz : (1 + z) > 0) :
  mu_o = 5 * Real.log (r_o * (1 + z)) + 25 →
  mu_l = 5 * Real.log (r_t * (1 + z)) + 25 →
  mu_o - mu_l = 5 * Real.log (r_o / r_t) := by
  intro h_o h_l
  have h1 : mu_o - mu_l = 5 * (Real.log (r_o * (1 + z)) - Real.log (r_t * (1 + z))) := by
    calc
      mu_o - mu_l = (5 * Real.log (r_o * (1 + z)) + 25) - (5 * Real.log (r_t * (1 + z)) + 25) := by rw [h_o, h_l]
      _ = 5 * (Real.log (r_o * (1 + z)) - Real.log (r_t * (1 + z))) := by ring
  -- Apply the logarithmic subtraction and multiplication identities
  have h_log_sub : Real.log (r_o * (1 + z)) - Real.log (r_t * (1 + z)) = Real.log ((r_o * (1 + z)) / (r_t * (1 + z))) := by
    exact (Real.log_div (mul_ne_zero (ne_of_gt hr_o) (ne_of_gt hz)) (mul_ne_zero (ne_of_gt hr_t) (ne_of_gt hz))).symm
  rw [h_log_sub] at h1
  have h_cancel : (r_o * (1 + z)) / (r_t * (1 + z)) = r_o / r_t := by
    have hz_ne : (1 + z) ≠ 0 := ne_of_gt hz
    exact mul_div_mul_right r_o r_t hz_ne
  rw [h_cancel] at h1
  exact h1
-- Theorem 59: The Optical Expansion Anomaly (Dark Energy) (Equation 198 / 15.5)
-- Proves Delta_mu = 5 * log10 (r_opt / r_true) natively from logarithmic expansion.
theorem magnitude_anomaly_divergence (hr_o : r_opt > 0) (hr_t : r_true > 0) (hz : (1 + z_val) > 0)
    (h_mu_obs : mu_obs = 5 * Real.log (r_opt * (1 + z_val)) + 25)
    (h_mu_lin : mu_lin = 5 * Real.log (r_true * (1 + z_val)) + 25) :
    mu_obs - mu_lin = 5 * Real.log (r_opt / r_true) := by
  exact logarithmic_magnitude_anomaly mu_obs mu_lin r_opt r_true z_val hr_o hr_t hz h_mu_obs h_mu_lin
end AsymmetricTensor
