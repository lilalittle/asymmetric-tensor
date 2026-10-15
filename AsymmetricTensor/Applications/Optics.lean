/-
Copyright (c) 2026 Binyamin Tsadik Bair-Mosheh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Binyamin Tsadik Bair-Mosheh
-/
module

public import AsymmetricTensor.Model
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Conditional redshift, refraction, and magnitude relations

See `docs/modules.md` for the module map and compatibility policy.
The manuscript terminology and the mathematical statements are retained.
-/

@[expose] public section

open Real BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars true

namespace AsymmetricTensor


-- ==========================================
-- SECTION 15: Macroscopic Lensing (The Optical Pressure Gradient)
-- ==========================================

-- ==========================================
-- 15.1 Cosmological Redshift as a Metric Capacity Ratio
-- ==========================================
-- Theorem 56: Cosmological Redshift Ratio (Equation 188 / 15.1)
theorem cosmological_redshift_ratio (lambda_obs lambda_emit alpha_obs alpha_emit lambda_0 : ℝ)
    (_h_emit_ne : lambda_emit ≠ 0) (_h_alpha_emit_ne : alpha_emit ≠ 0) (h_lambda_0_ne : lambda_0 ≠ 0)
    (h_obs : lambda_obs = alpha_obs * lambda_0)
    (h_emit : lambda_emit = alpha_emit * lambda_0) :
    lambda_obs / lambda_emit = alpha_obs / alpha_emit := by
  rw [h_obs, h_emit]
  exact mul_div_mul_right alpha_obs alpha_emit h_lambda_0_ne

-- ==========================================
-- 15.2 The Tensor Refractive Index
-- ==========================================
-- Theorem 57: The Refractive Index Limit (Equation 192 / 15.2)
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
      _ = 1 / alpha_sq := by
        field_simp [hc_ne]
  rw [h_alpha] at h4
  exact h4

-- ==========================================
-- 15.3 The Macroscopic Pressure Substitution
-- ==========================================
theorem refractive_index_substitution (r_val ct_val : ℝ) (hPc : P_c > 0) :
    1 / (1 - (P_c * (1 - Real.exp (-r_val / ct_val))^2) / P_c) =
    1 / (Real.exp (-r_val / ct_val) * (2 - Real.exp (-r_val / ct_val))) := by
  have hPc_ne : P_c ≠ 0 := ne_of_gt hPc
  congr 1
  have h_cancel : (P_c * (1 - Real.exp (-r_val / ct_val))^2) / P_c = (1 - Real.exp (-r_val / ct_val))^2 := by
    have h_div : (P_c * (1 - Real.exp (-r_val / ct_val))^2) / P_c = (1 - Real.exp (-r_val / ct_val))^2 * (P_c / P_c) := by ring
    rw [h_div, div_self hPc_ne, mul_one]
  rw [h_cancel]
  ring

-- ==========================================
-- 15.4 The Longitudinal Path Integral (Shapiro Delay)
-- ==========================================

/-!
The following results are conditional on the exponential pressure ansatz in
manuscript v9 Eqs. (235)-(237). `L` is a positive scale held fixed along the
path. The domain is any finite interval `[0, r]` with `r ≥ 0`; no physical
horizon identification or boundary saturation is assumed or established.
See `docs/optical-path.md` for the physical and mathematical scope.
-/

/-- Refractive index of the stated exponential ansatz, used on `s ≥ 0`, `L > 0`.
Its denominator is proved positive on this domain below. -/
noncomputable def exponential_refractive_index (L s : ℝ) : ℝ :=
  1 / (Real.exp (-s / L) * (2 - Real.exp (-s / L)))

lemma exponential_denominator_pos (L s : ℝ) (hL : 0 < L) (hs : 0 ≤ s) :
    0 < Real.exp (-s / L) * (2 - Real.exp (-s / L)) := by
  have he : Real.exp (-s / L) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) hL.le)
  exact mul_pos (Real.exp_pos _) (by linarith)

lemma exponential_refractive_index_one_le (L s : ℝ) (hL : 0 < L) (hs : 0 ≤ s) :
    1 ≤ exponential_refractive_index L s := by
  unfold exponential_refractive_index
  apply (le_div_iff₀ (exponential_denominator_pos L s hL hs)).mpr
  nlinarith [sq_nonneg (1 - Real.exp (-s / L))]

lemma exponential_refractive_index_one_lt (L s : ℝ) (hL : 0 < L) (hs : 0 < s) :
    1 < exponential_refractive_index L s := by
  have he : Real.exp (-s / L) < 1 := Real.exp_lt_one_iff.mpr
    (div_neg_of_neg_of_pos (neg_neg_of_pos hs) hL)
  unfold exponential_refractive_index
  apply (lt_div_iff₀ (exponential_denominator_pos L s hL hs.le)).mpr
  nlinarith [sq_pos_of_pos (sub_pos.mpr he)]

lemma exponential_refractive_index_continuousOn (L : ℝ) (hL : 0 < L) :
    ContinuousOn (exponential_refractive_index L) (Set.Ici 0) := by
  unfold exponential_refractive_index
  have he : Continuous (fun s : ℝ => Real.exp (-s / L)) :=
    Real.continuous_exp.comp (continuous_id.neg.div_const L)
  apply continuousOn_const.div (he.continuousOn.mul (continuousOn_const.sub he.continuousOn))
  intro s hs
  exact ne_of_gt (exponential_denominator_pos L s hL hs)

/-- Finite radial optical path, manuscript v9 Eq. (238).
The accompanying results establish integrability when `L > 0` and `r ≥ 0`. -/
noncomputable def optical_distance (L r : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..r, exponential_refractive_index L s

lemma exponential_refractive_index_intervalIntegrable (L r : ℝ) (hL : 0 < L)
    (hr : 0 ≤ r) :
    IntervalIntegrable (exponential_refractive_index L) MeasureTheory.volume 0 r := by
  apply ContinuousOn.intervalIntegrable_of_Icc hr
  exact (exponential_refractive_index_continuousOn L hL).mono
    (fun _ hs => hs.1)

/-- The actual optical integral strictly exceeds every positive path length.
The equality `n(0) = 1` is harmless: strictness holds at positive radius. -/
theorem optical_distance_gt (L r : ℝ) (hL : 0 < L) (hr : 0 < r) :
    r < optical_distance L r := by
  have hstrict := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hr continuousOn_const
    ((exponential_refractive_index_continuousOn L hL).mono
      (show Set.Icc 0 r ⊆ Set.Ici 0 from fun _ hs => hs.1))
    (fun s hs => exponential_refractive_index_one_le L s hL hs.1.le)
    ⟨r, ⟨hr.le, le_rfl⟩, exponential_refractive_index_one_lt L r hL hr⟩
  simpa [optical_distance] using hstrict

/-- The coordinate-speed model `c₀ / n(s)`, with positive baseline speed `c₀`.
This is a model definition, not a derivation of a null-geodesic equation. -/
noncomputable def refractive_speed (L c₀ s : ℝ) : ℝ :=
  c₀ / exponential_refractive_index L s

/-- Travel time obtained by integrating inverse speed along the same radial path. -/
noncomputable def refractive_travel_time (L c₀ r : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..r, 1 / refractive_speed L c₀ s

theorem refractive_travel_time_eq (L c₀ r : ℝ) :
    refractive_travel_time L c₀ r = optical_distance L r / c₀ := by
  simp only [refractive_travel_time, refractive_speed, one_div_div,
    intervalIntegral.integral_div, optical_distance]

lemma refractive_travel_time_intervalIntegrable (L c₀ r : ℝ) (hL : 0 < L)
    (hr : 0 ≤ r) :
    IntervalIntegrable (fun s => 1 / refractive_speed L c₀ s) MeasureTheory.volume 0 r := by
  simpa only [refractive_speed, one_div_div] using
    (exponential_refractive_index_intervalIntegrable L r hL hr).div_const c₀

/-- Positive accumulated delay relative to travel at the constant baseline speed.
This establishes the finite-path consequence of the ansatz, not agreement with
an observed Shapiro delay or a gravitational-field model. -/
theorem refractive_travel_time_delay_pos (L c₀ r : ℝ) (hL : 0 < L)
    (hc : 0 < c₀) (hr : 0 < r) :
    0 < refractive_travel_time L c₀ r - r / c₀ := by
  rw [refractive_travel_time_eq, ← sub_div]
  exact div_pos (sub_pos.mpr (optical_distance_gt L r hL hr)) hc

@[simp] theorem exponential_refractive_index_zero (L : ℝ) :
    exponential_refractive_index L 0 = 1 := by
  norm_num [exponential_refractive_index]

@[simp] theorem optical_distance_zero (L : ℝ) : optical_distance L 0 = 0 := by
  simp [optical_distance]

@[simp] theorem refractive_travel_time_zero (L c₀ : ℝ) :
    refractive_travel_time L c₀ 0 = 0 := by
  simp [refractive_travel_time]

lemma refractive_speed_pos (L c₀ s : ℝ) (hL : 0 < L) (hc : 0 < c₀)
    (hs : 0 ≤ s) : 0 < refractive_speed L c₀ s := by
  apply div_pos hc
  exact lt_of_lt_of_le (by norm_num) (exponential_refractive_index_one_le L s hL hs)

lemma refractive_speed_lt (L c₀ s : ℝ) (hL : 0 < L) (hc : 0 < c₀)
    (hs : 0 < s) : refractive_speed L c₀ s < c₀ := by
  have hn := exponential_refractive_index_one_lt L s hL hs
  apply (div_lt_iff₀ (lt_trans (by norm_num) hn)).mpr
  nlinarith

lemma refractive_speed_eq_ansatz (L c₀ s : ℝ) :
    refractive_speed L c₀ s = c₀ * (1 - (1 - Real.exp (-s / L)) ^ 2) := by
  unfold refractive_speed exponential_refractive_index
  simp only [one_div, div_inv_eq_mul]
  ring

lemma exponential_refractive_index_eq_ansatz (L s : ℝ) :
    exponential_refractive_index L s = 1 / (1 - (1 - Real.exp (-s / L)) ^ 2) := by
  unfold exponential_refractive_index
  congr 1
  ring

-- ==========================================
-- 15.5 The Magnitude Anomaly (Optical Expansion)
-- ==========================================
variable (mu_obs mu_lin r_opt r_true z_val : ℝ)

/-- Base-10 logarithm, written by change of base to make the normalization explicit. -/
noncomputable def decimalLog (x : ℝ) : ℝ := Real.log x / Real.log 10

/-- Difference of distance moduli for positive distances measured in megaparsecs.
The logarithm arguments represent dimensionless numerical ratios to 1 Mpc;
the offset 25 converts to the conventional 10 pc reference distance.
The common redshift factor cancels; this is conditional algebra, not a proof
that an optical path exceeds the true distance. The final ratio is dimensionless. -/
lemma logarithmic_magnitude_anomaly (mu_o mu_l r_o r_t z : ℝ)
    (hr_o : r_o > 0) (hr_t : r_t > 0) (hz : (1 + z) > 0) :
    mu_o = 5 * decimalLog (r_o * (1 + z)) + 25 →
    mu_l = 5 * decimalLog (r_t * (1 + z)) + 25 →
    mu_o - mu_l = 5 * decimalLog (r_o / r_t) := by
  intro h_o h_l
  rw [h_o, h_l]
  unfold decimalLog
  rw [Real.log_mul (ne_of_gt hr_o) (ne_of_gt hz),
    Real.log_mul (ne_of_gt hr_t) (ne_of_gt hz),
    Real.log_div (ne_of_gt hr_o) (ne_of_gt hr_t)]
  ring

/-- A tenfold distance ratio produces exactly five magnitudes. -/
theorem tenfold_distance_magnitude_anomaly :
    5 * decimalLog 10 = 5 := by
  have h : Real.log (10 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simp [decimalLog, h]

/-- Conditional base-10 distance-modulus identity matching manuscript v9 Eq. (239).
Distances are positive numerical values in Mpc. This statement does not assert
an optical-distance inequality or divergence as a limit. -/
theorem magnitude_anomaly_divergence
    (hr_o : r_opt > 0) (hr_t : r_true > 0) (hz : (1 + z_val) > 0)
    (h_mu_obs : mu_obs = 5 * decimalLog (r_opt * (1 + z_val)) + 25)
    (h_mu_lin : mu_lin = 5 * decimalLog (r_true * (1 + z_val)) + 25) :
    mu_obs - mu_lin = 5 * decimalLog (r_opt / r_true) := by
  exact logarithmic_magnitude_anomaly mu_obs mu_lin r_opt r_true z_val
    hr_o hr_t hz h_mu_obs h_mu_lin

/-- The actual finite optical path gives a strictly positive base-10 magnitude
anomaly. Both distances use the same units, so their ratio is dimensionless. -/
theorem optical_magnitude_anomaly_pos (L r : ℝ) (hL : 0 < L) (hr : 0 < r) :
    0 < 5 * decimalLog (optical_distance L r / r) := by
  have hratio : 1 < optical_distance L r / r := by
    apply (lt_div_iff₀ hr).mpr
    simpa using optical_distance_gt L r hL hr
  exact mul_pos (by norm_num)
    (div_pos (Real.log_pos hratio) (Real.log_pos (by norm_num)))

/-- Eq. (239), now connected to the defined optical integral rather than two
arbitrary distances. The distance-modulus prescriptions remain explicit
hypotheses; positivity follows from the ansatz and `L > 0`, `r > 0`.
Distances in the hypotheses are numerical values in Mpc, as above. -/
theorem magnitude_anomaly_of_optical_path (mu_o mu_l L r z : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hz : 0 < 1 + z)
    (ho : mu_o = 5 * decimalLog (optical_distance L r * (1 + z)) + 25)
    (hl : mu_l = 5 * decimalLog (r * (1 + z)) + 25) :
    mu_o - mu_l = 5 * decimalLog (optical_distance L r / r) ∧ 0 < mu_o - mu_l := by
  have hpath : 0 < optical_distance L r := lt_trans hr (optical_distance_gt L r hL hr)
  have heq := logarithmic_magnitude_anomaly mu_o mu_l (optical_distance L r) r z
    hpath hr hz ho hl
  exact ⟨heq, heq.symm ▸ optical_magnitude_anomaly_pos L r hL hr⟩

end AsymmetricTensor
