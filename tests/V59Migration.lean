import AsymmetricTensor
import ProofAudit

/-!
v5.9 exact-type and projection call sites. The optical theorem retains supplied
derivative premises and its unscaled HasDerivAt conclusion. Determinant tests
are finite matrix algebra, not a Born-Infeld action or a universal field cutoff.
-/

open AsymmetricTensor

namespace V59Migration

-- Whole-type ascriptions pin binder order, hypotheses and conjunction order.
example : ∀ (R_h z : ℝ)
    (hz2 : 2 * z + 1 ≠ 0)
    (h_dlin : HasDerivAt (fun x => x / 2) (1 / 2) z)
    (h_dlog : HasDerivAt (fun x => (1 / 4) * Real.log (2 * x + 1)) (1 / (2 * (2 * z + 1))) z),
    R_h * ((0 : ℝ) / 2 + (1 / 4) * Real.log (2 * 0 + 1)) = 0 ∧
    HasDerivAt (fun x => x / 2 + (1 / 4) * Real.log (2 * x + 1))
      ((1 + z) / (2 * z + 1)) z ∧
    R_h * (1 / 2 + 1 / (2 * (2 * z + 1))) = R_h * ((1 + z) / (2 * z + 1)) :=
  optical_path_closed_form_antiderivative

example : ∀ (r_opt r_true z_val : ℝ) (mu_obs_10 mu_lin_10 : ℝ)
    (hr_t : 0 < r_true) (h_retarded : r_true < r_opt) (hz : 0 < 1 + z_val)
    (h_obs10 : mu_obs_10 = 5 * log10 (r_opt * (1 + z_val)) + 25)
    (h_lin10 : mu_lin_10 = 5 * log10 (r_true * (1 + z_val)) + 25),
    mu_obs_10 - mu_lin_10 = 5 * log10 (r_opt / r_true) ∧
    mu_obs_10 - mu_lin_10 = (5 / Real.log 10) * Real.log (r_opt / r_true) ∧
    0 < mu_obs_10 - mu_lin_10 :=
  magnitude_anomaly_log10_pos

example : ∀ (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ)
    (ha_s : alpha_s ≠ 0),
    let Ex := alpha * (v_x / c)
    let Ey := alpha * (v_y / c)
    let Ez := alpha * (v_z / c)
    let Bx := alpha * (t_p_val * Omega_x_clebsch d_lambda d_beta)
    let By := alpha * (t_p_val * Omega_y_clebsch d_lambda d_beta)
    let Bz := alpha * (t_p_val * Omega_z_clebsch d_lambda d_beta)
    det4x4 (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) =
      - (1 / alpha_s^4) * (1 - (Ex^2 + Ey^2 + Ez^2)) -
      (Bx^2 + By^2 + Bz^2) +
      (Ex * Bx + Ey * By + Ez * Bz)^2 ∧
    - alpha_s^4 * det4x4 (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) =
      1 - (Ex^2 + Ey^2 + Ez^2) + alpha_s^4 * (Bx^2 + By^2 + Bz^2) -
      alpha_s^4 * (Ex * Bx + Ey * By + Ez * Bz)^2 ∧
    (det4x4 (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) =
      det4x4 (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) ↔
      (Ex^2 + Ey^2 + Ez^2) + alpha_s^4 * (Ex * Bx + Ey * By + Ez * Bz)^2 =
      alpha_s^4 * (Bx^2 + By^2 + Bz^2)) ∧
    (- (1 / (1 : ℝ)^4) * (1 - (0^2 + 0^2 + (1 / 2 : ℝ)^2)) -
      (0^2 + 0^2 + (1 / 2 : ℝ)^2) +
      (0 * 0 + 0 * 0 + (1 / 2 : ℝ) * (1 / 2 : ℝ))^2 = -(15 / 16 : ℝ)) :=
  born_infeld_general_determinant_isomorphism

-- v5.8 returned A ∧ B; v5.9 returns A ∧ C ∧ B. Reconstruct the old
-- view explicitly, taking positivity from .2.2 rather than stale .2.
theorem magnitude_projection_migration
    (r_opt r_true z_val mu_obs_10 mu_lin_10 : ℝ)
    (hr_t : 0 < r_true) (h_retarded : r_true < r_opt) (hz : 0 < 1 + z_val)
    (h_obs10 : mu_obs_10 = 5 * log10 (r_opt * (1 + z_val)) + 25)
    (h_lin10 : mu_lin_10 = 5 * log10 (r_true * (1 + z_val)) + 25) :
    mu_obs_10 - mu_lin_10 = 5 * log10 (r_opt / r_true) ∧
    0 < mu_obs_10 - mu_lin_10 := by
  have h := magnitude_anomaly_log10_pos r_opt r_true z_val mu_obs_10 mu_lin_10
    hr_t h_retarded hz h_obs10 h_lin10
  exact ⟨h.1, h.2.2⟩

-- The inserted second conjunct is the natural-log/base-10 conversion.
theorem magnitude_log_bridge_callsite
    (r_opt r_true z_val mu_obs_10 mu_lin_10 : ℝ)
    (hr_t : 0 < r_true) (h_retarded : r_true < r_opt) (hz : 0 < 1 + z_val)
    (h_obs10 : mu_obs_10 = 5 * log10 (r_opt * (1 + z_val)) + 25)
    (h_lin10 : mu_lin_10 = 5 * log10 (r_true * (1 + z_val)) + 25) :
    mu_obs_10 - mu_lin_10 = (5 / Real.log 10) * Real.log (r_opt / r_true) := by
  exact (magnitude_anomaly_log10_pos r_opt r_true z_val mu_obs_10 mu_lin_10
    hr_t h_retarded hz h_obs10 h_lin10).2.1

-- Exercise the production positivity projection at a tenfold distance ratio.
-- The pre-existing V45 suite independently retains decimal calibration.
theorem magnitude_tenfold_positive :
    0 < (5 * log10 (10 * (1 + (0 : ℝ))) + 25) -
      (5 * log10 (1 * (1 + (0 : ℝ))) + 25) := by
  exact (magnitude_anomaly_log10_pos 10 1 0 _ _
    (by norm_num) (by norm_num) (by norm_num) rfl rfl).2.2

-- All three outputs are consumed, without silently manufacturing either
-- component chain-rule premise or an integrated optical-path conclusion.
theorem antiderivative_projection_callsite (R_h z : ℝ)
    (hz2 : 2 * z + 1 ≠ 0)
    (h_dlin : HasDerivAt (fun x => x / 2) (1 / 2) z)
    (h_dlog : HasDerivAt (fun x => (1 / 4) * Real.log (2 * x + 1))
      (1 / (2 * (2 * z + 1))) z) :
    HasDerivAt (fun x => x / 2 + (1 / 4) * Real.log (2 * x + 1))
      ((1 + z) / (2 * z + 1)) z ∧
    R_h * ((0 : ℝ) / 2 + (1 / 4) * Real.log (2 * 0 + 1)) = 0 ∧
    R_h * (1 / 2 + 1 / (2 * (2 * z + 1))) = R_h * ((1 + z) / (2 * z + 1)) := by
  have h := optical_path_closed_form_antiderivative R_h z hz2 h_dlin h_dlog
  exact ⟨h.2.1, h.1, h.2.2⟩

-- Distinguish the cleared polynomial and equality criterion from a claim
-- that the asymmetric determinant always equals the symmetric determinant.
theorem determinant_projection_callsite
    (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ)
    (ha_s : alpha_s ≠ 0) :
    let Ex := alpha * (v_x / c)
    let Ey := alpha * (v_y / c)
    let Ez := alpha * (v_z / c)
    let Bx := alpha * (t_p_val * Omega_x_clebsch d_lambda d_beta)
    let By := alpha * (t_p_val * Omega_y_clebsch d_lambda d_beta)
    let Bz := alpha * (t_p_val * Omega_z_clebsch d_lambda d_beta);
    -alpha_s^4 * det4x4 (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) =
      1 - (Ex^2 + Ey^2 + Ez^2) + alpha_s^4 * (Bx^2 + By^2 + Bz^2) -
      alpha_s^4 * (Ex * Bx + Ey * By + Ez * Bz)^2 ∧
    (det4x4 (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) =
      det4x4 (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) ↔
      (Ex^2 + Ey^2 + Ez^2) + alpha_s^4 * (Ex * Bx + Ey * By + Ez * Bz)^2 =
        alpha_s^4 * (Bx^2 + By^2 + Bz^2)) := by
  have h := born_infeld_general_determinant_isomorphism
    alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val ha_s
  exact ⟨h.2.1, h.2.2.1⟩

-- Unlike the source's final numerical polynomial, this evaluates an actual
-- U_hat at nonunit alpha_s=2 and parallel E=B=(0,0,1/2). The dot-product term
-- is nonzero, and dropping it or forgetting the alpha_s powers changes the result.
theorem nonunit_parallel_matrix :
    det4x4 (U_hat 2 1 0 0 (c / 2)
      (v_perp_covec 0 1 0) (v_perp_covec (1 / 2) 0 0) 1) = -(15 / 64 : ℝ) := by
  have h := (born_infeld_general_determinant_isomorphism
    2 1 0 0 (c / 2) (v_perp_covec 0 1 0) (v_perp_covec (1 / 2) 0 0) 1
    (by norm_num)).1
  have he : (c / 2) / c = (1 / 2 : ℝ) := by field_simp [c_ne_zero]
  norm_num [Omega_x_clebsch, Omega_y_clebsch, Omega_z_clebsch,
    omega_clebsch_2form, wedge_covec, v_perp_covec, he] at h
  exact h

-- The symmetric comparison is -1/16, not the asymmetric -15/64 above.
theorem parallel_not_volume_preserving :
    det4x4 (U_hat 2 1 0 0 (c / 2)
      (v_perp_covec 0 1 0) (v_perp_covec (1 / 2) 0 0) 1) ≠
    det4x4 (U_sym 2 1 0 0 (c / 2)
      (v_perp_covec 0 1 0) (v_perp_covec (1 / 2) 0 0) 1) := by
  rw [nonunit_parallel_matrix,
    det4x4_U_sym 2 1 0 0 (c / 2)
      (v_perp_covec 0 1 0) (v_perp_covec (1 / 2) 0 0) 1 (by norm_num)]
  norm_num

-- Keep the source's fourth conjunct explicitly classified as polynomial algebra.
example :
    (- (1 / (1 : ℝ)^4) * (1 - (0^2 + 0^2 + (1 / 2 : ℝ)^2)) -
      (0^2 + 0^2 + (1 / 2 : ℝ)^2) +
      (0 * 0 + 0 * 0 + (1 / 2 : ℝ) * (1 / 2 : ℝ))^2 = -(15 / 16 : ℝ)) :=
  (born_infeld_general_determinant_isomorphism
    2 1 0 0 0 (fun _ => 0) (fun _ => 0) 1 (by norm_num)).2.2.2

#audit_theorem AsymmetricTensor.optical_path_closed_form_antiderivative custom []
#audit_theorem AsymmetricTensor.magnitude_anomaly_log10_pos custom []
#audit_theorem AsymmetricTensor.born_infeld_general_determinant_isomorphism custom []
#audit_theorem V59Migration.magnitude_projection_migration custom []
#audit_theorem V59Migration.magnitude_log_bridge_callsite custom []
#audit_theorem V59Migration.magnitude_tenfold_positive custom []
#audit_theorem V59Migration.antiderivative_projection_callsite custom []
#audit_theorem V59Migration.determinant_projection_callsite custom []
#audit_theorem V59Migration.nonunit_parallel_matrix custom []
#audit_theorem V59Migration.parallel_not_volume_preserving custom []

end V59Migration

#audit_current_module declared []
