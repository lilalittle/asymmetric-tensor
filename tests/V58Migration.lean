import AsymmetricTensor
import ProofAudit

/-!
Call sites for the v5.8 source delta. They distinguish pointwise algebra from
curvature flatness, and preserve the new cavitation conjunction order. The full
raw-reference API comparison remains independent of these focused regressions.
-/

open AsymmetricTensor

namespace V58Migration

-- The new second conjunct is all-entry antisymmetric-sector independence.
-- Rebuild the old four-result view explicitly instead of retaining stale .2 projections.
theorem cavitation_projection_migration
    (alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4)
    (t_p_val P_static P_dyn P_shear alpha_s : ℝ)
    (h_ledger : P_c = P_static + P_dyn + P_shear)
    (h_stat : P_static = alpha_s^2 * P_c) (h_cav : alpha_s = 0) :
    (U_hat 0 alpha v_x v_y v_z d_lambda d_beta t_p_val) 0 0 = 0 ∧
    (U_anti 0 alpha v_x v_y v_z d_lambda d_beta t_p_val) 2 1 =
      alpha * (t_p_val * Omega_z_clebsch d_lambda d_beta) ∧
    P_static = 0 ∧ P_dyn + P_shear = P_c := by
  have h := topological_phase_lock_cavitation alpha v_x v_y v_z d_lambda d_beta
    t_p_val P_static P_dyn P_shear alpha_s h_ledger h_stat h_cav
  simpa only [h_cav] using
    (And.intro h.1 (And.intro h.2.2.1 (And.intro h.2.2.2.1 h.2.2.2.2)))

-- Independence is not restricted to zero/nonzero or unit admittance. Consume
-- conjunct 2 at distinct nonunit values, and keep every matrix index general.
theorem antisymmetric_nonunit_independence
    (alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ)
    (i j : Fin 4) :
    U_anti 2 alpha v_x v_y v_z d_lambda d_beta t_p_val i j =
      U_anti (-3) alpha v_x v_y v_z d_lambda d_beta t_p_val i j := by
  have h := topological_phase_lock_cavitation alpha v_x v_y v_z d_lambda d_beta
    t_p_val 0 P_c 0 0 (by ring) (by ring) rfl
  exact h.2.1 2 (-3) i j

-- Double raising flips a mixed component but not a spatial one.
theorem eta_raising_signs (M : T2) :
    raiseBoth eta_metric M 0 1 = -M 0 1 ∧
    raiseBoth eta_metric M 2 1 = M 2 1 := by
  have h := raiseBoth_eta_entries M
  exact ⟨h.2.2.1, h.2.2.2.1⟩

-- The index-raised mixed component changes sign; the displayed spatial
-- derivative survives. This is not full equivalence of conservation operators.
theorem raised_divergence_call_site
    (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ)
    (x : SpaceTime) (h_dl0 : d_lambda 0 = 0) (h_db0 : d_beta 0 = 0) :
    (fun y => raiseBoth eta_metric (U_hat_dynamic y) 0 1) =
      (fun y => -U_hat_dynamic y 0 1) ∧
    partial_deriv (fun y => raiseBoth eta_metric (U_hat_dynamic y) 3 1) 3 x =
      partial_deriv (fun y => U_hat_dynamic y 3 1) 3 x := by
  have h := raised_contravariant_divergence_bridge
    alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val x h_dl0 h_db0
  rcases h with ⟨_, _, _, h01, _, _, _, _, _, h31⟩
  exact ⟨h01, h31⟩

-- Keep admissibility hypotheses explicit and separate the open-domain bounds
-- from the denominator-free boundary-polynomial equivalence.
theorem admissible_domain_call_site
    (alpha_s alpha v_x v_y v_z v_0 P_dyn P_ambient E_x B_z : ℝ)
    (d_lambda d_beta : V4) (t_p_val : ℝ)
    (hv0 : 0 < v_0^2) (hvsub : v_0^2 < c^2)
    (hamb : P_ambient = P_c * (1 - v_0^2 / c^2))
    (hdyn0 : 0 ≤ P_dyn) (hdynsub : P_dyn < P_ambient)
    (hadm : alpha_s^2 = (P_ambient - P_dyn) / P_c) :
    0 < alpha_s^2 ∧ alpha_s^2 < 1 ∧ alpha_s ≠ 0 ∧
    1 - alpha_s^2 ≠ 0 ∧
    (((E_x^2 - 1) - (0 : ℝ)^4 * B_z^2 = 0) ↔ E_x^2 = 1) := by
  have h := counterbalanced_cavitation_regularity
    alpha_s alpha v_x v_y v_z v_0 P_dyn P_ambient E_x B_z d_lambda d_beta t_p_val
    hv0 hvsub hamb hdyn0 hdynsub hadm
  rcases h with ⟨hpos, hlt, hne, hsub, _, _, _, hboundary⟩
  exact ⟨hpos, hlt, hne, hsub, hboundary⟩

-- An explicit local boost Jacobian and metric data yield the residual. The
-- vanishing Lie component is an extra premise for the alpha_s=1 consequence.
theorem boost_operator_call_site
    (alpha_s : ℝ) (X : VectorField) (U : MetricField) (x : SpaceTime) (omega : ℝ)
    (h_omega : omega ≠ 0) (h_pos : alpha_s > 0)
    (h_homog : ∀ a : Fin 4, partial_deriv (fun y => U y 0 1) a x = 0)
    (h_dX0 : ∀ a : Fin 4,
      partial_deriv (fun y => X y a) 0 x = if a = 1 then omega else 0)
    (h_dX1 : ∀ a : Fin 4,
      partial_deriv (fun y => X y a) 1 x = if a = 0 then omega else 0)
    (h_U00 : U x 0 0 = -alpha_s^2) (h_U11 : U x 1 1 = 1 / alpha_s^2)
    (h_zero : lie_derivative X U x 0 1 = 0) : alpha_s = 1 := by
  have h := lie_derivative_boost_residual_bridge alpha_s X U x omega
    h_omega h_pos h_homog h_dX0 h_dX1 h_U00 h_U11
  exact h.2 h_zero

-- Keep the Frobenius and Lorentzian pairings separate at a pure electric input.
-- Zero Clebsch gradients remove the magnetic sector, not the temporal sign.
theorem pure_electric_pairing_signs :
    (1 / 4) * P_c * tensor_contract
      (U_anti 2 3 c 0 0 (fun _ => 0) (fun _ => 0) 1)
      (U_anti 2 3 c 0 0 (fun _ => 0) (fun _ => 0) 1) = (9 / 2) * P_c ∧
    (1 / 4) * P_c * lorentzian_contract
      (U_anti 2 3 c 0 0 (fun _ => 0) (fun _ => 0) 1)
      (U_anti 2 3 c 0 0 (fun _ => 0) (fun _ => 0) 1) = -(9 / 2) * P_c := by
  have h := frobenius_vs_lorentzian_shear_bridge
    2 3 c 0 0 (fun _ => 0) (fun _ => 0) 1
  have hc : c ≠ 0 := ne_of_gt c_pos
  norm_num [Omega_x_clebsch, Omega_y_clebsch, Omega_z_clebsch,
    omega_clebsch_2form, wedge_covec, hc] at h
  constructor <;> nlinarith [h.1, h.2]

-- Zero first metric derivatives and zero torsion yield a pointwise zero
-- connection and divergence reduction, not a curvature-flatness statement.
theorem pointwise_connection_call_site
    (Gamma : AffineConnection) (gInv S U : MetricField) (x : SpaceTime)
    (h_lc : ∀ l m n, symConnection Gamma x l m n = leviCivitaConnection gInv S x l m n)
    (h_deriv : ∀ a m n : Fin 4, partial_deriv (fun y => S y m n) a x = 0)
    (h_torsion : ∀ l m n : Fin 4, torsionTensor Gamma x l m n = 0) :
    (∀ l m n : Fin 4, Gamma x l m n = 0) ∧
    covariant_metric_divergence Gamma U x = metric_divergence U x := by
  have h := independent_flat_connection_divergence_bridge
    Gamma gInv S U x h_lc h_deriv h_torsion
  exact h.2

#audit_theorem V58Migration.cavitation_projection_migration custom []
#audit_theorem V58Migration.antisymmetric_nonunit_independence custom []
#audit_theorem V58Migration.eta_raising_signs custom []
#audit_theorem V58Migration.raised_divergence_call_site custom []
#audit_theorem V58Migration.admissible_domain_call_site custom []
#audit_theorem V58Migration.boost_operator_call_site custom []
#audit_theorem V58Migration.pure_electric_pairing_signs custom []
#audit_theorem V58Migration.pointwise_connection_call_site custom []

end V58Migration

#audit_current_module declared []
