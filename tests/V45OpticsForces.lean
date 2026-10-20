import AsymmetricTensor
import ProofAudit

/-! Tests of the actual v4.5 natural-log and scaled-force contracts.
These are not substitutes for v2 base-10 photometry or finite-path theorems. -/

open AsymmetricTensor

namespace V45OpticsForcesRegression

-- Preserve the author's complete elaborated binder order, not just theorem tokens.
-- The monolith introduced v_val before the later P_dyn_val section binder.
example : ∀ (v_val P_dyn_val C r : ℝ), r ≠ 0 →
    v_val = C / r^2 → P_dyn_val = (1 / 2) * rho_tau * v_val^2 →
    P_dyn_val = (rho_tau * C^2) / (2 * r^4) :=
  isochoric_velocity_scaling

-- Common positive redshift cancels, but this API now uses the natural log.
theorem natural_tenfold_magnitude (r z : ℝ) (hr : 0 < r) (hz : 0 < 1 + z) :
    (5 * Real.log ((10 * r) * (1 + z)) + 25) -
      (5 * Real.log (r * (1 + z)) + 25) = 5 * Real.log 10 := by
  have h := logarithmic_magnitude_anomaly _ _ (10 * r) r z
    (mul_pos (by norm_num) hr) hr hz rfl rfl
  simpa only [mul_div_cancel_right₀ 10 (ne_of_gt hr)] using h

-- The historical base-10 calibration needs an explicit log(10) divisor.
-- This test-local normalization preserves that numerical regression; the raw
-- author's theorem above is still natural-log and is not a base-10 API.
theorem decimal_tenfold_calibration (r z : ℝ) (hr : 0 < r) (hz : 0 < 1 + z) :
    (5 * (Real.log ((10 * r) * (1 + z)) / Real.log 10) + 25) -
      (5 * (Real.log (r * (1 + z)) / Real.log 10) + 25) = 5 := by
  calc
    _ = ((5 * Real.log ((10 * r) * (1 + z)) + 25) -
      (5 * Real.log (r * (1 + z)) + 25)) / Real.log 10 := by ring
    _ = (5 * Real.log 10) / Real.log 10 := by
      rw [natural_tenfold_magnitude r z hr hz]
    _ = 5 := mul_div_cancel_right₀ 5 (ne_of_gt (Real.log_pos (by norm_num)))

-- Natural-log unit: an e-fold distance change gives five in this convention.
example (r : ℝ) (hr : 0 < r) :
    5 * Real.log ((Real.exp 1 * r) / r) = 5 := by
  rw [mul_div_cancel_right₀ _ (ne_of_gt hr), Real.log_exp]
  ring

example (r : ℝ) (hr : 0 < r) : 5 * Real.log (r / r) = 0 := by
  simp [ne_of_gt hr]

-- The currently available optical result is a pointwise substitution only.
example (r L : ℝ) :
    1 / (1 - P_c * (1 - Real.exp (-r / L))^2 / P_c) =
      1 / (Real.exp (-r / L) * (2 - Real.exp (-r / L))) :=
  refractive_index_substitution r L

example (L : ℝ) :
    1 / (Real.exp (-(0 : ℝ) / L) * (2 - Real.exp (-(0 : ℝ) / L))) = 1 := by
  norm_num

-- v4.5's named EM theorem contains the extra alpha factor and alpha^3.
example (m α a₀ : ℝ) (hm : m ≠ 0) (hα : α ≠ 0)
    (ha₀ : a₀ = hbar / (α * m * c)) :
    α * F_fund a₀ = (α^3 * m^2 * c^3) / hbar :=
  (interaction_hierarchy_em m α a₀ (α * hbar / (m * c)) hm hα ha₀ rfl).2.1

-- Nonunit alpha catches accidental alpha^2/alpha^3 conflation.
example : (1 / 2 : ℝ) * F_fund (hbar / ((1 / 2 : ℝ) * 1 * c)) =
    c^3 / (8 * hbar) := by
  have h := (interaction_hierarchy_em 1 (1 / 2)
    (hbar / ((1 / 2) * 1 * c)) ((1 / 2) * hbar / (1 * c))
    (by norm_num) (by norm_num) rfl rfl).2.1
  norm_num at h ⊢
  rw [h]
  ring

example : F_fund 0 = 0 := by simp [F_fund]

-- Both old ratio identities remain algebraically testable from F_fund.
-- Their physical interpretation is not selected by these test-local proofs.
theorem baseline_ratio (m α : ℝ) (hm : m ≠ 0) (hα : α ≠ 0) :
    F_fund (hbar / (α * m * c)) / F_fund (α * hbar / (m * c)) = α^4 := by
  dsimp [F_fund]
  field_simp [hm, hα, c_ne_zero, ne_of_gt hbar_pos]

theorem scaled_ratio (m α : ℝ) (hm : m ≠ 0) (hα : α ≠ 0) :
    (α * F_fund (hbar / (α * m * c))) / F_fund (α * hbar / (m * c)) = α^5 := by
  rw [mul_div_assoc, baseline_ratio m α hm hα]
  ring

example : F_fund (hbar / ((1 / 2 : ℝ) * 1 * c)) /
    F_fund ((1 / 2 : ℝ) * hbar / (1 * c)) = (1 / 16 : ℝ) := by
  have h := baseline_ratio 1 (1 / 2) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example : ((1 / 2 : ℝ) * F_fund (hbar / ((1 / 2 : ℝ) * 1 * c))) /
    F_fund ((1 / 2 : ℝ) * hbar / (1 * c)) = (1 / 32 : ℝ) := by
  have h := scaled_ratio 1 (1 / 2) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

-- The excluded zero-mass case does not satisfy the nonzero ratio conclusion.
example : F_fund (hbar / ((1 / 2 : ℝ) * 0 * c)) /
    F_fund ((1 / 2 : ℝ) * hbar / (0 * c)) ≠ (1 / 2 : ℝ)^4 := by
  norm_num [F_fund]


#audit_theorem V45OpticsForcesRegression.natural_tenfold_magnitude custom []
#audit_theorem V45OpticsForcesRegression.decimal_tenfold_calibration custom []
#audit_theorem V45OpticsForcesRegression.baseline_ratio custom []
#audit_theorem V45OpticsForcesRegression.scaled_ratio custom []
#audit_theorem AsymmetricTensor.logarithmic_magnitude_anomaly custom []
#audit_theorem AsymmetricTensor.magnitude_anomaly_divergence custom []
#audit_theorem AsymmetricTensor.refractive_index_substitution custom []
#audit_theorem AsymmetricTensor.interaction_hierarchy_em custom []

end V45OpticsForcesRegression

-- Audit this test module's retained declarations for completeness, too.
#audit_current_module declared []
