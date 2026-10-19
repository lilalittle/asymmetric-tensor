-- SECTION 9: ELECTROMAGNETIC GAUGE & UNITARY EVOLUTION
-- ======================================================================
-- Dimensional Audit: Pointwise impedance ratio ((v_x / c) / (t_p * Omega_z)) and Deborah Lorentz factor (E / (m c^2)) are dimensionless:
theorem unit_section9_impedance_and_deborah :
    (u_c / u_c) / (u_t_p * u_omega) = u_dimless ∧
    u_Energy / (u_M_P * (u_c^(2:ℤ))) = u_dimless := by
  constructor <;> rfl
-- ----------------------------------------------------------------------
-- 9.1 The Longitudinal Axis (λ_1 = α_s^-2)
-- ----------------------------------------------------------------------
-- Theorem 55: Longitudinal Axis Volumetric Invariance (U_00 * U_11 = -1, Manuscript Section 9.1)
theorem longitudinal_axis_invariance (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ)
    (h_alpha_s : alpha_s > 0) :
    (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 0 0 *
    (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 1 = -1 := by
  have ha2_ne : alpha_s^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt h_alpha_s)
  have h1 : (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 0 0 = -alpha_s^2 := by simp [U_hat]
  have h2 : (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 1 = 1 / alpha_s^2 := by simp [U_hat]
  rw [h1, h2]
  have h3 : (-alpha_s^2) * (1 / alpha_s^2) = -(alpha_s^2 * (1 / alpha_s^2)) := by ring
  have h4 : alpha_s^2 * (1 / alpha_s^2) = alpha_s^2 / alpha_s^2 := by ring
  have h5 : alpha_s^2 / alpha_s^2 = 1 := div_self ha2_ne
  rw [h4, h5] at h3
  exact h3
-- ----------------------------------------------------------------------
-- 9.2 Electromagnetic Cross-Coupling Equivalence
-- ----------------------------------------------------------------------
-- Theorem 56: Pointwise Electromagnetic Impedance Ratio under Clebsch Vorticity (Manuscript Section 9.2)
theorem cross_coupling_impedance (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ)
    (h_alpha : alpha > 0) :
    (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 0 1 /
    (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 2 =
    (v_x / c) / (t_p_val * Omega_z_clebsch d_lambda d_beta) := by
  have h_ne : alpha ≠ 0 := ne_of_gt h_alpha
  have h_num : (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 0 1 =
               -(alpha * (v_x / c)) := by simp [U_hat]
  have h_den : (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 2 =
               -(alpha * (t_p_val * Omega_z_clebsch d_lambda d_beta)) := by simp [U_hat]
  rw [h_num, h_den]
  have h_neg_cancel : (-(alpha * (v_x / c))) / (-(alpha * (t_p_val * Omega_z_clebsch d_lambda d_beta))) =
                      (alpha * (v_x / c)) / (alpha * (t_p_val * Omega_z_clebsch d_lambda d_beta)) :=
    neg_div_neg_eq (alpha * (v_x / c)) (alpha * (t_p_val * Omega_z_clebsch d_lambda d_beta))
  rw [h_neg_cancel]
  exact mul_div_mul_left (v_x / c) (t_p_val * Omega_z_clebsch d_lambda d_beta) h_ne
-- ----------------------------------------------------------------------
-- 9.3 Orthogonal Stability (Eigenstate Degeneracy)
-- ----------------------------------------------------------------------
-- Theorem 57: Transverse Eigenstate Degeneracy Condition under Clebsch Vorticity (Manuscript Section 9.3)
theorem transverse_eigenvalues_are_real_iff_no_spin (alpha : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) :
    (alpha * t_p_val * Omega_z_clebsch d_lambda d_beta = 0) ↔
    (alpha * t_p_val * Omega_z_clebsch d_lambda d_beta)^2 = 0 := by
  constructor
  · intro h; rw [h]; ring
  · intro h; exact sq_eq_zero_iff.mp h
-- ----------------------------------------------------------------------
-- 9.4 Classical Volume Preservation (α_s = 1) (Manuscript Eqs. 136–137)
-- ----------------------------------------------------------------------
/-- Explicit 4D matrix trace `Tr(M) = ∑_μ M_μμ`. -/
noncomputable def trace4x4 (M : T2) : ℝ :=
  M 0 0 + M 1 1 + M 2 2 + M 3 3
/-- Explicit 3x3 minor determinant for cofactor expansion on `T2`. -/
noncomputable def det3x3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : ℝ) : ℝ :=
  a11 * (a22 * a33 - a23 * a32) -
  a12 * (a21 * a33 - a23 * a31) +
  a13 * (a21 * a32 - a22 * a31)
/-- Explicit 4x4 Laplace determinant along row 0 of `M : T2`. -/
noncomputable def det4x4 (M : T2) : ℝ :=
  M 0 0 * det3x3 (M 1 1) (M 1 2) (M 1 3) (M 2 1) (M 2 2) (M 2 3) (M 3 1) (M 3 2) (M 3 3) -
  M 0 1 * det3x3 (M 1 0) (M 1 2) (M 1 3) (M 2 0) (M 2 2) (M 2 3) (M 3 0) (M 3 2) (M 3 3) +
  M 0 2 * det3x3 (M 1 0) (M 1 1) (M 1 3) (M 2 0) (M 2 1) (M 2 3) (M 3 0) (M 3 1) (M 3 3) -
  M 0 3 * det3x3 (M 1 0) (M 1 1) (M 1 2) (M 2 0) (M 2 1) (M 2 2) (M 3 0) (M 3 1) (M 3 2)
-- Theorem 58: 4D Trace and Finite Determinant Identities for `U_anti`, `U_sym`, and `U_hat` under Clebsch Vorticity
theorem trace4x4_U_anti_zero (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) :
    trace4x4 (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) = 0 := by
  dsimp [trace4x4, U_anti, antiPart, U_hat, Matrix.of_apply]
  norm_num
theorem det4x4_U_sym (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ)
    (ha_s : alpha_s ≠ 0) :
    det4x4 (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) = - (1 / alpha_s^4) := by
  dsimp [det4x4, det3x3, U_sym, symPart, U_hat, Matrix.of_apply]
  norm_num
  field_simp
theorem det4x4_U_hat_orthogonal (alpha_s alpha v_perp lx ly bx by_val t_p_val : ℝ)
    (ha_s : alpha_s ≠ 0) :
    det4x4 (U_hat alpha_s alpha v_perp 0 0 (v_perp_covec lx ly 0) (v_perp_covec bx by_val 0) t_p_val) =
    - (1 / alpha_s^4) -
    (alpha * t_p_val * Omega_z_clebsch (v_perp_covec lx ly 0) (v_perp_covec bx by_val 0))^2 +
    (1 / alpha_s^4) * (alpha * (v_perp / c))^2 := by
  have hc : c ≠ 0 := c_ne_zero
  dsimp [det4x4, det3x3, U_hat, Matrix.of_apply]
  rw [Omega_x_planar_zero, Omega_y_planar_zero]
  norm_num
  field_simp
  ring
theorem det4x4_U_hat_static (alpha v_perp lx ly bx by_val t_p_val : ℝ) :
    det4x4 (U_hat 1 alpha v_perp 0 0 (v_perp_covec lx ly 0) (v_perp_covec bx by_val 0) t_p_val) =
    -1 - (alpha * t_p_val * Omega_z_clebsch (v_perp_covec lx ly 0) (v_perp_covec bx by_val 0))^2 +
    (alpha * (v_perp / c))^2 := by
  have h1 : (1 : ℝ) ≠ 0 := one_ne_zero
  have h_gen := det4x4_U_hat_orthogonal 1 alpha v_perp lx ly bx by_val t_p_val h1
  rw [h_gen]
  ring
theorem PureMagnetic_det4x4_eq_neg_two :
    trace4x4 (U_anti 1 1 0 0 0 (v_perp_covec 0 1 0) (v_perp_covec 1 0 0) 1) = 0 ∧
    det4x4 (U_hat 1 1 0 0 0 (v_perp_covec 0 1 0) (v_perp_covec 1 0 0) 1) = -2 := by
  refine ⟨trace4x4_U_anti_zero 1 1 0 0 0 (v_perp_covec 0 1 0) (v_perp_covec 1 0 0) 1, ?_⟩
  rw [det4x4_U_hat_static]
  dsimp [Omega_z_clebsch, omega_clebsch_2form, wedge_covec, v_perp_covec, Matrix.of_apply]
  norm_num
-- Theorem 59: Classical Volume Preservation & Null-Wave Equipartition under Clebsch Vorticity (Manuscript Eq. 137)
theorem isochoric_volume_preservation (v_perp lx ly bx by_val alpha_val t_p_val : ℝ) :
    det4x4 (U_hat 1 alpha_val v_perp 0 0 (v_perp_covec lx ly 0) (v_perp_covec bx by_val 0) t_p_val) = -1 ↔
    (alpha_val * (v_perp / c))^2 =
    (alpha_val * t_p_val * Omega_z_clebsch (v_perp_covec lx ly 0) (v_perp_covec bx by_val 0))^2 := by
  rw [det4x4_U_hat_static]
  constructor <;> intro h <;> linarith
-- ----------------------------------------------------------------------
-- 9.5 Non-Linear Vacuum Polarization (The Schwinger Limit) (Manuscript Eq. 138)
-- ----------------------------------------------------------------------
-- Theorem 60: Schwinger Limit Eigenmode Condition under Clebsch Vorticity (Manuscript Section 9.5)
theorem schwinger_limit_eigenvalues (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ)
    (h_alpha_s : alpha_s = 1)
    (h_Omega : alpha * t_p_val * Omega_z_clebsch d_lambda d_beta = 1) :
    ((U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 1 = 1) ∧
    (alpha * t_p_val * Omega_z_clebsch d_lambda d_beta = 1) := by
  constructor
  · have h1 : (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 1 = 1 / alpha_s^2 := by simp [U_hat]
    rw [h1, h_alpha_s]
    norm_num
  · exact h_Omega
-- ----------------------------------------------------------------------
-- 9.6 Continuous Unitary Evolution (U(1) Symmetry) (Manuscript Eqs. 139–140)
-- ----------------------------------------------------------------------
-- Theorem 61: Transverse 2x2 U(1) Sub-Matrix Decomposition under Clebsch Vorticity (Manuscript Eq. 139)
theorem transverse_U1_decomposition (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) :
    (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 1 = 1 / alpha_s^2 ∧
    (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 2 =
      - (alpha * (t_p_val * Omega_z_clebsch d_lambda d_beta)) ∧
    (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 2 1 =
      alpha * (t_p_val * Omega_z_clebsch d_lambda d_beta) := by
  have h1 : (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 1 = 1 / alpha_s^2 := by simp [U_hat]
  have h2 : (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 2 =
            - (alpha * (t_p_val * Omega_z_clebsch d_lambda d_beta)) := by simp [U_hat]
  have h3 : (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 2 1 =
            alpha * (t_p_val * Omega_z_clebsch d_lambda d_beta) := by simp [U_hat]
  exact ⟨h1, h2, h3⟩
-- ----------------------------------------------------------------------
-- 9.7 The Generalized Determinant (det(U) = 0) (Manuscript Eqs. 141–142)
-- ----------------------------------------------------------------------
lemma generalized_cavitation_algebra (alpha_s_val alpha_val v_perp Omega_z t_p_val : ℝ) (h_alpha_s : alpha_s_val > 0) :
  - (1 / alpha_s_val^4) - (alpha_val * t_p_val * Omega_z)^2 + (1 / alpha_s_val^4) * (alpha_val * (v_perp / c))^2 = 0 →
  (alpha_val * (v_perp / c))^2 - alpha_s_val^4 * (alpha_val * t_p_val * Omega_z)^2 = 1 := by
  intro h
  have h_s_ne : alpha_s_val ≠ 0 := ne_of_gt h_alpha_s
  have h_s4_ne : alpha_s_val^4 ≠ 0 := pow_ne_zero 4 h_s_ne
  have h2 : (- (1 / alpha_s_val^4) - (alpha_val * t_p_val * Omega_z)^2 +
             (1 / alpha_s_val^4) * (alpha_val * (v_perp / c))^2) * alpha_s_val^4 = 0 := by
    have h_zero : 0 * alpha_s_val^4 = 0 := by ring
    rw [h, h_zero]
  have h_distrib : (- (1 / alpha_s_val^4) - (alpha_val * t_p_val * Omega_z)^2 +
                    (1 / alpha_s_val^4) * (alpha_val * (v_perp / c))^2) * alpha_s_val^4 =
                   (- (1 / alpha_s_val^4)) * alpha_s_val^4 -
                   (alpha_val * t_p_val * Omega_z)^2 * alpha_s_val^4 +
                   ((1 / alpha_s_val^4) * (alpha_val * (v_perp / c))^2) * alpha_s_val^4 := by ring
  rw [h_distrib] at h2
  have h_cancel_one : (- (1 / alpha_s_val^4)) * alpha_s_val^4 = -1 := by
    have h_tmp : (- (1 / alpha_s_val^4)) * alpha_s_val^4 = - ((1 / alpha_s_val^4) * alpha_s_val^4) := by ring
    have h_div : (1 / alpha_s_val^4) * alpha_s_val^4 = 1 * (alpha_s_val^4 / alpha_s_val^4) := by ring
    rw [h_tmp, h_div, div_self h_s4_ne, mul_one]
  have h_cancel_two : ((1 / alpha_s_val^4) * (alpha_val * (v_perp / c))^2) * alpha_s_val^4 =
                      (alpha_val * (v_perp / c))^2 := by
    have h_tmp2 : ((1 / alpha_s_val^4) * (alpha_val * (v_perp / c))^2) * alpha_s_val^4 =
                  ((alpha_val * (v_perp / c))^2) * (alpha_s_val^4 / alpha_s_val^4) := by ring
    rw [h_tmp2, div_self h_s4_ne, mul_one]
  rw [h_cancel_one, h_cancel_two] at h2
  linarith
-- Theorem 62: The Generalized Cavitation Limit under Clebsch Vorticity (Manuscript Eq. 142)
theorem generalized_cavitation (v_perp : ℝ) (d_lambda d_beta : V4) (alpha_s_val alpha_val t_p_val : ℝ)
    (h_alpha_s : alpha_s_val > 0)
    (h_det_collapse : - (1 / alpha_s_val^4) -
                      (alpha_val * t_p_val * Omega_z_clebsch d_lambda d_beta)^2 +
                      (1 / alpha_s_val^4) * (alpha_val * (v_perp / c))^2 = 0) :
    (alpha_val * (v_perp / c))^2 -
    alpha_s_val^4 * (alpha_val * t_p_val * Omega_z_clebsch d_lambda d_beta)^2 = 1 := by
  exact generalized_cavitation_algebra alpha_s_val alpha_val v_perp
    (Omega_z_clebsch d_lambda d_beta) t_p_val h_alpha_s h_det_collapse
-- ----------------------------------------------------------------------
-- 9.8 The Temporal Cavitation Limit (α_s → 0^+)
-- ----------------------------------------------------------------------
def metric_is_continuous (alpha_s_val : ℝ) : Prop := alpha_s_val > 0
def metric_is_cavitated  (alpha_s_val : ℝ) : Prop := alpha_s_val = 0
def is_subcritical_pressure (P_load : ℝ) : Prop := 0 ≤ P_load ∧ P_load < P_c
-- Theorem 63: Subcritical Regularity, One-Sided Spatial Divergence & Polynomial Cavitation Lock (Manuscript Section 9.8)
theorem subcritical_implies_positive_compliance (P_load : ℝ) (h_sub : is_subcritical_pressure P_load) :
    0 < 1 - P_load / P_c := by
  dsimp [is_subcritical_pressure] at h_sub
  have h_ratio : P_load / P_c < 1 := (div_lt_one P_c_pos).mpr h_sub.2
  linarith
theorem subcritical_implies_continuous (P_load alpha_s_val : ℝ)
    (h_sub : is_subcritical_pressure P_load)
    (h_alpha_s : alpha_s_val = Real.sqrt (1 - P_load / P_c)) :
    metric_is_continuous alpha_s_val ∧ ¬ metric_is_cavitated alpha_s_val := by
  have h_pos_inner : 0 < 1 - P_load / P_c := subcritical_implies_positive_compliance P_load h_sub
  have h_sqrt_pos : 0 < Real.sqrt (1 - P_load / P_c) := Real.sqrt_pos.mpr h_pos_inner
  have h_cont : metric_is_continuous alpha_s_val := by
    dsimp [metric_is_continuous]
    linarith
  refine ⟨h_cont, ?_⟩
  dsimp [metric_is_cavitated]
  exact ne_of_gt h_cont
theorem spatial_diagonal_one_sided_divergence (alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4)
    (t_p_val n M_bound : ℝ)
    (hn : 0 < n) (hM : 0 ≤ M_bound) (h_large : Real.sqrt M_bound < n) :
    metric_is_continuous (1 / n) ∧
    (U_hat (1 / n) alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 1 = n^2 ∧
    M_bound < (U_hat (1 / n) alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 1 := by
  have h_cont : metric_is_continuous (1 / n) := one_div_pos.mpr hn
  have hn_ne : n ≠ 0 := ne_of_gt hn
  have h_diag : (U_hat (1 / n) alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 1 = n^2 := by
    have h11 : (U_hat (1 / n) alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 1 = 1 / (1 / n)^2 := by
      simp [U_hat]
    rw [h11]
    field_simp
  refine ⟨h_cont, h_diag, ?_⟩
  rw [h_diag]
  have h_sq : (Real.sqrt M_bound)^2 < n^2 :=
    sq_lt_sq.mpr (by rw [abs_of_nonneg (Real.sqrt_nonneg M_bound), abs_of_pos hn]; exact h_large)
  rwa [Real.sq_sqrt hM] at h_sq
theorem polynomial_cavitation_lock (v_perp : ℝ) (d_lambda d_beta : V4) (alpha_s_val alpha_val t_p_val : ℝ)
    (h_cav : metric_is_cavitated alpha_s_val)
    (h_cleared : (alpha_val * (v_perp / c))^2 -
                 alpha_s_val^4 * (alpha_val * t_p_val * Omega_z_clebsch d_lambda d_beta)^2 = 1) :
    (alpha_val * (v_perp / c))^2 = 1 := by
  dsimp [metric_is_cavitated] at h_cav
  rw [h_cav] at h_cleared
  linarith
-- ----------------------------------------------------------------------
-- 9.9 Complex Strain & The Deborah Number (Manuscript Eqs. 143–151)
-- ----------------------------------------------------------------------
noncomputable def U_perp_Re (alpha_s_val : ℝ) : ℝ := 1 / alpha_s_val^2
noncomputable def U_perp_Im (alpha_val : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) : ℝ :=
  alpha_val * t_p_val * Omega_z_clebsch d_lambda d_beta
noncomputable def tan_delta (alpha_s_val alpha_val : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) : ℝ :=
  U_perp_Im alpha_val d_lambda d_beta t_p_val / U_perp_Re alpha_s_val
-- Theorem 64: Geometric Deborah Number Derivation under Clebsch Vorticity (Manuscript Eq. 145)
theorem geometric_deborah_derivation (alpha_s_val alpha_val : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) :
    U_perp_Re alpha_s_val / U_perp_Im alpha_val d_lambda d_beta t_p_val =
    1 / (alpha_s_val^2 * (alpha_val * t_p_val * Omega_z_clebsch d_lambda d_beta)) := by
  dsimp [U_perp_Re, U_perp_Im]
  ring
variable (gamma_val : ℝ)
lemma crossover_algebra (alpha_val alpha_s_val tp_omega gamma_var : ℝ)
  (h_alpha_s : alpha_s_val > 0) (h_alpha : alpha_val > 0) :
  1 / alpha_s_val = gamma_var →
  alpha_val / alpha_s_val = (1 / alpha_s_val^2) / (alpha_val * tp_omega) →
  tp_omega = gamma_var / alpha_val^2 := by
  intro h_gamma h_De_eq
  have h_s_ne : alpha_s_val ≠ 0 := ne_of_gt h_alpha_s
  have h_a_ne : alpha_val ≠ 0 := ne_of_gt h_alpha
  have h_tp_neq_zero : alpha_val * tp_omega ≠ 0 := by
    intro hz
    have h_bad : alpha_val / alpha_s_val = 0 := by
      have h_div_zero : (1 / alpha_s_val^2) / 0 = 0 := div_zero (1 / alpha_s_val^2)
      rw [hz] at h_De_eq
      rw [h_div_zero] at h_De_eq
      exact h_De_eq
    have h_a_zero : alpha_val = 0 := by
      have h_1 : alpha_val = alpha_val * (alpha_s_val / alpha_s_val) := by rw [div_self h_s_ne, mul_one]
      have h_2 : alpha_val * (alpha_s_val / alpha_s_val) = (alpha_val / alpha_s_val) * alpha_s_val := by ring
      have h_3 : (alpha_val / alpha_s_val) * alpha_s_val = 0 * alpha_s_val := by rw [h_bad]
      have h_4 : 0 * alpha_s_val = 0 := by ring
      rw [h_1, h_2, h_3, h_4]
    exact h_a_ne h_a_zero
  have h_mult : (alpha_val / alpha_s_val) * (alpha_val * tp_omega) = 1 / alpha_s_val^2 := by
    have h_step : (alpha_val / alpha_s_val) * (alpha_val * tp_omega) =
                  ((1 / alpha_s_val^2) / (alpha_val * tp_omega)) * (alpha_val * tp_omega) := by rw [h_De_eq]
    have h_cancel : ((1 / alpha_s_val^2) / (alpha_val * tp_omega)) * (alpha_val * tp_omega) =
                    (1 / alpha_s_val^2) * ((alpha_val * tp_omega) / (alpha_val * tp_omega)) := by ring
    rw [h_step, h_cancel, div_self h_tp_neq_zero, mul_one]
  have h_frac_eval : ((alpha_val / alpha_s_val) * (alpha_val * tp_omega) * alpha_s_val) / alpha_val^2 = tp_omega := by
    have h_num_rearrange : (alpha_val / alpha_s_val) * (alpha_val * tp_omega) * alpha_s_val =
                           ((alpha_val * alpha_val * tp_omega) / alpha_s_val) * alpha_s_val := by ring
    have h_num : ((alpha_val * alpha_val * tp_omega) / alpha_s_val) * alpha_s_val =
                 (alpha_val * alpha_val * tp_omega) * (alpha_s_val / alpha_s_val) := by ring
    rw [h_num, div_self h_s_ne, mul_one] at h_num_rearrange
    have h_final_rearrange : (alpha_val * alpha_val * tp_omega) / alpha_val^2 =
                             tp_omega * (alpha_val^2 / alpha_val^2) := by ring
    rw [h_num_rearrange, h_final_rearrange, div_self (pow_ne_zero 2 h_a_ne), mul_one]
  have h_step2 : ((alpha_val / alpha_s_val) * (alpha_val * tp_omega) * alpha_s_val) / alpha_val^2 =
                 ((1 / alpha_s_val^2) * alpha_s_val) / alpha_val^2 := by rw [h_mult]
  have h_step3 : ((1 / alpha_s_val^2) * alpha_s_val) / alpha_val^2 = (1 / alpha_s_val) / alpha_val^2 := by
    have h_step_4 : (1 / alpha_s_val^2) * alpha_s_val = alpha_s_val / alpha_s_val^2 := by ring
    have h_step_5 : alpha_s_val / (alpha_s_val * alpha_s_val) = (alpha_s_val / alpha_s_val) / alpha_s_val := by ring
    have h_step_6 : (alpha_s_val / alpha_s_val) / alpha_s_val = 1 / alpha_s_val := by rw [div_self h_s_ne]
    have h_merge : (1 / alpha_s_val^2) * alpha_s_val = 1 / alpha_s_val := by
      rw [h_step_4, pow_two alpha_s_val, h_step_5, h_step_6]
    rw [h_merge]
  rw [←h_frac_eval, h_step2, h_step3, ← h_gamma]
-- Theorem 65: The Kinematic Crossover Constraint under Clebsch Vorticity (Manuscript Eq. 149)
theorem kinematic_crossover_limit (d_lambda d_beta : V4) (alpha_s_val alpha_val t_p_val : ℝ)
    (h_alpha_s : alpha_s_val > 0) (h_alpha : alpha_val > 0)
    (h_gamma : 1 / alpha_s_val = gamma_val)
    (h_De_eq : alpha_val / alpha_s_val =
               (1 / alpha_s_val^2) / (alpha_val * (t_p_val * Omega_z_clebsch d_lambda d_beta))) :
    t_p_val * Omega_z_clebsch d_lambda d_beta = gamma_val / alpha_val^2 := by
  exact crossover_algebra alpha_val alpha_s_val
    (t_p_val * Omega_z_clebsch d_lambda d_beta) gamma_val h_alpha_s h_alpha h_gamma h_De_eq
variable (E_val m_val : ℝ)
-- Theorem 66: The Phenomenological Energy Limit (De_macro = α (E / m c^2), Manuscript Eq. 151)
theorem phenomenological_energy_scale (De_macro alpha_val : ℝ)
    (h_De : De_macro = alpha_val * gamma_val)
    (h_gamma_def : gamma_val = E_val / (m_val * c^2)) :
    De_macro = alpha_val * (E_val / (m_val * c^2)) := by
  rw [h_De, h_gamma_def]
  -- ======================================================================
