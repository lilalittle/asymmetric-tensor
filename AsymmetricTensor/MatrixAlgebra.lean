-- ==========================================
-- SECTION 3: Assembly of the Asymmetric Metric-Tensor
-- ==========================================
variable {alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z : ℝ}
-- ==========================================
-- 3.1 The Symmetric Diagonals (Isotropic Volumetric Strain)
-- ==========================================
-- ==========================================
-- 3.2 The Antisymmetric Off-Diagonals (Transverse Shear)
-- ==========================================
-- ==========================================
-- 3.3 The Final Tensor Matrix
-- ==========================================
noncomputable def U_hat : Matrix (Fin 4) (Fin 4) ℝ :=
  ![
    ![-alpha_s^2, -alpha * (v_x / c), -alpha * (v_y / c), -alpha * (v_z / c)],
    ![alpha * (v_x / c), 1 / alpha_s^2, -alpha * (t_p * Omega_z), alpha * (t_p * Omega_y)],
    ![alpha * (v_y / c), alpha * (t_p * Omega_z), 1 / alpha_s^2, -alpha * (t_p * Omega_x)],
    ![alpha * (v_z / c), -alpha * (t_p * Omega_y), alpha * (t_p * Omega_x), 1 / alpha_s^2]
  ]
theorem symmetric_diagonals :
    U_hat 0 0 = -alpha_s^2 ∧
    U_hat 1 1 = 1 / alpha_s^2 ∧
    U_hat 2 2 = 1 / alpha_s^2 ∧
    U_hat 3 3 = 1 / alpha_s^2 := by
  simp [U_hat]
theorem antisymmetric_shear :
    U_hat 0 1 = - U_hat 1 0 ∧
    U_hat 1 2 = - U_hat 2 1 := by
  simp [U_hat]
  constructor <;> ring
noncomputable def U_sym : Matrix (Fin 4) (Fin 4) ℝ :=
  ![
    ![-alpha_s^2, 0, 0, 0],
    ![0, 1 / alpha_s^2, 0, 0],
    ![0, 0, 1 / alpha_s^2, 0],
    ![0, 0, 0, 1 / alpha_s^2]
  ]
noncomputable def U_anti : Matrix (Fin 4) (Fin 4) ℝ :=
  ![
    ![0, -alpha * (v_x / c), -alpha * (v_y / c), -alpha * (v_z / c)],
    ![alpha * (v_x / c), 0, -alpha * (t_p * Omega_z), alpha * (t_p * Omega_y)],
    ![alpha * (v_y / c), alpha * (t_p * Omega_z), 0, -alpha * (t_p * Omega_x)],
    ![alpha * (v_z / c), -alpha * (t_p * Omega_y), alpha * (t_p * Omega_x), 0]
  ]
theorem tensor_decomposition_proven :
    U_hat = U_sym + U_anti := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [U_hat, U_sym, U_anti]; try ring)
-- ==========================================
-- SECTION 6: Unified Action & Singularity Resolution
-- ==========================================
-- ==========================================
-- 6.1 Unified Action
-- ==========================================
variable {TensorSpace : Type*} [AddCommGroup TensorSpace] [Module ℝ TensorSpace]
constant U_hat_macro : TensorSpace
constant S_sym_macro : TensorSpace
constant A_anti_macro : TensorSpace
constant tensor_contract : TensorSpace → TensorSpace → ℝ
axiom contract_sym_anti : tensor_contract S_sym_macro A_anti_macro = 0
theorem unified_action_separation
    (h_decomp : U_hat_macro = S_sym_macro + A_anti_macro)
    (h_expand : tensor_contract U_hat_macro U_hat_macro =
                tensor_contract S_sym_macro S_sym_macro +
                tensor_contract A_anti_macro A_anti_macro +
                2 * tensor_contract S_sym_macro A_anti_macro) :
    tensor_contract U_hat_macro U_hat_macro = tensor_contract S_sym_macro S_sym_macro + tensor_contract A_anti_macro A_anti_macro := by
  rw [h_expand]
  have h_zero : tensor_contract S_sym_macro A_anti_macro = 0 := contract_sym_anti
  rw [h_zero]
  ring
-- ==========================================
-- 6.2 Strain Incompatibility & Riemann Curvature
-- ==========================================
-- (This section establishes the macroscopic Riemann curvature via the
-- Saint-Venant compatibility operator. Formalized conceptually in prose).
-- ==========================================
-- 6.3 Volumetric Cavitation & The Metric Lagrangian
-- ==========================================
variable (r_c : ℝ)
lemma isolate_schwarzschild_radius (M_val r_val : ℝ) (hr : r_val ≠ 0) :
  rho_tau * ((G * M_val) / r_val) = (1 / 2) * rho_tau * c^2 → r_val = 2 * G * M_val / c^2 := by
  intro h
  have hc2 : c^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt c_pos)
  have hrho_ne : rho_tau ≠ 0 := ne_of_gt rho_tau_pos
  have c_ne : c ≠ 0 := ne_of_gt c_pos
  have h1 : (rho_tau * ((G * M_val) / r_val)) * r_val * 2 / (rho_tau * c^2) =
            ((1 / 2) * rho_tau * c^2) * r_val * 2 / (rho_tau * c^2) := by rw [h]
  calc
    r_val = ((1 / 2) * rho_tau * c^2) * r_val * 2 / (rho_tau * c^2) := by field_simp [hrho_ne, hr, c_ne, hc2]; ring
    _ = (rho_tau * ((G * M_val) / r_val)) * r_val * 2 / (rho_tau * c^2) := by rw [←h1]
    _ = 2 * G * M_val / c^2 := by field_simp [hrho_ne, hr, c_ne, hc2]; ring
theorem cavitation_schwarzschild_radius (P_dyn_val P_c_val : ℝ) (hr : r_c ≠ 0)
    (h_P_c : P_c_val = (1 / 2) * rho_tau * c^2)
    (h_P_dyn : P_dyn_val = rho_tau * ((G * M) / r_c))
    (h_limit : P_dyn_val = P_c_val) :
    r_c = 2 * G * M / c^2 := by
  have h1 : rho_tau * ((G * M) / r_c) = (1 / 2) * rho_tau * c^2 := by
    rw [←h_P_dyn, ←h_P_c]
    exact h_limit
  exact isolate_schwarzschild_radius M r_c hr h1
-- ==========================================
-- 6.4 Euler-Lagrange Variation & Singularity Resolution
-- ==========================================
variable (Phi : ℝ)
variable (Laplacian Biharmonic : ℝ → ℝ)
lemma apply_source_coupling (Phi_val rho_dyn r_c_val kappa : ℝ)
    (h_Laplace_linear : Laplacian (1 - (2 * Phi_val / c^2)) = - (2 / c^2) * Laplacian Phi_val)
    (h_Biharmonic_linear : Biharmonic (1 - (2 * Phi_val / c^2)) = - (2 / c^2) * Biharmonic Phi_val)
    (h_kappa : kappa = - (8 * Real.pi * G) / c^2) :
  Laplacian (1 - (2 * Phi_val / c^2)) - r_c_val^2 * Biharmonic (1 - (2 * Phi_val / c^2)) = kappa * rho_dyn →
  Laplacian Phi_val - r_c_val^2 * Biharmonic Phi_val = 4 * Real.pi * G * rho_dyn := by
  intro h
  rw [h_Laplace_linear, h_Biharmonic_linear, h_kappa] at h
  have hc2 : c^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt c_pos)
  have c_ne : c ≠ 0 := ne_of_gt c_pos
  calc
    Laplacian Phi_val - r_c_val^2 * Biharmonic Phi_val =
      (- (c^2 / 2)) * (- (2 / c^2) * Laplacian Phi_val - r_c_val^2 * (- (2 / c^2) * Biharmonic Phi_val)) := by field_simp [c_ne, hc2]; ring
    _ = (- (c^2 / 2)) * (- (8 * Real.pi * G) / c^2 * rho_dyn) := by rw [h]
    _ = 4 * Real.pi * G * rho_dyn := by field_simp [c_ne, hc2]; ring
theorem modified_poisson_equation (S_ii rho_dyn kappa : ℝ)
    (h_Laplace_linear : Laplacian (1 - (2 * Phi / c^2)) = - (2 / c^2) * Laplacian Phi)
    (h_Biharmonic_linear : Biharmonic (1 - (2 * Phi / c^2)) = - (2 / c^2) * Biharmonic Phi)
    (h_kappa : kappa = - (8 * Real.pi * G) / c^2)
    (h_weak_field : S_ii = 1 - (2 * Phi / c^2))
    (h_variation : Laplacian S_ii - r_c^2 * Biharmonic S_ii = kappa * rho_dyn) :
    Laplacian Phi - r_c^2 * Biharmonic Phi = 4 * Real.pi * G * rho_dyn := by
  have h1 : Laplacian (1 - (2 * Phi / c^2)) - r_c^2 * Biharmonic (1 - (2 * Phi / c^2)) = kappa * rho_dyn := by
    rw [←h_weak_field]
    exact h_variation
  exact apply_source_coupling Phi rho_dyn r_c kappa h_Laplace_linear h_Biharmonic_linear h_kappa h1
-- ==========================================
-- 6.5 The Unified Wave Operator & Phase Propagation
-- ==========================================
theorem unified_wave_propagation
    (dAlembertian : TensorSpace → TensorSpace)
    (h_linear : ∀ A B, dAlembertian (A + B) = dAlembertian A + dAlembertian B)
    (h_vacuum : dAlembertian U_hat_macro = 0)
    (h_decomp : U_hat_macro = S_sym_macro + A_anti_macro) :
    dAlembertian S_sym_macro + dAlembertian A_anti_macro = 0 := by
  have h1 : dAlembertian (S_sym_macro + A_anti_macro) = 0 := by
    rw [←h_decomp]
    exact h_vacuum
  have h2 : dAlembertian (S_sym_macro + A_anti_macro) = dAlembertian S_sym_macro + dAlembertian A_anti_macro := h_linear S_sym_macro A_anti_macro
  rw [h2] at h1
  exact h1
