/-
Copyright (c) 2026 Binyamin Tsadik Bair-Mosheh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Binyamin Tsadik Bair-Mosheh
-/
module

public import AsymmetricTensor.Model

/-!
# Tensor algebra foundation and unified action

Module of Binyamin's v3.1 formalization. Declarations retained verbatim
from the author's single-file development.
-/

@[expose] public section

open Real BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars true

namespace AsymmetricTensor

-- ==========================================
-- SECTION 3: The Tensor Algebra Foundation
-- ==========================================
-- 3.1 Generalized Matrix Slicing Operators
noncomputable def symPart (U : T2) : T2 :=
  fun i j => (U i j + U j i) / 2
noncomputable def antiPart (U : T2) : T2 :=
  fun i j => (U i j - U j i) / 2
-- Proof: 4x4 real matrix decomposition.
theorem matrix_decomposition (U : T2) :
    U = symPart U + antiPart U := by
  ext i j
  change U i j = (U i j + U j i) / 2 + (U i j - U j i) / 2
  ring
-- 3.2 The Bilinear Form Bridge
noncomputable def asBilinear (U : T2) : LinearMap.BilinForm ℝ V4 :=
  Matrix.toBilin' U
-- 3.3 Concrete Tensor Contractions
noncomputable def raiseBoth (gInv A : T2) : T2 :=
  fun μ ν => ∑ α : Fin 4, ∑ β : Fin 4, gInv μ α * gInv ν β * A α β
noncomputable def contract2 (gInv U V : T2) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, U μ ν * raiseBoth gInv V μ ν
-- 3.4 Assembly of the Specific Asymmetric Metric-Tensor
-- Dimensional Audit: Every matrix entry of U_hat (-alpha_s^2, 1/alpha_s^2, alpha*(v/c), alpha*t_p*Omega) is dimensionless:
theorem unit_section3_tensor_entries_dimensionless :
    u_dimless^(2:ℤ) = u_dimless ∧
    u_dimless / (u_dimless^(2:ℤ)) = u_dimless ∧
    u_dimless * (u_c / u_c) = u_dimless ∧
    u_dimless * (u_t_p * u_omega) = u_dimless := by
  refine ⟨rfl, rfl, rfl, rfl⟩
-- Foundation tensor matrix.
noncomputable def U_hat (alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val : ℝ) : T2 :=
  Matrix.of (fun i j =>
    if i = 0 ∧ j = 0 then -alpha_s^2
    else if i = 0 ∧ j = 1 then -alpha * (v_x / c)
    else if i = 0 ∧ j = 2 then -alpha * (v_y / c)
    else if i = 0 ∧ j = 3 then -alpha * (v_z / c)
    else if i = 1 ∧ j = 0 then alpha * (v_x / c)
    else if i = 1 ∧ j = 1 then 1 / alpha_s^2
    else if i = 1 ∧ j = 2 then -alpha * (t_p_val * Omega_z)
    else if i = 1 ∧ j = 3 then alpha * (t_p_val * Omega_y)
    else if i = 2 ∧ j = 0 then alpha * (v_y / c)
    else if i = 2 ∧ j = 1 then alpha * (t_p_val * Omega_z)
    else if i = 2 ∧ j = 2 then 1 / alpha_s^2
    else if i = 2 ∧ j = 3 then -alpha * (t_p_val * Omega_x)
    else if i = 3 ∧ j = 0 then alpha * (v_z / c)
    else if i = 3 ∧ j = 1 then -alpha * (t_p_val * Omega_y)
    else if i = 3 ∧ j = 2 then alpha * (t_p_val * Omega_x)
    else if i = 3 ∧ j = 3 then 1 / alpha_s^2
    else 0
  )
-- Derived symmetric and antisymmetric tensor components.
noncomputable def U_sym (alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val : ℝ) : T2 :=
  symPart (U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val)
noncomputable def U_anti (alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val : ℝ) : T2 :=
  antiPart (U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val)
theorem symmetric_diagonals (alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val : ℝ) :
    (U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) 0 0 = -alpha_s^2 ∧ 
    (U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) 1 1 = 1 / alpha_s^2 ∧ 
    (U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) 2 2 = 1 / alpha_s^2 ∧ 
    (U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) 3 3 = 1 / alpha_s^2 := by
  dsimp [U_hat, Matrix.of_apply]
  simp
theorem antisymmetric_shear (alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val : ℝ) :
    (U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) 0 1 = - (U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) 1 0 ∧ 
    (U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) 1 2 = - (U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) 2 1 := by
  dsimp [U_hat, Matrix.of_apply]
  simp
-- Tensor decomposition theorem.
theorem tensor_decomposition_proven (alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val : ℝ) :
    U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val = 
    U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val + 
    U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val := by
  exact matrix_decomposition (U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val)
-- ==========================================
-- 3.5 Covariant 4-Velocity & Projector Construction (Resolves Issue #13 Criteria 1 & 2)
-- ==========================================
/-- The background Minkowski metric tensor η_μν = diag(-1, 1, 1, 1). -/
noncomputable def eta_metric : T2 :=
  Matrix.of (fun i j =>
    if i = 0 ∧ j = 0 then -1
    else if i = 1 ∧ j = 1 then 1
    else if i = 2 ∧ j = 2 then 1
    else if i = 3 ∧ j = 3 then 1
    else 0)
/-- The comoving 4-velocity covector u_μ = (-1, 0, 0, 0) in rest-frame coordinates. -/
def u_comoving : V4 :=
  fun i => if i = 0 then -1 else 0
/-- The transverse slip 4-covector v_⊥,μ = (0, v_x, v_y, v_z) orthogonal to u_comoving. -/
def v_perp_covec (v_x v_y v_z : ℝ) : V4 :=
  fun i => if i = 1 then v_x else if i = 2 then v_y else if i = 3 then v_z else 0
/-- The spatial vorticity 2-form ω_μν orthogonal to u_comoving. -/
noncomputable def omega_2form (Omega_x Omega_y Omega_z : ℝ) : T2 :=
  Matrix.of (fun i j =>
    if i = 1 ∧ j = 2 then -Omega_z
    else if i = 1 ∧ j = 3 then Omega_y
    else if i = 2 ∧ j = 1 then Omega_z
    else if i = 2 ∧ j = 3 then -Omega_x
    else if i = 3 ∧ j = 1 then -Omega_y
    else if i = 3 ∧ j = 2 then Omega_x
    else 0)
/-- The spatial projection tensor h_μν = η_μν + u_μ u_ν. -/
noncomputable def h_projector (u : V4) : T2 :=
  Matrix.of (fun μ ν => eta_metric μ ν + u μ * u ν)
/-- The general covariant Asymmetric Metric-Tensor (Manuscript Eq. 7):
    U_μν = -α_s^2 u_μ u_ν + (1/α_s^2) h_μν + (α/c)(u_μ v_⊥,ν - u_ν v_⊥,μ) + α t_p ω_μν. -/
noncomputable def U_covariant (alpha_s alpha c_val t_p_val : ℝ) (u v_perp : V4) (omega : T2) : T2 :=
  Matrix.of (fun μ ν =>
    -alpha_s^2 * (u μ * u ν) +
    (1 / alpha_s^2) * (h_projector u μ ν) +
    (alpha / c_val) * (u μ * v_perp ν - u ν * v_perp μ) +
    alpha * t_p_val * omega μ ν)
-- Criterion 2 (Issue #13): Proves 4-velocity normalization (u_μ u^μ = -1), projector orthogonality (u^μ h_μν = 0),
-- and slip orthogonality (u^μ v_⊥,μ = 0) in the comoving frame.
theorem comoving_orthogonality_relations (v_x v_y v_z : ℝ) (ν : Fin 4) :
    (∑ μ : Fin 4, ∑ α : Fin 4, eta_metric μ α * u_comoving μ * u_comoving α) = -1 ∧
    (∑ μ : Fin 4, ∑ α : Fin 4, eta_metric μ α * u_comoving μ * h_projector u_comoving α ν) = 0 ∧
    (∑ μ : Fin 4, ∑ α : Fin 4, eta_metric μ α * u_comoving μ * v_perp_covec v_x v_y v_z α) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [eta_metric, u_comoving, Matrix.of_apply]
  · fin_cases ν <;>
    simp [eta_metric, u_comoving, h_projector, Matrix.of_apply]
  · simp [Fin.sum_univ_four, eta_metric, u_comoving, v_perp_covec, Matrix.of_apply]
-- Criterion 1 (Issue #13): Proves that `U_hat` is the exact comoving rest-frame specialization of `U_covariant`.
theorem U_hat_eq_comoving_U_covariant (alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val : ℝ) :
    U_covariant alpha_s alpha c t_p_val u_comoving (v_perp_covec v_x v_y v_z) (omega_2form Omega_x Omega_y Omega_z) =
    U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    dsimp [U_covariant, U_hat, h_projector, eta_metric, u_comoving, v_perp_covec, omega_2form, Matrix.of_apply] <;>
    norm_num <;>
    ring

-- ==========================================
-- SECTION 6: Unified Action & Singularity Resolution
-- ==========================================
-- ==========================================
-- 6.1 Unified Action
-- ==========================================
-- PHASE 7 UPGRADE: The contraction is explicitly defined as the Frobenius inner product on T2.
noncomputable def tensor_contract (A B : T2) : ℝ :=
  (A 0 0 * B 0 0) + (A 0 1 * B 0 1) + (A 0 2 * B 0 2) + (A 0 3 * B 0 3) +
  (A 1 0 * B 1 0) + (A 1 1 * B 1 1) + (A 1 2 * B 1 2) + (A 1 3 * B 1 3) +
  (A 2 0 * B 2 0) + (A 2 1 * B 2 1) + (A 2 2 * B 2 2) + (A 2 3 * B 2 3) +
  (A 3 0 * B 3 0) + (A 3 1 * B 3 1) + (A 3 2 * B 3 2) + (A 3 3 * B 3 3)
-- The orthogonality of the symmetric and antisymmetric states is now proven.
theorem contract_sym_anti_proven (alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val : ℝ) :
    tensor_contract 
      (U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) 
      (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) = 0 := by
  dsimp [tensor_contract, U_sym, U_anti, symPart, antiPart, U_hat, Matrix.of_apply]
  simp
-- All abstract hypotheses vanish. The physical action decomposes perfectly via native matrix algebra.
theorem unified_action_separation (alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val : ℝ) :
    tensor_contract 
      (U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) 
      (U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) = 
    tensor_contract 
      (U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) 
      (U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) + 
    tensor_contract 
      (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) 
      (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) := by
  have h_decomp := tensor_decomposition_proven alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val
  rw [h_decomp]
  have h_expand : tensor_contract 
                    (U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val + U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) 
                    (U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val + U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) = 
                  tensor_contract (U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) (U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) + 
                  tensor_contract (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) + 
                  2 * tensor_contract (U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) := by
    dsimp [tensor_contract]
    ring
  rw [h_expand]
  have h_zero := contract_sym_anti_proven alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val
  rw [h_zero]
  ring
  /-- Lorentzian contraction raising both indices with the Minkowski metric η = diag(-1, 1, 1, 1) (Resolves Issue #10):
    A_μν B^μν = η^μα η^νβ A_μν B_αβ. Time-space mixed components (0,i) and (i,0) carry a negative sign (-1),
    while (0,0) and purely spatial (i,j) components carry a positive sign (+1). -/
noncomputable def lorentzian_contract (A B : T2) : ℝ :=
  (A 0 0 * B 0 0) - (A 0 1 * B 0 1) - (A 0 2 * B 0 2) - (A 0 3 * B 0 3) -
  (A 1 0 * B 1 0) + (A 1 1 * B 1 1) + (A 1 2 * B 1 2) + (A 1 3 * B 1 3) -
  (A 2 0 * B 2 0) + (A 2 1 * B 2 1) + (A 2 2 * B 2 2) + (A 2 3 * B 2 3) -
  (A 3 0 * B 3 0) + (A 3 1 * B 3 1) + (A 3 2 * B 3 2) + (A 3 3 * B 3 3)
-- Criterion 2 (Issue #10): Symmetric and antisymmetric states remain strictly orthogonal under the Lorentzian contraction:
theorem lorentzian_contract_sym_anti_proven (alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val : ℝ) :
    lorentzian_contract
      (U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val)
      (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) = 0 := by
  dsimp [lorentzian_contract, U_sym, U_anti, symPart, antiPart, U_hat, Matrix.of_apply]
  norm_num

-- Criterion 2 (Issue #10): The physical Lorentzian action separates into symmetric and antisymmetric invariants (Eq. 65):
theorem lorentzian_action_separation (alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val : ℝ) :
    lorentzian_contract
      (U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val)
      (U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) =
    lorentzian_contract
      (U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val)
      (U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) +
    lorentzian_contract
      (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val)
      (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) := by
  dsimp [lorentzian_contract, U_sym, U_anti, symPart, antiPart, U_hat, Matrix.of_apply]
  norm_num
  ring
-- Criteria 1 & 3 (Issue #10): Derives Manuscript Equation (123) directly from `U_anti`, proving the negative sign
-- for electric slip (-v_⊥^2 / c^2) and positive sign for magnetic vorticity (+t_p^2 Ω^2):
theorem lorentzian_antisymmetric_trace_eq123 (alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val : ℝ) :
    lorentzian_contract
      (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val)
      (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) =
    2 * alpha^2 * (t_p_val^2 * (Omega_x^2 + Omega_y^2 + Omega_z^2) - (v_x^2 + v_y^2 + v_z^2) / c^2) := by
  dsimp [lorentzian_contract, U_anti, antiPart, U_hat, Matrix.of_apply]
  norm_num
  ring
-- ==========================================
-- 6.2 Strain Incompatibility & Riemann Curvature
-- ==========================================
-- (This section establishes the macroscopic Riemann curvature via the 
-- Saint-Venant compatibility operator. Formalized conceptually in prose).
-- 6.3 Volumetric Cavitation & The Metric Lagrangian
variable (r_c : ℝ)
-- Dimensional Audit: Gravitational pressure saturation (rho_tau * G * M / r_c = P_c) and Schwarzschild radius (2 G M / c^2 = r_c):
theorem unit_section6_schwarzschild_cavitation :
    u_rho_tau * ((u_G * u_M_P) / u_l_p) = u_P_c ∧
    (u_G * u_M_P) / (u_c^(2:ℤ)) = u_l_p := by
  constructor <;> rfl
lemma isolate_schwarzschild_radius (M_val r_val : ℝ) (hr : r_val ≠ 0) :
  rho_tau * ((G * M_val) / r_val) = (1 / 2) * rho_tau * c^2 → r_val = (2 * G * M_val) / c^2 := by
  intro h
  have hc2 : c^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt c_pos)
  have hrho_ne : rho_tau ≠ 0 := ne_of_gt rho_tau_pos
  calc
    r_val = (r_val * (rho_tau * c^2)) / (rho_tau * c^2) := by exact (mul_div_cancel_right₀ r_val (mul_ne_zero hrho_ne hc2)).symm
    _ = (((1 / 2) * rho_tau * c^2) * r_val * 2) / (rho_tau * c^2) := by ring
    _ = ((rho_tau * ((G * M_val) / r_val)) * r_val * 2) / (rho_tau * c^2) := by rw [←h]
    _ = (rho_tau * (G * M_val) * 2) / (rho_tau * c^2) := by 
      have h_r_cancel : ((G * M_val) / r_val) * r_val = G * M_val := div_mul_cancel₀ (G * M_val) hr
      have h_sub : (rho_tau * ((G * M_val) / r_val)) * r_val = rho_tau * (((G * M_val) / r_val) * r_val) := by ring
      rw [h_sub, h_r_cancel]
    _ = (2 * G * M_val) / c^2 := by
      have h_rho_cancel : (rho_tau * (G * M_val) * 2) / (rho_tau * c^2) = (rho_tau * (2 * G * M_val)) / (rho_tau * c^2) := by ring
      rw [h_rho_cancel]
      exact mul_div_mul_left (2 * G * M_val) (c^2) hrho_ne
theorem cavitation_schwarzschild_radius (P_dyn_val P_c_val : ℝ) (hr : r_c ≠ 0)
    (h_P_c : P_c_val = (1 / 2) * rho_tau * c^2)
    (h_P_dyn : P_dyn_val = rho_tau * ((G * M) / r_c))
    (h_limit : P_dyn_val = P_c_val) :
    r_c = (2 * G * M) / c^2 := by
  have h1 : rho_tau * ((G * M) / r_c) = (1 / 2) * rho_tau * c^2 := by
    rw [←h_P_dyn, ←h_P_c]
    exact h_limit
  exact isolate_schwarzschild_radius M r_c hr h1
-- 6.4 Euler-Lagrange Variation & Singularity Resolution
variable (Phi : ℝ)
variable (Laplacian Biharmonic : ℝ → ℝ)
-- Dimensional Audit: In the 4th-order Modified Poisson Equation (nabla^2 Phi - r_c^2 nabla^4 Phi = 4 pi G rho_dyn),
-- all three terms share the exact dimensions of squared frequency ⟨-2, 2, 0⟩:
theorem unit_section6_modified_poisson :
    u_Laplacian * u_Phi = u_G * u_rho_tau ∧
    (u_l_p^(2:ℤ)) * (u_Biharmonic * u_Phi) = u_G * u_rho_tau ∧
    u_G * u_rho_tau = u_omega^(2:ℤ) := by
  refine ⟨rfl, rfl, rfl⟩
lemma apply_source_coupling (Laplace_op Biharm_op : ℝ → ℝ) (Phi_val rho_dyn r_c_val kappa : ℝ)
    (h_Laplace_linear : Laplace_op (1 - (2 * Phi_val) / c^2) = - (2 / c^2) * Laplace_op Phi_val)
    (h_Biharmonic_linear : Biharm_op (1 - (2 * Phi_val) / c^2) = - (2 / c^2) * Biharm_op Phi_val)
    (h_kappa : kappa = - (8 * Real.pi * G) / c^2) :
  Laplace_op (1 - (2 * Phi_val) / c^2) - r_c_val^2 * Biharm_op (1 - (2 * Phi_val) / c^2) = kappa * rho_dyn →
  Laplace_op Phi_val - r_c_val^2 * Biharm_op Phi_val = 4 * Real.pi * G * rho_dyn := by
  intro h
  rw [h_Laplace_linear, h_Biharmonic_linear, h_kappa] at h
  have hc2 : c^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt c_pos)
  have h_frac_eval : (- (c^2 / 2)) * (- (2 / c^2) * Laplace_op Phi_val - r_c_val^2 * (- (2 / c^2) * Biharm_op Phi_val)) = Laplace_op Phi_val - r_c_val^2 * Biharm_op Phi_val := by
    calc (- (c^2 / 2)) * (- (2 / c^2) * Laplace_op Phi_val - r_c_val^2 * (- (2 / c^2) * Biharm_op Phi_val)) 
      = (c^2 / 2) * (2 / c^2) * (Laplace_op Phi_val - r_c_val^2 * Biharm_op Phi_val) := by ring
      _ = 1 * (Laplace_op Phi_val - r_c_val^2 * Biharm_op Phi_val) := by 
        have h_one_eval : (c^2 / 2) * (2 / c^2) = (c^2 * 2) / (c^2 * 2) := by ring
        have h_two_ne : (2 : ℝ) ≠ 0 := by norm_num
        have denom_ne : c^2 * 2 ≠ 0 := mul_ne_zero hc2 h_two_ne
        have h_one : (c^2 * 2) / (c^2 * 2) = 1 := div_self denom_ne
        rw [h_one_eval, h_one]
      _ = Laplace_op Phi_val - r_c_val^2 * Biharm_op Phi_val := by ring
  calc
    Laplace_op Phi_val - r_c_val^2 * Biharm_op Phi_val = 
      (- (c^2 / 2)) * (- (2 / c^2) * Laplace_op Phi_val - r_c_val^2 * (- (2 / c^2) * Biharm_op Phi_val)) := by rw [h_frac_eval]
    _ = (- (c^2 / 2)) * (- (8 * Real.pi * G) / c^2 * rho_dyn) := by rw [h]
    _ = (c^2 / 2) * (8 * Real.pi * G / c^2) * rho_dyn := by ring
    _ = ((c^2 * 8 * Real.pi * G) / (2 * c^2)) * rho_dyn := by ring
    _ = (4 * Real.pi * G) * rho_dyn := by 
      have h_eval : ((c^2 * 8 * Real.pi * G) / (2 * c^2)) = (c^2 * (8 * Real.pi * G)) / (c^2 * 2) := by ring
      rw [h_eval]
      have h_cancel : (c^2 * (8 * Real.pi * G)) / (c^2 * 2) = (8 * Real.pi * G) / 2 := by exact mul_div_mul_left (8 * Real.pi * G) 2 hc2
      rw [h_cancel]
      ring
omit [Module ℝ V_3D] [Module ℝ Forms_2D] in
theorem modified_poisson_equation (S_ii rho_dyn kappa : ℝ)
    (h_Laplace_linear : Laplacian (1 - (2 * Phi) / c^2) = - (2 / c^2) * Laplacian Phi)
    (h_Biharmonic_linear : Biharmonic (1 - (2 * Phi) / c^2) = - (2 / c^2) * Biharmonic Phi)
    (h_kappa : kappa = - (8 * Real.pi * G) / c^2)
    (h_weak_field : S_ii = 1 - (2 * Phi) / c^2)
    (h_variation : Laplacian S_ii - r_c^2 * Biharmonic S_ii = kappa * rho_dyn) :
    Laplacian Phi - r_c^2 * Biharmonic Phi = 4 * Real.pi * G * rho_dyn := by
  have h1 : Laplacian (1 - (2 * Phi) / c^2) - r_c^2 * Biharmonic (1 - (2 * Phi) / c^2) = kappa * rho_dyn := by
    rw [←h_weak_field]
    exact h_variation
  exact apply_source_coupling Laplacian Biharmonic Phi rho_dyn r_c kappa h_Laplace_linear h_Biharmonic_linear h_kappa h1
-- 6.5 The Unified Wave Operator & Phase Propagation
theorem unified_wave_propagation (alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val : ℝ)
    (dAlembertian : T2 → T2)
    (h_linear : ∀ A B, dAlembertian (A + B) = dAlembertian A + dAlembertian B)
    (h_vacuum : dAlembertian (U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) = 0) :
    dAlembertian (U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) + 
    dAlembertian (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) = 0 := by
  have h_decomp := tensor_decomposition_proven alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val
  have h1 : dAlembertian (U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val + U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) = 0 := by
    rw [←h_decomp]
    exact h_vacuum
  rw [h_linear] at h1
  exact h1

end AsymmetricTensor
