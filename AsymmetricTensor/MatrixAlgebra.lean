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
# Asymmetric metric-tensor assembly and unified action

Module of Binyamin's v5.7 formalization. Declarations retained verbatim
from the author's single-file development.
-/

@[expose] public section

open Real BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars true

namespace AsymmetricTensor

variable {V_3D : Type} [AddCommGroup V_3D] [Module ℝ V_3D]
variable {Forms_2D : Type} [AddCommGroup Forms_2D] [Module ℝ Forms_2D]
variable {Forms_1D : Type} [AddCommGroup Forms_1D] [Module ℝ Forms_1D]
variable (wedge : Forms_1D →ₗ[ℝ] Forms_1D →ₗ[ℝ] Forms_2D)
variable (M : ℝ)
-- ======================================================================
-- SECTION 3: ASSEMBLY OF THE ASYMMETRIC METRIC-TENSOR (U_hat_μν)
-- ======================================================================

-- Dimensional Audit: Every matrix entry of U_hat (-alpha_s^2, 1/alpha_s^2, alpha*(v/c), alpha*t_p*Omega) is dimensionless:
theorem unit_section3_tensor_entries_dimensionless :
    u_dimless^(2:ℤ) = u_dimless ∧
    u_dimless / (u_dimless^(2:ℤ)) = u_dimless ∧
    u_dimless * (u_c / u_c) = u_dimless ∧
    u_dimless * (u_t_p * u_omega) = u_dimless := by
  refine ⟨rfl, rfl, rfl, rfl⟩

-- ----------------------------------------------------------------------
-- 3.0 Tensor Slicing, Bilinear Forms, and Covariant Clebsch Projector Assembly
-- ----------------------------------------------------------------------
noncomputable def symPart (U : T2) : T2 :=
  fun i j => (U i j + U j i) / 2

noncomputable def antiPart (U : T2) : T2 :=
  fun i j => (U i j - U j i) / 2

-- Theorem 7: General Rank-2 Tensor Decomposition (U_μν = U_(μν) + U_[μν], Manuscript Eq. 6)
theorem matrix_decomposition (U : T2) :
    U = symPart U + antiPart U := by
  ext i j
  change U i j = (U i j + U j i) / 2 + (U i j - U j i) / 2
  ring

noncomputable def asBilinear (U : T2) : LinearMap.BilinForm ℝ V4 :=
  Matrix.toBilin' U

noncomputable def raiseBoth (gInv A : T2) : T2 :=
  fun μ ν => ∑ α : Fin 4, ∑ β : Fin 4, gInv μ α * gInv ν β * A α β

noncomputable def contract2 (gInv U V : T2) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, U μ ν * raiseBoth gInv V μ ν

/-- Background Minkowski metric tensor `η_μν = diag(-1, 1, 1, 1)`. -/
noncomputable def eta_metric : T2 :=
  Matrix.of (fun i j =>
    if i = 0 ∧ j = 0 then -1
    else if i = 1 ∧ j = 1 then 1
    else if i = 2 ∧ j = 2 then 1
    else if i = 3 ∧ j = 3 then 1
    else 0)

/-- Comoving 4-velocity covector `u_μ = (-1, 0, 0, 0)` in rest-frame coordinates. -/
def u_comoving : V4 :=
  fun i => if i = 0 then -1 else 0

/-- Spatial 4-covector `(0, v_x, v_y, v_z)` orthogonal to `u_comoving` (used for transverse slip `v_⊥` and spatial Clebsch gradients `dλ_Ω, dβ_Ω`). -/
def v_perp_covec (v_x v_y v_z : ℝ) : V4 :=
  fun i => if i = 1 then v_x else if i = 2 then v_y else if i = 3 then v_z else 0

/-- Concrete exterior wedge product of two 4-covectors (1-forms):
    `(α ∧ β)_μν = α_μ β_ν - α_ν β_μ`. -/
noncomputable def wedge_covec (α β : V4) : T2 :=
  Matrix.of (fun μ ν => α μ * β ν - α ν * β μ)

/-- The Clebsch vorticity 2-form `ω_μν = (dλ_Ω ∧ dβ_Ω)_μν` constructed strictly via the exterior wedge product (Manuscript Eq. 2). -/
noncomputable def omega_clebsch_2form (d_lambda d_beta : V4) : T2 :=
  wedge_covec d_lambda d_beta

/-- Spatial projection tensor `h_μν = η_μν + u_μ u_ν`. -/
noncomputable def h_projector (u : V4) : T2 :=
  Matrix.of (fun μ ν => eta_metric μ ν + u μ * u ν)

/-- General Covariant Asymmetric Metric-Tensor (Manuscript Eq. 7):
    `U_μν = -α_s^2 u_μ u_ν + (1/α_s^2) h_μν + (α/c)(u ∧ v_⊥)_μν + α t_p (dλ_Ω ∧ dβ_Ω)_μν`. -/
noncomputable def U_covariant (alpha_s alpha c_val t_p_val : ℝ) (u v_perp d_lambda d_beta : V4) : T2 :=
  Matrix.of (fun μ ν =>
    -alpha_s^2 * (u μ * u ν) +
    (1 / alpha_s^2) * (h_projector u μ ν) +
    (alpha / c_val) * (wedge_covec u v_perp μ ν) +
    alpha * t_p_val * (omega_clebsch_2form d_lambda d_beta μ ν))

-- Theorem 8: Comoving 4-Velocity Normalization and Projector Orthogonality (Manuscript Section 3)
theorem comoving_orthogonality_relations (v_x v_y v_z : ℝ) (ν : Fin 4) :
    (∑ μ : Fin 4, ∑ α : Fin 4, eta_metric μ α * u_comoving μ * u_comoving α) = -1 ∧
    (∑ μ : Fin 4, ∑ α : Fin 4, eta_metric μ α * u_comoving μ * h_projector u_comoving α ν) = 0 ∧
    (∑ μ : Fin 4, ∑ α : Fin 4, eta_metric μ α * u_comoving μ * v_perp_covec v_x v_y v_z α) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [eta_metric, u_comoving, Matrix.of_apply]
  · fin_cases ν <;>
    simp [eta_metric, u_comoving, h_projector, Matrix.of_apply]
  · simp [Fin.sum_univ_four, eta_metric, u_comoving, v_perp_covec, Matrix.of_apply]

-- ----------------------------------------------------------------------
-- 3.1 The Symmetric Diagonals (Isotropic Volumetric Strain)
-- ----------------------------------------------------------------------

-- Dimensional Audit: The factorized temporal diagonal (-α_s^2 = -α_g^2 α_a^2),
-- the inverse spatial diagonal (1 / α_s^2), and their reciprocal product are dimensionless:
theorem unit_section3_1_symmetric_diagonals :
    (u_dimless^(2:ℤ)) * (u_dimless^(2:ℤ)) = u_dimless ∧
    u_dimless / (u_dimless^(2:ℤ)) = u_dimless ∧
    (u_dimless^(2:ℤ)) * (u_dimless / (u_dimless^(2:ℤ))) = u_dimless := by
  refine ⟨rfl, rfl, rfl⟩

/-- Isotropic symmetric diagonal strain matrix `diag(-α_s^2, 1/α_s^2, 1/α_s^2, 1/α_s^2)`
    representing the bulk volumetric packing of the coordinate grid (Manuscript Section 3.1). -/
noncomputable def U_isotropic_diag (alpha_s : ℝ) : T2 :=
  Matrix.of (fun μ ν =>
    if μ = ν then
      (if μ = 0 then -alpha_s^2 else 1 / alpha_s^2)
    else 0)

-- Theorem 169: Symmetric Diagonals & Isotropic Volumetric Strain (Manuscript Section 3.1)
-- Proves:
-- 1. Temporal Component (`U_00`): equates to `-α_s^2 = -(α_g^2 * α_a^2)`, the product of gravitational
--    and kinematic time dilation,
-- 2. Spatial Components (`U_ii`): equate isotropically to `1 / α_s^2` across all three spatial axes
--    (`U_11 = U_22 = U_33 = 1 / α_s^2`),
-- 3. Reciprocal Invariant: the temporal and spatial diagonals satisfy `U_00 * U_11 = -1` for all `α_s ≠ 0`,
-- 4. Unperturbed Minkowski Baseline: at full admittance (`α_s = 1`), `U_00 = -1` and `U_11 = 1`.
theorem symmetric_diagonals_isotropic_strain
    (alpha_s alpha_g alpha_a : ℝ) (ha_s : alpha_s ≠ 0)
    (h_factor : alpha_s = alpha_g * alpha_a) :
    U_isotropic_diag alpha_s 0 0 = - (alpha_g^2 * alpha_a^2) ∧
    U_isotropic_diag alpha_s 1 1 = 1 / alpha_s^2 ∧
    U_isotropic_diag alpha_s 2 2 = U_isotropic_diag alpha_s 1 1 ∧
    U_isotropic_diag alpha_s 3 3 = U_isotropic_diag alpha_s 1 1 ∧
    U_isotropic_diag alpha_s 0 0 * U_isotropic_diag alpha_s 1 1 = -1 ∧
    U_isotropic_diag 1 0 0 = -1 ∧
    U_isotropic_diag 1 1 1 = 1 := by
  have ha2 : alpha_s^2 ≠ 0 := pow_ne_zero 2 ha_s
  refine ⟨?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · change -alpha_s^2 = - (alpha_g^2 * alpha_a^2)
    rw [h_factor]
    ring
  · change -alpha_s^2 * (1 / alpha_s^2) = -1
    field_simp
  · change -(1 : ℝ)^2 = -1
    norm_num
  · change (1 : ℝ) / (1 : ℝ)^2 = 1
    norm_num

-- ----------------------------------------------------------------------
-- 3.2 The Antisymmetric Off-Diagonals (Transverse Shear)
-- ----------------------------------------------------------------------

/-- Spatial vorticity axial components extracted directly from the Clebsch exterior wedge product `dλ_Ω ∧ dβ_Ω` (Manuscript Section 3.2): -/
noncomputable def Omega_x_clebsch (d_lambda d_beta : V4) : ℝ :=
  omega_clebsch_2form d_lambda d_beta 3 2

noncomputable def Omega_y_clebsch (d_lambda d_beta : V4) : ℝ :=
  omega_clebsch_2form d_lambda d_beta 1 3

noncomputable def Omega_z_clebsch (d_lambda d_beta : V4) : ℝ :=
  omega_clebsch_2form d_lambda d_beta 2 1

-- Theorem 9: Clebsch Wedge Product Expansion of the Spatial Vorticity Components (Manuscript Eq. 2 & Section 3.2)
theorem clebsch_vorticity_components_expansion (lx ly lz bx by_val bz : ℝ) :
    Omega_x_clebsch (v_perp_covec lx ly lz) (v_perp_covec bx by_val bz) = lz * by_val - ly * bz ∧
    Omega_y_clebsch (v_perp_covec lx ly lz) (v_perp_covec bx by_val bz) = lx * bz - lz * bx ∧
    Omega_z_clebsch (v_perp_covec lx ly lz) (v_perp_covec bx by_val bz) = ly * bx - lx * by_val := by
  refine ⟨rfl, rfl, rfl⟩

lemma Omega_x_planar_zero (lx ly bx by_val : ℝ) :
    Omega_x_clebsch (v_perp_covec lx ly 0) (v_perp_covec bx by_val 0) = 0 := by
  dsimp [Omega_x_clebsch, omega_clebsch_2form, wedge_covec, v_perp_covec, Matrix.of_apply]
  ring

lemma Omega_y_planar_zero (lx ly bx by_val : ℝ) :
    Omega_y_clebsch (v_perp_covec lx ly 0) (v_perp_covec bx by_val 0) = 0 := by
  dsimp [Omega_y_clebsch, omega_clebsch_2form, wedge_covec, v_perp_covec, Matrix.of_apply]
  ring

-- ----------------------------------------------------------------------
-- 3.3 The Final Tensor Matrix
-- ----------------------------------------------------------------------

/-- The 4x4 Cartesian Asymmetric Metric-Tensor `U_hat` (Manuscript Eq. 8),
    where all vorticity entries are generated directly from the Clebsch 1-form gradients `d_lambda` and `d_beta`. -/
noncomputable def U_hat (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) : T2 :=
  Matrix.of (fun i j =>
    if i = 0 ∧ j = 0 then -alpha_s^2
    else if i = 0 ∧ j = 1 then -alpha * (v_x / c)
    else if i = 0 ∧ j = 2 then -alpha * (v_y / c)
    else if i = 0 ∧ j = 3 then -alpha * (v_z / c)
    else if i = 1 ∧ j = 0 then alpha * (v_x / c)
    else if i = 1 ∧ j = 1 then 1 / alpha_s^2
    else if i = 1 ∧ j = 2 then -alpha * (t_p_val * Omega_z_clebsch d_lambda d_beta)
    else if i = 1 ∧ j = 3 then alpha * (t_p_val * Omega_y_clebsch d_lambda d_beta)
    else if i = 2 ∧ j = 0 then alpha * (v_y / c)
    else if i = 2 ∧ j = 1 then alpha * (t_p_val * Omega_z_clebsch d_lambda d_beta)
    else if i = 2 ∧ j = 2 then 1 / alpha_s^2
    else if i = 2 ∧ j = 3 then -alpha * (t_p_val * Omega_x_clebsch d_lambda d_beta)
    else if i = 3 ∧ j = 0 then alpha * (v_z / c)
    else if i = 3 ∧ j = 1 then -alpha * (t_p_val * Omega_y_clebsch d_lambda d_beta)
    else if i = 3 ∧ j = 2 then alpha * (t_p_val * Omega_x_clebsch d_lambda d_beta)
    else if i = 3 ∧ j = 3 then 1 / alpha_s^2
    else 0
  )

noncomputable def U_sym (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) : T2 :=
  symPart (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)

noncomputable def U_anti (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) : T2 :=
  antiPart (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)

-- Theorem 10: Symmetric Diagonal Components (Isotropic Volumetric Strain, Manuscript Section 3.1)
theorem symmetric_diagonals (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) :
    (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 0 0 = -alpha_s^2 ∧
    (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 1 = 1 / alpha_s^2 ∧
    (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 2 2 = 1 / alpha_s^2 ∧
    (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 3 3 = 1 / alpha_s^2 := by
  dsimp [U_hat, Matrix.of_apply]
  simp

-- Theorem 11: Antisymmetric Off-Diagonal Shear Components (Manuscript Section 3.2)
theorem antisymmetric_shear (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) :
    (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 0 1 =
      - (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 0 ∧
    (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 2 =
      - (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 2 1 := by
  dsimp [U_hat, Matrix.of_apply]
  simp

-- Theorem 12: Asymmetric Metric-Tensor Decomposition (U_hat = U_sym + U_anti, Manuscript Eq. 6)
theorem tensor_decomposition_proven (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) :
    U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val =
    U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val +
    U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val := by
  exact matrix_decomposition (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)

-- Theorem 13: Comoving Rest-Frame Equivalence of `U_covariant` and `U_hat` under Clebsch Wedge Vorticity (Manuscript Eqs. 7–8)
theorem U_hat_eq_comoving_U_covariant (alpha_s alpha v_x v_y v_z lx ly lz bx by_val bz t_p_val : ℝ) :
    U_covariant alpha_s alpha c t_p_val u_comoving
      (v_perp_covec v_x v_y v_z) (v_perp_covec lx ly lz) (v_perp_covec bx by_val bz) =
    U_hat alpha_s alpha v_x v_y v_z (v_perp_covec lx ly lz) (v_perp_covec bx by_val bz) t_p_val := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    dsimp [U_covariant, U_hat, h_projector, eta_metric, u_comoving, v_perp_covec,
           Omega_x_clebsch, Omega_y_clebsch, Omega_z_clebsch, omega_clebsch_2form,
           wedge_covec, Matrix.of_apply] <;>
    norm_num <;>
    ring

-- ======================================================================
-- SECTION 6: UNIFIED ACTION & SINGULARITY RESOLUTION
-- ======================================================================

-- ----------------------------------------------------------------------
-- 6.1 Unified Action (Manuscript Eqs. 64–69)
-- ----------------------------------------------------------------------

/-- Euclidean Frobenius inner product on 4x4 tensors `T2`. -/
noncomputable def tensor_contract (A B : T2) : ℝ :=
  (A 0 0 * B 0 0) + (A 0 1 * B 0 1) + (A 0 2 * B 0 2) + (A 0 3 * B 0 3) +
  (A 1 0 * B 1 0) + (A 1 1 * B 1 1) + (A 1 2 * B 1 2) + (A 1 3 * B 1 3) +
  (A 2 0 * B 2 0) + (A 2 1 * B 2 1) + (A 2 2 * B 2 2) + (A 2 3 * B 2 3) +
  (A 3 0 * B 3 0) + (A 3 1 * B 3 1) + (A 3 2 * B 3 2) + (A 3 3 * B 3 3)

-- Theorem 36: Frobenius Orthogonality and Unified Action Separation under Clebsch Vorticity
theorem contract_sym_anti_proven (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) :
    tensor_contract
      (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)
      (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) = 0 := by
  dsimp [tensor_contract, U_sym, U_anti, symPart, antiPart, U_hat, Matrix.of_apply]
  simp

theorem unified_action_separation (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) :
    tensor_contract
      (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)
      (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) =
    tensor_contract
      (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)
      (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) +
    tensor_contract
      (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)
      (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) := by
  have h_decomp := tensor_decomposition_proven alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val
  rw [h_decomp]
  have h_expand : tensor_contract
                    (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val +
                     U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)
                    (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val +
                     U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) =
                  tensor_contract (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)
                                  (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) +
                  tensor_contract (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)
                                  (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) +
                  2 * tensor_contract (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)
                                      (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) := by
    dsimp [tensor_contract]
    ring
  rw [h_expand]
  have h_zero := contract_sym_anti_proven alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val
  rw [h_zero]
  ring

/-- Lorentzian contraction raising both indices with the Minkowski metric `η = diag(-1, 1, 1, 1)`:
    `A_μν B^μν = η^μα η^νβ A_μν B_αβ`. -/
noncomputable def lorentzian_contract (A B : T2) : ℝ :=
  (A 0 0 * B 0 0) - (A 0 1 * B 0 1) - (A 0 2 * B 0 2) - (A 0 3 * B 0 3) -
  (A 1 0 * B 1 0) + (A 1 1 * B 1 1) + (A 1 2 * B 1 2) + (A 1 3 * B 1 3) -
  (A 2 0 * B 2 0) + (A 2 1 * B 2 1) + (A 2 2 * B 2 2) + (A 2 3 * B 2 3) -
  (A 3 0 * B 3 0) + (A 3 1 * B 3 1) + (A 3 2 * B 3 2) + (A 3 3 * B 3 3)

-- Theorem 37: Lorentzian Action Orthogonality and Separation (U_μν U^μν = S_μν S^μν + A_μν A^μν, Manuscript Eqs. 64–65)
theorem lorentzian_contract_sym_anti_proven (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) :
    lorentzian_contract
      (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)
      (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) = 0 := by
  dsimp [lorentzian_contract, U_sym, U_anti, symPart, antiPart, U_hat, Matrix.of_apply]
  norm_num

theorem lorentzian_action_separation (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) :
    lorentzian_contract
      (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)
      (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) =
    lorentzian_contract
      (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)
      (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) +
    lorentzian_contract
      (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)
      (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) := by
  dsimp [lorentzian_contract, U_sym, U_anti, symPart, antiPart, U_hat, Matrix.of_apply]
  norm_num
  ring

-- Theorem 39: Lorentzian Antisymmetric Action Invariant from Clebsch Vorticity (Manuscript Section 6.1 & Eq. 123)
theorem lorentzian_antisymmetric_trace_eq123 (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) :
    lorentzian_contract
      (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)
      (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) =
    2 * alpha^2 * (t_p_val^2 * ((Omega_x_clebsch d_lambda d_beta)^2 +
                                (Omega_y_clebsch d_lambda d_beta)^2 +
                                (Omega_z_clebsch d_lambda d_beta)^2) -
                   (v_x^2 + v_y^2 + v_z^2) / c^2) := by
  dsimp [lorentzian_contract, U_anti, antiPart, U_hat, Matrix.of_apply]
  norm_num
  ring

-- ----------------------------------------------------------------------
-- 6.3 Volumetric Cavitation & The Metric Lagrangian (Manuscript Eqs. 74–79)
-- ----------------------------------------------------------------------
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
    r_val = (r_val * (rho_tau * c^2)) / (rho_tau * c^2) :=
      (mul_div_cancel_right₀ r_val (mul_ne_zero hrho_ne hc2)).symm
    _ = (((1 / 2) * rho_tau * c^2) * r_val * 2) / (rho_tau * c^2) := by ring
    _ = ((rho_tau * ((G * M_val) / r_val)) * r_val * 2) / (rho_tau * c^2) := by rw [←h]
    _ = (rho_tau * (G * M_val) * 2) / (rho_tau * c^2) := by
      have h_r_cancel : ((G * M_val) / r_val) * r_val = G * M_val := div_mul_cancel₀ (G * M_val) hr
      have h_sub : (rho_tau * ((G * M_val) / r_val)) * r_val = rho_tau * (((G * M_val) / r_val) * r_val) := by ring
      rw [h_sub, h_r_cancel]
    _ = (2 * G * M_val) / c^2 := by
      have h_rho_cancel : (rho_tau * (G * M_val) * 2) / (rho_tau * c^2) =
                          (rho_tau * (2 * G * M_val)) / (rho_tau * c^2) := by ring
      rw [h_rho_cancel]
      exact mul_div_mul_left (2 * G * M_val) (c^2) hrho_ne

-- Theorem 40: Volumetric Cavitation Schwarzschild Radius (r_c = 2GM/c^2, Manuscript Eq. 74)
theorem cavitation_schwarzschild_radius (P_dyn_val P_c_val : ℝ) (hr : r_c ≠ 0)
    (h_P_c : P_c_val = (1 / 2) * rho_tau * c^2)
    (h_P_dyn : P_dyn_val = rho_tau * ((G * M) / r_c))
    (h_limit : P_dyn_val = P_c_val) :
    r_c = (2 * G * M) / c^2 := by
  have h1 : rho_tau * ((G * M) / r_c) = (1 / 2) * rho_tau * c^2 := by
    rw [←h_P_dyn, ←h_P_c]
    exact h_limit
  exact isolate_schwarzschild_radius M r_c hr h1

-- ----------------------------------------------------------------------
-- 6.4 Euler-Lagrange Variation & Singularity Resolution (Manuscript Eqs. 80–84)
-- ----------------------------------------------------------------------
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
  have h_frac_eval : (- (c^2 / 2)) * (- (2 / c^2) * Laplace_op Phi_val - r_c_val^2 * (- (2 / c^2) * Biharm_op Phi_val)) =
                     Laplace_op Phi_val - r_c_val^2 * Biharm_op Phi_val := by
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
      have h_cancel : (c^2 * (8 * Real.pi * G)) / (c^2 * 2) = (8 * Real.pi * G) / 2 :=
        mul_div_mul_left (8 * Real.pi * G) 2 hc2
      rw [h_cancel]
      ring

-- Theorem 41: Fourth-Order Modified Poisson Equation (∇^2 Φ - r_c^2 ∇^4 Φ = 4πG ρ_dyn, Manuscript Eq. 84)
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

-- ----------------------------------------------------------------------
-- 6.5 The Unified Wave Operator & Phase Propagation (Manuscript Eqs. 85–88)
-- ----------------------------------------------------------------------

-- Theorem 42: Unified d'Alembertian Wave Decomposition (□ U_hat = □ S + □ A = 0, Manuscript Eqs. 85, 88)
theorem unified_wave_propagation (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ)
    (dAlembertian : T2 → T2)
    (h_linear : ∀ A B, dAlembertian (A + B) = dAlembertian A + dAlembertian B)
    (h_vacuum : dAlembertian (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) = 0) :
    dAlembertian (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) +
    dAlembertian (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) = 0 := by
  have h_decomp := tensor_decomposition_proven alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val
  have h1 : dAlembertian (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val +
                          U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) = 0 := by
    rw [←h_decomp]
    exact h_vacuum
  rw [h_linear] at h1
  exact h1

end AsymmetricTensor
