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
public import AsymmetricTensor.MatrixAlgebra

/-!
# Continuous field equation, equation of motion, and conformal symmetry

Module of Binyamin's v5.7 formalization. Declarations retained verbatim
from the author's single-file development.
-/

@[expose] public section

open Real BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars true

namespace AsymmetricTensor

variable {V_3D : Type} [AddCommGroup V_3D] [Module ℝ V_3D]
variable {Forms_0D : Type} [AddCommGroup Forms_0D] [Module ℝ Forms_0D]
variable {Forms_1D : Type} [AddCommGroup Forms_1D] [Module ℝ Forms_1D]
variable (d0 : Forms_0D →ₗ[ℝ] Forms_1D)
variable (smul_form  : Forms_0D → Forms_1D → Forms_1D)
variable (v_esc : ℝ)
variable (v_parallel v_perp_mag v_circ : ℝ)
-- ======================================================================
-- SECTION 4: THE CONTINUOUS FIELD EQUATION
-- ======================================================================

-- ----------------------------------------------------------------------
-- 4.0 Constitutive Cauchy Stress & Hyperelastic Extension (Manuscript Eqs. 9–11)
-- ----------------------------------------------------------------------

/-- The Constitutive Asymmetric Cauchy Stress Tensor (Manuscript Eq. 9):
    `T_μν = P_c (U_μν - η_μν)`. -/
noncomputable def constitutive_stress (U : T2) : T2 :=
  Matrix.of (fun μ ν => P_c * (U μ ν - eta_metric μ ν))

/-- Non-linear Hyperelastic Stress Extension near topological boundaries (Manuscript Eq. 11). -/
noncomputable def hyperelastic_stress (chi_hyp : ℝ) (U : T2) : T2 :=
  Matrix.of (fun μ ν =>
    P_c * (U μ ν - eta_metric μ ν) +
    chi_hyp * ((∑ α : Fin 4, ∑ β : Fin 4, U μ α * eta_metric α β * U β ν) - eta_metric μ ν))

/-- Unperturbed Minkowski vacuum second invariant `I_2^(vac) = η_μν η^μν`. -/
noncomputable def I_2_vac : ℝ :=
  (-1) * (-1) + (1) * (1) + (1) * (1) + (1) * (1)

-- Theorem 14: Minkowski Baseline Second Invariant (I_2^(vac) = 4, Manuscript Eq. 10)
theorem I_2_vac_equals_4 : I_2_vac = 4 := by
  dsimp [I_2_vac]
  ring

-- ----------------------------------------------------------------------
-- 4.1 Energy Density and Structural Stress (Manuscript Eqs. 12–13)
-- ----------------------------------------------------------------------
variable (P_static P_shear : ℝ)

-- Theorem 15: Temporal Stress Energy Density (T_00 = ΔP_macro + P_dyn + P_shear, Manuscript Eq. 12)
theorem energy_density_proof
    (h_P_static : P_static = P_c - (P_g v_esc + P_dyn_components v_parallel v_perp_mag v_circ + P_shear)) :
    P_c - P_static = P_g v_esc + P_dyn_components v_parallel v_perp_mag v_circ + P_shear := by
  rw [h_P_static]
  ring

-- Theorem 16: Spatial Structural Cauchy Stress (T_ii, Manuscript Eq. 13)
theorem spatial_stress_proof
    (h_P_static : P_static = P_c - (P_g v_esc + P_dyn_components v_parallel v_perp_mag v_circ + P_shear)) :
    P_c * ((P_c - P_static) / P_static) =
    P_c * ((P_g v_esc + P_dyn_components v_parallel v_perp_mag v_circ + P_shear) / P_static) := by
  have h1 : P_c - P_static = P_g v_esc + P_dyn_components v_parallel v_perp_mag v_circ + P_shear := by
    rw [h_P_static]
    ring
  rw [h1]

-- ----------------------------------------------------------------------
-- 4.2 The Cosmological Constant & Metric Density (ρ_τ) (Manuscript Eqs. 14–23)
-- ----------------------------------------------------------------------

-- Dimensional Audit: Verifies c^7/(hbar G^2) = P_c, c^5/(hbar G^2) = rho_tau, Lambda = 2/R_h^2, and rho_tau * Phi = P_c:
theorem unit_section4_cosmology_and_density :
    (u_c^(7:ℤ)) / (u_hbar * (u_G^(2:ℤ))) = u_P_c ∧
    (u_c^(5:ℤ)) / (u_hbar * (u_G^(2:ℤ))) = u_rho_tau ∧
    ((u_c^(4:ℤ)) / u_G) / u_Area = u_P_c ∧
    (u_G * u_P_c) / (u_c^(4:ℤ)) = u_Curvature ∧
    u_Phi = (u_G * u_M_P) / u_l_p ∧
    u_rho_tau * u_Phi = u_P_c := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma reduce_density_algebra (P_val : ℝ) :
  (1 / 2) * rho_tau * c^2 = P_val → rho_tau = 2 * P_val / c^2 := by
  intro h
  have hc2 : c^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt c_pos)
  calc
    rho_tau = (rho_tau * c^2) / c^2 := (mul_div_cancel_right₀ rho_tau hc2).symm
    _ = (((1 / 2) * rho_tau * c^2) * 2) / c^2 := by ring
    _ = (P_val * 2) / c^2 := by rw [h]
    _ = 2 * P_val / c^2 := by ring

lemma reduce_c7_c2 :
  2 * (c^7 / (4 * Real.pi * hbar * G^2)) / c^2 = (1 / (2 * Real.pi)) * (c^5 / (hbar * G^2)) := by
  have hc2 : c^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt c_pos)
  have hG2 : G^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt G_pos)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hbar_ne : hbar ≠ 0 := ne_of_gt hbar_pos
  field_simp
  ring

-- Theorem 17: Baseline Metric Density Derivation (ρ_τ = c^5 / (2π ℏ G^2), Manuscript Eq. 16)
theorem metric_density_derivation (P_c_val : ℝ)
    (h_P_c : P_c_val = c^7 / (4 * Real.pi * hbar * G^2))
    (h_P_dyn : (1 / 2) * rho_tau * c^2 = P_c_val) :
    rho_tau = (1 / (2 * Real.pi)) * (c^5 / (hbar * G^2)) := by
  have h1 : rho_tau = 2 * P_c_val / c^2 := reduce_density_algebra P_c_val h_P_dyn
  have h2 : rho_tau = 2 * (c^7 / (4 * Real.pi * hbar * G^2)) / c^2 := by rw [h_P_c] at h1; exact h1
  have h_cancel : 2 * (c^7 / (4 * Real.pi * hbar * G^2)) / c^2 = (1 / (2 * Real.pi)) * (c^5 / (hbar * G^2)) :=
    reduce_c7_c2
  rw [h_cancel] at h2
  exact h2

lemma dilate_lambda_algebra (P_m R_val : ℝ) (hR : R_val ≠ 0) :
  P_m = (c^4 / G) / (4 * Real.pi * R_val^2) →
  (8 * Real.pi * G / c^4) * P_m = 2 / R_val^2 := by
  intro h
  have hc : c ≠ 0 := ne_of_gt c_pos
  have hG : G ≠ 0 := ne_of_gt G_pos
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [h]
  field_simp
  ring

-- Theorem 18: Epoch-Dependent Cosmological Constant Derivation (Λ = 2 / R_h^2, Manuscript Eq. 19)
theorem cosmological_constant_derivation (R_h P_macro Lambda : ℝ) (hR : R_h ≠ 0)
    (h_P_macro : P_macro = (c^4 / G) / (4 * Real.pi * R_h^2))
    (h_Lambda : Lambda = (8 * Real.pi * G * P_macro) / c^4) :
    Lambda = 2 / R_h^2 := by
  have h1 : Lambda = (8 * Real.pi * G / c^4) * P_macro := by
    calc
      Lambda = (8 * Real.pi * G * P_macro) / c^4 := h_Lambda
      _ = (8 * Real.pi * G / c^4) * P_macro := by ring
  have h2 : (8 * Real.pi * G / c^4) * P_macro = 2 / R_h^2 :=
    dilate_lambda_algebra P_macro R_h hR h_P_macro
  rw [h2] at h1
  exact h1

-- Theorem 19: Weak-Field Poisson Stress Limit (T_ii = -ρ_τ Φ, Manuscript Eq. 23)
theorem spatial_stress_potential (Phi : ℝ) :
    (((1 / 2) * rho_tau * c^2) * (- (2 * Phi) / c^2)) = - (rho_tau * Phi) := by
  have hc : c ≠ 0 := ne_of_gt c_pos
  field_simp

-- ----------------------------------------------------------------------
-- 4.3 The Macroscopic Reduction (The Einstein Field Equation) (Manuscript Eqs. 24–31)
-- ----------------------------------------------------------------------

/-- Volumetric Average operator acting as symmetric spatial coarse-graining (`LinearMap` over `ℝ`). -/
noncomputable def VolAvg : T2 →ₗ[ℝ] T2 where
  toFun U := symPart U
  map_add' A B := by
    ext i j
    change (A i j + B i j + (A j i + B j i)) / (2 : ℝ) = (A i j + A j i) / (2 : ℝ) + (B i j + B j i) / (2 : ℝ)
    ring
  map_smul' r_scalar A := by
    ext i j
    change (r_scalar * A i j + r_scalar * A j i) / (2 : ℝ) = r_scalar * ((A i j + A j i) / (2 : ℝ))
    ring

lemma VolAvg_U_anti (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) :
    VolAvg (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) = 0 := by
  ext i j
  dsimp [VolAvg, U_anti, symPart, antiPart]
  ring

variable (Inc : T2 →ₗ[ℝ] T2)

-- Theorem 20: Macroscopic Torsion Nullification under Coarse-Graining (Manuscript Eqs. 28–30)
theorem macroscopic_torsion_nullification (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ)
    (h_commute : ∀ (A : T2), Inc (VolAvg A) = VolAvg (Inc A)) :
    VolAvg (Inc (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)) =
    VolAvg (Inc (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)) := by
  have h_decomp := tensor_decomposition_proven alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val
  rw [h_decomp]
  have h2 : Inc (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val +
                 U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) =
            Inc (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) +
            Inc (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) := map_add Inc _ _
  rw [h2]
  have h3 : VolAvg (Inc (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) +
                    Inc (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)) =
            VolAvg (Inc (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)) +
            VolAvg (Inc (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)) := map_add VolAvg _ _
  rw [h3]
  have h4 : VolAvg (Inc (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)) =
            Inc (VolAvg (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)) :=
    (h_commute (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)).symm
  rw [h4]
  have h5 : VolAvg (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) = 0 :=
    VolAvg_U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val
  rw [h5]
  have h6 : Inc (0 : T2) = 0 := map_zero Inc
  rw [h6, add_zero]

-- ======================================================================
-- SECTION 5: THE EQUATION OF MOTION (DIVERGENCE EQUILIBRIUM)
-- ======================================================================

-- ----------------------------------------------------------------------
-- 5.0 Spacetime Manifold, Clebsch Potential Fields & Weak-Field Stress Expansion (Manuscript Eqs. 32–36)
-- ----------------------------------------------------------------------
abbrev SpaceTime := Fin 4 → ℝ
abbrev ScalarField := SpaceTime → ℝ
abbrev VectorField := SpaceTime → SpaceTime
abbrev MetricField := SpaceTime → T2

/-- Partial derivative operator `∂_μ f(x)` via the Fréchet derivative along basis direction `μ`. -/
noncomputable def partial_deriv (f : ScalarField) (μ : Fin 4) (x : SpaceTime) : ℝ :=
  (fderiv ℝ f x) (fun i => if i = μ then 1 else 0)

/-- Concrete exterior derivative of a continuous 0-form (`ScalarField`): `(df)_μ = ∂_μ f`. -/
noncomputable def d_scalar_field (f : ScalarField) (x : SpaceTime) : V4 :=
  fun μ => partial_deriv f μ x

/-- Spacetime divergence `∂_μ U^μν(x)`. -/
noncomputable def metric_divergence (U : MetricField) (x : SpaceTime) : V4 :=
  fun ν => ∑ μ : Fin 4, partial_deriv (fun y => U y μ ν) μ x

/-- A metric field is divergence-free at `x` when `∂_μ U^μν(x) = 0`. -/
def is_divergence_free (U : MetricField) (x : SpaceTime) : Prop :=
  metric_divergence U x = 0

-- Theorem 26.5 (Resolves Issue #9 Satisfiability Witness):
-- Proves without axioms that any homogeneous vacuum metric field `fun _ => U_const`
-- has vanishing partial derivatives and satisfies `is_divergence_free` at every point `x`.
theorem homogeneous_vacuum_is_divergence_free (U_const : T2) (x : SpaceTime) :
    is_divergence_free (fun _ : SpaceTime => U_const) x := by
  unfold is_divergence_free
  ext ν
  dsimp [metric_divergence, partial_deriv]
  simp

/-- Bundles the dynamic kinematic and Clebsch scalar potential fields with the on-shell
    covariant conservation law `∂_μ U^μν(x) = 0` (Zero-Axiom Witness Architecture). -/
structure DynamicClebschFields where
  alpha_s_f      : ScalarField
  alpha_f        : ScalarField
  h_phase_f      : ScalarField
  v_x_f          : ScalarField
  v_y_f          : ScalarField
  v_z_f          : ScalarField
  lambda_Omega_f : ScalarField
  beta_Omega_f   : ScalarField
  conservation   : ∀ (x : SpaceTime),
    metric_divergence
      (fun y => U_hat (alpha_s_f y) (alpha_f y) (v_x_f y) (v_y_f y) (v_z_f y)
                      (d_scalar_field lambda_Omega_f y) (d_scalar_field beta_Omega_f y) t_p) x = 0

/-- Constructive homogeneous vacuum witness proving `DynamicClebschFields` is non-empty without
  axioms. -/
noncomputable def vacuum_clebsch_witness : DynamicClebschFields where
  alpha_s_f      := fun _ => 1
  alpha_f        := fun _ => 0
  h_phase_f      := fun _ => 0
  v_x_f          := fun _ => 0
  v_y_f          := fun _ => 0
  v_z_f          := fun _ => 0
  lambda_Omega_f := fun _ => 0
  beta_Omega_f   := fun _ => 0
  conservation   := by
    intro x
    have hd0 : ∀ y : SpaceTime,
        d_scalar_field (fun _ : SpaceTime => (0 : ℝ)) y = (fun _ : Fin 4 => (0 : ℝ)) := by
      intro y
      ext μ
      dsimp [d_scalar_field, partial_deriv]
      simp
    have h_const :
        (fun y : SpaceTime =>
          U_hat (1 : ℝ) 0 0 0 0
            (d_scalar_field (fun _ : SpaceTime => (0 : ℝ)) y)
            (d_scalar_field (fun _ : SpaceTime => (0 : ℝ)) y) t_p) =
        (fun _ : SpaceTime =>
          U_hat (1 : ℝ) 0 0 0 0 (fun _ => 0) (fun _ => 0) t_p) := by
      ext y i j
      rw [hd0 y]
    rw [h_const]
    exact homogeneous_vacuum_is_divergence_free _ x

/-- Active opaque on-shell field configuration (zero custom kernel axioms). -/
noncomputable opaque dyn_state : DynamicClebschFields := vacuum_clebsch_witness

-- Dynamic Kinematic & Clebsch Scalar Potential Fields on SpaceTime (Projected from `dyn_state`)
noncomputable def alpha_s_f      : ScalarField := dyn_state.alpha_s_f
noncomputable def alpha_f        : ScalarField := dyn_state.alpha_f
noncomputable def h_phase_f      : ScalarField := dyn_state.h_phase_f
noncomputable def v_x_f          : ScalarField := dyn_state.v_x_f
noncomputable def v_y_f          : ScalarField := dyn_state.v_y_f
noncomputable def v_z_f          : ScalarField := dyn_state.v_z_f
noncomputable def lambda_Omega_f : ScalarField := dyn_state.lambda_Omega_f
noncomputable def beta_Omega_f   : ScalarField := dyn_state.beta_Omega_f

/-- Dynamic Clebsch vorticity 2-form field on `SpaceTime` (Manuscript Eq. 2):
    `Ω_μν(x) = (dλ_Ω(x) ∧ dβ_Ω(x))_μν`. -/
noncomputable def Omega_clebsch_field (lambda_f beta_f : ScalarField) : MetricField :=
  fun x => omega_clebsch_2form (d_scalar_field lambda_f x) (d_scalar_field beta_f x)

/-- Dynamic vorticity components generated directly from `lambda_Omega_f` and `beta_Omega_f`: -/
noncomputable def Omega_x_f : ScalarField :=
  fun x => Omega_x_clebsch (d_scalar_field lambda_Omega_f x) (d_scalar_field beta_Omega_f x)

noncomputable def Omega_y_f : ScalarField :=
  fun x => Omega_y_clebsch (d_scalar_field lambda_Omega_f x) (d_scalar_field beta_Omega_f x)

noncomputable def Omega_z_f : ScalarField :=
  fun x => Omega_z_clebsch (d_scalar_field lambda_Omega_f x) (d_scalar_field beta_Omega_f x)

/-- Dynamic Asymmetric Metric-Tensor field `U_hat_dynamic`, with vorticity constructed
    from the Clebsch scalar potentials `lambda_Omega_f` and `beta_Omega_f`. -/
noncomputable def U_hat_dynamic : MetricField :=
  fun x => U_hat (alpha_s_f x) (alpha_f x) (v_x_f x) (v_y_f x) (v_z_f x)
                 (d_scalar_field lambda_Omega_f x) (d_scalar_field beta_Omega_f x) t_p

/-- Moving-frame weak-field 4-velocity covector `u_μ = (-1, v_x/c, v_y/c, v_z/c)`. -/
noncomputable def u_moving_weak (v_x v_y v_z : ℝ) : V4 :=
  fun i => if i = 0 then -1 else if i = 1 then v_x / c else if i = 2 then v_y / c else if i = 3 then v_z / c else 0

-- Theorem 21: Moving-Frame Symmetric Strain Prefactor ((γ^4 - 1) β_i β_j, Manuscript Eqs. 32–34)
theorem moving_frame_gamma4_factor (gamma_val beta_i beta_j : ℝ) (h_gamma : gamma_val ≠ 0) :
    (gamma_val^2 - 1 / gamma_val^2) * ((gamma_val * beta_i) * (gamma_val * beta_j)) =
    (gamma_val^4 - 1) * (beta_i * beta_j) := by
  field_simp

-- Theorem 22: Weak-Field Lorentz Factor Taylor Expansions with Remainder (Manuscript Eqs. 33–34)
theorem weak_field_gamma_expansions_with_remainder (beta_sq : ℝ) (h_sub : beta_sq ≠ 1) :
    1 / (1 - beta_sq) = 1 + beta_sq + beta_sq^2 + beta_sq^3 / (1 - beta_sq) ∧
    1 / (1 - beta_sq)^2 - 1 = 2 * beta_sq + 3 * beta_sq^2 + (4 * beta_sq^3 - 3 * beta_sq^4) / (1 - beta_sq)^2 := by
  have h_denom : 1 - beta_sq ≠ 0 := sub_ne_zero.mpr (Ne.symm h_sub)
  refine ⟨?_, ?_⟩
  · field_simp
    ring
  · field_simp
    ring

-- Theorem 23: O(β^4) Momentum Density Flux and Spatial Stress Perturbation (Manuscript Eqs. 33–36)
theorem weak_field_order_beta4_stress_consistency
    (beta_sq P_dyn_local rho_dyn_local v_i v_j delta_ij : ℝ)
    (h_beta : beta_sq = P_dyn_local / P_c)
    (h_rho_dyn : rho_dyn_local = P_dyn_local / c^2) :
    P_c * (2 * beta_sq * (v_i / c)) = 2 * rho_dyn_local * c * v_i ∧
    P_c * ((beta_sq + beta_sq^2) * delta_ij + 2 * beta_sq * ((v_i * v_j) / c^2)) =
    (P_dyn_local + P_dyn_local^2 / P_c) * delta_ij + 2 * rho_dyn_local * (v_i * v_j) := by
  have hPc : P_c ≠ 0 := Pc_non_zero
  have hc : c ≠ 0 := c_ne_zero
  rw [h_beta, h_rho_dyn]
  refine ⟨?_, ?_⟩
  · field_simp
  · field_simp

-- Theorem 24: Moving-Frame Reynolds Convective Momentum Flux (Manuscript Eq. 35)
theorem moving_frame_reynolds_stress (v_x v_y v_z : ℝ) :
    P_c * (u_moving_weak v_x v_y v_z 1 * u_moving_weak v_x v_y v_z 2) =
    (1 / 2) * rho_tau * (v_x * v_y) := by
  dsimp [u_moving_weak, P_c]
  have hc : c ≠ 0 := c_ne_zero
  norm_num
  field_simp

-- ----------------------------------------------------------------------
-- 5.1 The Equation of Motion (Navier-Stokes) (Manuscript Eqs. 37–46)
-- ----------------------------------------------------------------------

-- On-Shell Covariant Conservation Theorem (Proved from `dyn_state.conservation` without axioms):
theorem covariant_conservation (x : SpaceTime) :
    metric_divergence U_hat_dynamic x = 0 :=
  dyn_state.conservation x

-- Theorem 25: Temporal Divergence Equilibrium (Bernoulli Energy Conservation)
theorem bernoulli_energy_conservation (x : SpaceTime) :
    (metric_divergence U_hat_dynamic x) 0 = 0 := by
  have h := covariant_conservation x
  rw [h]
  rfl

-- Theorem 26: Spatial Divergence Equilibrium (Navier-Stokes Momentum Conservation)
theorem navier_stokes_momentum_conservation (x : SpaceTime) (i : Fin 4)
    (_h_spatial : i ≠ 0) :
    (metric_divergence U_hat_dynamic x) i = 0 := by
  have h := covariant_conservation x
  rw [h]
  rfl

theorem divergence_expansion (x : SpaceTime) (ν : Fin 4) :
    (metric_divergence U_hat_dynamic x) ν =
    ∑ μ : Fin 4, partial_deriv (fun y => U_hat_dynamic y μ ν) μ x := by
  rfl

/-- Dynamic pressure field `P_dyn(x) = (1 - α_s(x)^2) P_c`. -/
noncomputable def P_dyn_f : ScalarField :=
  fun x => (1 - (alpha_s_f x)^2) * P_c

-- Lemma: Contravariant index raising `U^μν = η^μα η^νβ U_αβ` (`raiseBoth eta_metric`) on any 4×4
-- matrix `M`
lemma raiseBoth_eta_entries (M : T2) :
    raiseBoth eta_metric M 0 0 = M 0 0 ∧
    raiseBoth eta_metric M 1 1 = M 1 1 ∧
    raiseBoth eta_metric M 0 1 = - M 0 1 ∧
    raiseBoth eta_metric M 2 1 = M 2 1 ∧
    raiseBoth eta_metric M 3 1 = M 3 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · unfold raiseBoth
    rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four,
      Fin.sum_univ_four]
    dsimp [eta_metric, Matrix.of_apply]
    ring

-- Theorem 26a: Comoving `U_covariant` Assembly & Contravariant Index-Raising Bridge (Resolves Issue
-- #13)
-- Proves:
-- 1. Comoving Reduction: Evaluating `U_covariant` on `u_comoving = (-1, 0, 0, 0)` and
--    `v_perp_covec v_x v_y v_z` reproduces the diagonal (`U_00 = -α_s^2`, `U_11 = 1/α_s^2`)
--    and space-time slip (`U_01 = -α v_x / c`) components of `U_hat`,
-- 2. Contravariant Divergence Bridge: Raising both indices of `U_hat_dynamic` with `eta_metric`
--    preserves the spatial components `(1,1)`, `(2,1)`, `(3,1)` and their partial derivatives,
--    while flipping the sign of the mixed temporal-spatial component `(0,1)`.
theorem raised_contravariant_divergence_bridge
    (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4) (t_p_val : ℝ) (x : SpaceTime)
    (h_dl0 : d_lambda 0 = 0) (h_db0 : d_beta 0 = 0) :
    U_covariant alpha_s alpha c t_p_val u_comoving (v_perp_covec v_x v_y v_z) d_lambda d_beta 0 0 =
      (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 0 0 ∧
    U_covariant alpha_s alpha c t_p_val u_comoving (v_perp_covec v_x v_y v_z) d_lambda d_beta 1 1 =
      (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 1 ∧
    U_covariant alpha_s alpha c t_p_val u_comoving (v_perp_covec v_x v_y v_z) d_lambda d_beta 0 1 =
      (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 0 1 ∧
    (fun y => raiseBoth eta_metric (U_hat_dynamic y) 0 1) = (fun y => - U_hat_dynamic y 0 1) ∧
    (fun y => raiseBoth eta_metric (U_hat_dynamic y) 1 1) = (fun y => U_hat_dynamic y 1 1) ∧
    (fun y => raiseBoth eta_metric (U_hat_dynamic y) 2 1) = (fun y => U_hat_dynamic y 2 1) ∧
    (fun y => raiseBoth eta_metric (U_hat_dynamic y) 3 1) = (fun y => U_hat_dynamic y 3 1) ∧
    partial_deriv (fun y => raiseBoth eta_metric (U_hat_dynamic y) 1 1) 1 x =
      partial_deriv (fun y => U_hat_dynamic y 1 1) 1 x ∧
    partial_deriv (fun y => raiseBoth eta_metric (U_hat_dynamic y) 2 1) 2 x =
      partial_deriv (fun y => U_hat_dynamic y 2 1) 2 x ∧
    partial_deriv (fun y => raiseBoth eta_metric (U_hat_dynamic y) 3 1) 3 x =
      partial_deriv (fun y => U_hat_dynamic y 3 1) 3 x := by
  have h_cov00 : U_covariant alpha_s alpha c t_p_val u_comoving (v_perp_covec v_x v_y v_z) d_lambda
    d_beta 0 0 =
      (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 0 0 := by
    dsimp [U_covariant, U_hat, h_projector, eta_metric, u_comoving, v_perp_covec,
           wedge_covec, omega_clebsch_2form, Matrix.of_apply]
    ring
  have h_cov11 : U_covariant alpha_s alpha c t_p_val u_comoving (v_perp_covec v_x v_y v_z) d_lambda
    d_beta 1 1 =
      (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 1 := by
    dsimp [U_covariant, U_hat, h_projector, eta_metric, u_comoving, v_perp_covec,
           wedge_covec, omega_clebsch_2form, Matrix.of_apply]
    ring
  have h_cov01 : U_covariant alpha_s alpha c t_p_val u_comoving (v_perp_covec v_x v_y v_z) d_lambda
    d_beta 0 1 =
      (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 0 1 := by
    dsimp [U_covariant, U_hat, h_projector, eta_metric, u_comoving, v_perp_covec,
           wedge_covec, omega_clebsch_2form, Matrix.of_apply]
    rw [h_dl0, h_db0]
    ring
  have h01 : (fun y => raiseBoth eta_metric (U_hat_dynamic y) 0 1) = (fun y => - U_hat_dynamic y 0
    1) := by
    ext y; exact (raiseBoth_eta_entries (U_hat_dynamic y)).2.2.1
  have h11 : (fun y => raiseBoth eta_metric (U_hat_dynamic y) 1 1) = (fun y => U_hat_dynamic y 1 1)
    := by
    ext y; exact (raiseBoth_eta_entries (U_hat_dynamic y)).2.1
  have h21 : (fun y => raiseBoth eta_metric (U_hat_dynamic y) 2 1) = (fun y => U_hat_dynamic y 2 1)
    := by
    ext y; exact (raiseBoth_eta_entries (U_hat_dynamic y)).2.2.2.1
  have h31 : (fun y => raiseBoth eta_metric (U_hat_dynamic y) 3 1) = (fun y => U_hat_dynamic y 3 1)
    := by
    ext y; exact (raiseBoth_eta_entries (U_hat_dynamic y)).2.2.2.2
  refine ⟨h_cov00, h_cov11, h_cov01, h01, h11, h21, h31, ?_, ?_, ?_⟩
  · rw [h11]
  · rw [h21]
  · rw [h31]

-- Theorem 27: Dynamic Spatial Compliance Link and Pressure Gradient Extraction
theorem dynamic_compliance_link (x : SpaceTime) :
  1 / (alpha_s_f x)^2 = 1 / (1 - (P_dyn_f x) / P_c) := by
  unfold P_dyn_f
  have h_cancel : (1 - (alpha_s_f x)^2) * P_c / P_c = 1 - (alpha_s_f x)^2 :=
    mul_div_cancel_right₀ (1 - (alpha_s_f x)^2) Pc_non_zero
  rw [h_cancel]
  have h_sub : 1 - (1 - (alpha_s_f x)^2) = (alpha_s_f x)^2 := by ring
  rw [h_sub]

theorem pressure_gradient_extraction (μ : Fin 4) (x : SpaceTime) :
    partial_deriv (fun y => 1 / (alpha_s_f y)^2) μ x =
    partial_deriv (fun y => 1 / (1 - (P_dyn_f y) / P_c)) μ x := by
  have h_field : (fun y => 1 / (alpha_s_f y)^2) = (fun y => 1 / (1 - (P_dyn_f y) / P_c)) := by
    ext y
    exact dynamic_compliance_link y
  rw [h_field]

/-- Transverse shear stress field `T_⊥(x) = -α(x) (v_x(x)/c) P_c`. -/
noncomputable def T_perp_f : ScalarField :=
  fun x => - (alpha_f x) * (v_x_f x / c) * P_c

-- Theorem 28: Constitutive Off-Diagonal Shear Stress Projection and Divergence Link
theorem transverse_shear_link (x : SpaceTime) :
  - (alpha_f x) * (v_x_f x / c) = (T_perp_f x) / P_c := by
  unfold T_perp_f
  have h_cancel : - (alpha_f x) * (v_x_f x / c) * P_c / P_c = - (alpha_f x) * (v_x_f x / c) :=
    mul_div_cancel_right₀ (- (alpha_f x) * (v_x_f x / c)) Pc_non_zero
  rw [h_cancel]

theorem constitutive_stress_off_diagonal_link (x : SpaceTime) :
    constitutive_stress (U_hat_dynamic x) 0 1 = T_perp_f x := by
  dsimp [constitutive_stress, U_hat_dynamic, U_hat, eta_metric, T_perp_f, Matrix.of_apply]
  norm_num
  ring

theorem shear_divergence_extraction (μ : Fin 4) (x : SpaceTime) :
    partial_deriv (fun y => - (alpha_f y) * (v_x_f y / c)) μ x =
    partial_deriv (fun y => (T_perp_f y) / P_c) μ x := by
  have h_field : (fun y => - (alpha_f y) * (v_x_f y / c)) = (fun y => (T_perp_f y) / P_c) := by
    ext y
    exact transverse_shear_link y
  rw [h_field]

-- Dimensional Audit: Spatial derivative of dimensionless strain (1/L) equals normalized pressure/stress divergence (grad_P / P_c):
theorem unit_section5_navier_stokes_divergence :
    u_dimless / u_l_p = u_grad_P / u_P_c ∧
    (u_dimless / u_rho_tau) * u_grad_P = u_accel := by
  constructor <;> rfl

noncomputable def kinematic_accel_f : ScalarField :=
  fun x => - (partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x) * P_c

theorem acceleration_link (x : SpaceTime) :
  partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x = - (kinematic_accel_f x) / P_c := by
  unfold kinematic_accel_f
  have h1 : - (- (partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x) * P_c) =
            (partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x) * P_c := by ring
  rw [h1]
  have h_cancel : (partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x) * P_c / P_c =
                  partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x :=
    mul_div_cancel_right₀ (partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x) Pc_non_zero
  rw [h_cancel]

theorem exact_pressure_link (x : SpaceTime) :
  partial_deriv (fun y => U_hat_dynamic y 1 1) 1 x =
  partial_deriv (fun y => 1 / (1 - (P_dyn_f y) / P_c)) 1 x := by
  have h_diag : (fun y => U_hat_dynamic y 1 1) = (fun y => 1 / (alpha_s_f y)^2) := by rfl
  rw [h_diag]
  exact pressure_gradient_extraction 1 x

noncomputable def div_T_perp_f : ScalarField :=
  fun x => (partial_deriv (fun y => U_hat_dynamic y 2 1) 2 x +
            partial_deriv (fun y => U_hat_dynamic y 3 1) 3 x) * P_c

theorem transverse_divergence_link (x : SpaceTime) :
  partial_deriv (fun y => U_hat_dynamic y 2 1) 2 x +
  partial_deriv (fun y => U_hat_dynamic y 3 1) 3 x = (div_T_perp_f x) / P_c := by
  unfold div_T_perp_f
  have h_cancel : (partial_deriv (fun y => U_hat_dynamic y 2 1) 2 x +
                   partial_deriv (fun y => U_hat_dynamic y 3 1) 3 x) * P_c / P_c =
                  partial_deriv (fun y => U_hat_dynamic y 2 1) 2 x +
                  partial_deriv (fun y => U_hat_dynamic y 3 1) 3 x :=
    mul_div_cancel_right₀ (partial_deriv (fun y => U_hat_dynamic y 2 1) 2 x +
                          partial_deriv (fun y => U_hat_dynamic y 3 1) 3 x) Pc_non_zero
  rw [h_cancel]

-- Theorem 29: Exact Nonlinear Geometric Navier-Stokes Equation
theorem geometric_navier_stokes (x : SpaceTime)
    (h_geometric_zero : partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x +
                        partial_deriv (fun y => U_hat_dynamic y 1 1) 1 x +
                        partial_deriv (fun y => U_hat_dynamic y 2 1) 2 x +
                        partial_deriv (fun y => U_hat_dynamic y 3 1) 3 x = 0) :
    (kinematic_accel_f x) / P_c =
    partial_deriv (fun y => 1 / (1 - (P_dyn_f y) / P_c)) 1 x + (div_T_perp_f x) / P_c := by
  have h1 := acceleration_link x
  have h2 := exact_pressure_link x
  have h3 := transverse_divergence_link x
  have h_sum : (- (kinematic_accel_f x) / P_c) +
               partial_deriv (fun y => 1 / (1 - (P_dyn_f y) / P_c)) 1 x +
               ((div_T_perp_f x) / P_c) = 0 := by
    calc (- (kinematic_accel_f x) / P_c) +
         partial_deriv (fun y => 1 / (1 - (P_dyn_f y) / P_c)) 1 x +
         ((div_T_perp_f x) / P_c)
      _ = partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x +
          partial_deriv (fun y => U_hat_dynamic y 1 1) 1 x +
          (partial_deriv (fun y => U_hat_dynamic y 2 1) 2 x +
           partial_deriv (fun y => U_hat_dynamic y 3 1) 3 x) := by rw [h1, h2, h3]
      _ = partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x +
          partial_deriv (fun y => U_hat_dynamic y 1 1) 1 x +
          partial_deriv (fun y => U_hat_dynamic y 2 1) 2 x +
          partial_deriv (fun y => U_hat_dynamic y 3 1) 3 x := by ring
      _ = 0 := h_geometric_zero
  calc (kinematic_accel_f x) / P_c
    _ = (kinematic_accel_f x) / P_c + 0 := by ring
    _ = (kinematic_accel_f x) / P_c +
        ((- (kinematic_accel_f x) / P_c) +
         partial_deriv (fun y => 1 / (1 - (P_dyn_f y) / P_c)) 1 x +
         ((div_T_perp_f x) / P_c)) := by rw [h_sum]
    _ = partial_deriv (fun y => 1 / (1 - (P_dyn_f y) / P_c)) 1 x + (div_T_perp_f x) / P_c := by ring

/-- 3D Convective Derivative `(v · ∇) f` on a continuous `ScalarField`. -/
noncomputable def convective_deriv (f : ScalarField) (x : SpaceTime) : ℝ :=
  v_x_f x * partial_deriv f 1 x +
  v_y_f x * partial_deriv f 2 x +
  v_z_f x * partial_deriv f 3 x

/-- Eulerian Material Derivative `D_t f = ∂_t f + (v · ∇) f` (Manuscript Eq. 40). -/
noncomputable def material_deriv (f : ScalarField) (x : SpaceTime) : ℝ :=
  partial_deriv f 0 x + convective_deriv f x

-- Theorem 30: Eulerian Material Acceleration from Mass Continuity (Manuscript Eqs. 39–40)
theorem material_acceleration_from_continuity
    (rho v_i dt_rho dt_vi dx_rhovx dy_rhovy dz_rhovz v_x v_y v_z dx_vi dy_vi dz_vi
     flux_t flux_x flux_y flux_z : ℝ)
    (h_leibniz_t : flux_t = dt_rho * v_i + rho * dt_vi)
    (h_leibniz_x : flux_x = dx_rhovx * v_i + rho * (v_x * dx_vi))
    (h_leibniz_y : flux_y = dy_rhovy * v_i + rho * (v_y * dy_vi))
    (h_leibniz_z : flux_z = dz_rhovz * v_i + rho * (v_z * dz_vi))
    (h_continuity : dt_rho + dx_rhovx + dy_rhovy + dz_rhovz = 0) :
    flux_t + flux_x + flux_y + flux_z =
    rho * (dt_vi + (v_x * dx_vi + v_y * dy_vi + v_z * dz_vi)) := by
  rw [h_leibniz_t, h_leibniz_x, h_leibniz_y, h_leibniz_z]
  calc dt_rho * v_i + rho * dt_vi + (dx_rhovx * v_i + rho * (v_x * dx_vi)) +
       (dy_rhovy * v_i + rho * (v_y * dy_vi)) + (dz_rhovz * v_i + rho * (v_z * dz_vi))
    _ = (dt_rho + dx_rhovx + dy_rhovy + dz_rhovz) * v_i +
        rho * (dt_vi + (v_x * dx_vi + v_y * dy_vi + v_z * dz_vi)) := by ring
    _ = 0 * v_i + rho * (dt_vi + (v_x * dx_vi + v_y * dy_vi + v_z * dz_vi)) := by rw [h_continuity]
    _ = rho * (dt_vi + (v_x * dx_vi + v_y * dy_vi + v_z * dz_vi)) := by ring

theorem material_derivative_continuity_field_link
    (rho_f v_i_f : ScalarField) (x : SpaceTime)
    (flux_t flux_x flux_y flux_z dx_rhovx dy_rhovy dz_rhovz : ℝ)
    (h_leibniz_t : flux_t = partial_deriv rho_f 0 x * v_i_f x + rho_f x * partial_deriv v_i_f 0 x)
    (h_leibniz_x : flux_x = dx_rhovx * v_i_f x + rho_f x * (v_x_f x * partial_deriv v_i_f 1 x))
    (h_leibniz_y : flux_y = dy_rhovy * v_i_f x + rho_f x * (v_y_f x * partial_deriv v_i_f 2 x))
    (h_leibniz_z : flux_z = dz_rhovz * v_i_f x + rho_f x * (v_z_f x * partial_deriv v_i_f 3 x))
    (h_continuity : partial_deriv rho_f 0 x + dx_rhovx + dy_rhovy + dz_rhovz = 0) :
    flux_t + flux_x + flux_y + flux_z = rho_f x * material_deriv v_i_f x := by
  dsimp [material_deriv, convective_deriv]
  exact material_acceleration_from_continuity
    (rho_f x) (v_i_f x) (partial_deriv rho_f 0 x) (partial_deriv v_i_f 0 x)
    dx_rhovx dy_rhovy dz_rhovz (v_x_f x) (v_y_f x) (v_z_f x)
    (partial_deriv v_i_f 1 x) (partial_deriv v_i_f 2 x) (partial_deriv v_i_f 3 x)
    flux_t flux_x flux_y flux_z h_leibniz_t h_leibniz_x h_leibniz_y h_leibniz_z h_continuity

-- Theorem 31: Weak-Field Cauchy Momentum PDE (Manuscript Eq. 40)
theorem eulerian_momentum_pde_eq46
    (rho v_i dt_rho dt_vi dx_rhovx dy_rhovy dz_rhovz v_x v_y v_z dx_vi dy_vi dz_vi
     flux_t flux_x flux_y flux_z grad_P_i div_T_perp_i : ℝ)
    (h_leibniz_t : flux_t = dt_rho * v_i + rho * dt_vi)
    (h_leibniz_x : flux_x = dx_rhovx * v_i + rho * (v_x * dx_vi))
    (h_leibniz_y : flux_y = dy_rhovy * v_i + rho * (v_y * dy_vi))
    (h_leibniz_z : flux_z = dz_rhovz * v_i + rho * (v_z * dz_vi))
    (h_continuity : dt_rho + dx_rhovx + dy_rhovy + dz_rhovz = 0)
    (h_conservation : (flux_t + flux_x + flux_y + flux_z) + grad_P_i - div_T_perp_i = 0) :
    rho * (dt_vi + (v_x * dx_vi + v_y * dy_vi + v_z * dz_vi)) = - grad_P_i + div_T_perp_i := by
  have h_mat := material_acceleration_from_continuity
    rho v_i dt_rho dt_vi dx_rhovx dy_rhovy dz_rhovz v_x v_y v_z dx_vi dy_vi dz_vi
    flux_t flux_x flux_y flux_z h_leibniz_t h_leibniz_x h_leibniz_y h_leibniz_z h_continuity
  linarith

-- Theorem 32: Admittance-Modified Kinematic Navier-Stokes Equation with Clebsch Wedge Vorticity (Manuscript Eqs. 41–46)
theorem kinematic_navier_stokes_clebsch_eq46
    (lambda_f beta_f : ScalarField) (x : SpaceTime) (i : Fin 4)
    (rho_dyn v_i dt_rho dt_vi dx_rhovx dy_rhovy dz_rhovz v_x v_y v_z dx_vi dy_vi dz_vi
     flux_t flux_x flux_y flux_z grad_P_total_i div_T_perp_i
     grad_P_amb_i grad_P_dyn_i div_T_slip_i alpha_val mu_visc : ℝ)
    (h_leibniz_t : flux_t = dt_rho * v_i + rho_dyn * dt_vi)
    (h_leibniz_x : flux_x = dx_rhovx * v_i + rho_dyn * (v_x * dx_vi))
    (h_leibniz_y : flux_y = dy_rhovy * v_i + rho_dyn * (v_y * dy_vi))
    (h_leibniz_z : flux_z = dz_rhovz * v_i + rho_dyn * (v_z * dz_vi))
    (h_continuity : dt_rho + dx_rhovx + dy_rhovy + dz_rhovz = 0)
    (h_conservation : (flux_t + flux_x + flux_y + flux_z) + grad_P_total_i - div_T_perp_i = 0)
    (h_P_partition : grad_P_total_i = (1 / 2) * grad_P_amb_i + (1 / 2) * grad_P_dyn_i)
    (h_shear_partition : div_T_perp_i =
      (1 / 2) * alpha_val * (div_T_slip_i - mu_visc * metric_divergence (Omega_clebsch_field lambda_f beta_f) x i)) :
    (rho_dyn / rho_tau) * (dt_vi + (v_x * dx_vi + v_y * dy_vi + v_z * dz_vi)) =
    - (grad_P_amb_i / (2 * rho_tau)) - (grad_P_dyn_i / (2 * rho_tau)) +
    alpha_val * ((div_T_slip_i / (2 * rho_tau)) -
      (mu_visc / (2 * rho_tau)) * metric_divergence (Omega_clebsch_field lambda_f beta_f) x i) := by
  have h_pde := eulerian_momentum_pde_eq46
    rho_dyn v_i dt_rho dt_vi dx_rhovx dy_rhovy dz_rhovz v_x v_y v_z dx_vi dy_vi dz_vi
    flux_t flux_x flux_y flux_z grad_P_total_i div_T_perp_i
    h_leibniz_t h_leibniz_x h_leibniz_y h_leibniz_z h_continuity h_conservation
  rw [h_P_partition, h_shear_partition] at h_pde
  have hrho : rho_tau ≠ 0 := rho_tau_ne_zero
  have h_scale := congrArg (· / rho_tau) h_pde
  calc (rho_dyn / rho_tau) * (dt_vi + (v_x * dx_vi + v_y * dy_vi + v_z * dz_vi))
    _ = (rho_dyn * (dt_vi + (v_x * dx_vi + v_y * dy_vi + v_z * dz_vi))) / rho_tau := by ring
    _ = (- ((1 / 2) * grad_P_amb_i + (1 / 2) * grad_P_dyn_i) +
         (1 / 2) * alpha_val * (div_T_slip_i - mu_visc * metric_divergence (Omega_clebsch_field lambda_f beta_f) x i)) / rho_tau := h_scale
    _ = - (grad_P_amb_i / (2 * rho_tau)) - (grad_P_dyn_i / (2 * rho_tau)) +
        alpha_val * ((div_T_slip_i / (2 * rho_tau)) -
          (mu_visc / (2 * rho_tau)) * metric_divergence (Omega_clebsch_field lambda_f beta_f) x i) := by ring

-- ----------------------------------------------------------------------
-- 5.2 The Incompatible Defect (Compliance-Modified Momentum) (Manuscript Eqs. 47–52)
-- ----------------------------------------------------------------------
variable (a_lambda g_lambda F_surf_lambda : V_3D)
variable (P : ℝ)
variable (M : ℝ)

-- Dimensional Audit: Relativistic enthalpy density correction (P / c^2 = rho_tau),
-- effective strain volume (l_p^4 / r_c = Volume), and inverse-cube volume invariant (V * V^3 = L^12):
theorem unit_section5_8_defect_inertia :
    u_P_c / (u_c^(2:ℤ)) = u_rho_tau ∧
    u_rho_tau * u_accel = u_grad_P ∧
    (u_l_p^(4:ℤ)) / u_l_p = u_Volume ∧
    u_Volume * (u_Volume^(3:ℤ)) = u_l_p^(12:ℤ) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Effective relativistic inertial density of an incompatible defect (Manuscript Eq. 50):
    `ρ_eff = ρ_τ + P / c^2`. -/
noncomputable def rho_defect_eff (P_val : ℝ) : ℝ :=
  rho_tau + P_val / c^2

-- Theorem 33: Relativistic Defect Inertial Density Compliance Factor (ρ_eff = ρ_τ (1 + P / 2P_c))
theorem defect_inertia_compliance_factor (P_val : ℝ) :
    rho_defect_eff P_val = rho_tau * (1 + P_val / (2 * P_c)) := by
  dsimp [rho_defect_eff, P_c]
  have hc : c ≠ 0 := c_ne_zero
  have hrho : rho_tau ≠ 0 := rho_tau_ne_zero
  field_simp

-- Theorem 34: Compliance-Modified Defect Momentum Balance (Manuscript Eq. 52)
theorem incompatible_defect_momentum_eq52 (P_val : ℝ)
    (h_eff_ne : rho_defect_eff P_val ≠ 0)
    (h_balance : (rho_defect_eff P_val) • a_lambda = (rho_defect_eff P_val) • g_lambda + F_surf_lambda) :
    a_lambda = g_lambda + (1 / rho_defect_eff P_val) • F_surf_lambda := by
  have h_scale := congrArg ((1 / rho_defect_eff P_val) • ·) h_balance
  rw [smul_add, smul_smul, smul_smul] at h_scale
  have h_inv : (1 / rho_defect_eff P_val) * rho_defect_eff P_val = 1 :=
    one_div_mul_cancel h_eff_ne
  rw [h_inv, one_smul, one_smul] at h_scale
  exact h_scale

-- ----------------------------------------------------------------------
-- 5.3 The Archimedean Limit of the Geodesic Equation (Manuscript Eqs. 53–63)
-- ----------------------------------------------------------------------

-- Theorem 35: Archimedean Geodesic Buoyancy Acceleration & Newtonian Limit (Manuscript Eqs. 54, 63)
theorem archimedean_buoyancy_and_newtonian_limit
    (a_buoy grad_P_static_scalar F_g V_eff m_tau M_defect k_defect r_val : ℝ)
    (h_geodesic : a_buoy = - (c^2 / (2 * P_c)) * grad_P_static_scalar)
    (h_V_eff : V_eff = m_tau / rho_tau)
    (h_k : k_defect = rho_tau * G * M_defect)
    (h_archimedes : F_g = - V_eff * (k_defect / r_val^2)) :
    a_buoy = - (1 / rho_tau) * grad_P_static_scalar ∧
    F_g = - (G * M_defect * m_tau) / r_val^2 := by
  have h_2Pc : 2 * P_c = rho_tau * c^2 := by
    dsimp [P_c]
    ring
  have hc2 : c^2 ≠ 0 := pow_ne_zero 2 c_ne_zero
  have hrho : rho_tau ≠ 0 := rho_tau_ne_zero
  have h_ratio : c^2 / (2 * P_c) = 1 / rho_tau := by
    rw [h_2Pc]
    calc c^2 / (rho_tau * c^2) = (1 * c^2) / (rho_tau * c^2) := by ring
      _ = 1 / rho_tau := mul_div_mul_right 1 rho_tau hc2
  refine ⟨?_, ?_⟩
  · rw [h_geodesic, h_ratio]
  · rw [h_archimedes, h_V_eff, h_k]
    calc - (m_tau / rho_tau) * (rho_tau * G * M_defect / r_val^2)
      _ = (- (G * M_defect * m_tau) / r_val^2) * (rho_tau / rho_tau) := by ring
      _ = - (G * M_defect * m_tau) / r_val^2 := by rw [div_self hrho, mul_one]

-- Theorem 38: Quadratic Gravitational Action Trace Reduction (Manuscript Eqs. 67–69)
theorem quadratic_gravitational_lagrangian_trace (S_sq G_sq R_sq R_scalar Lambda_val : ℝ)
    (h_G_sq : G_sq = R_sq - R_scalar^2 + (1 / 4) * R_scalar^2 * I_2_vac)
    (h_S_sq : S_sq = (1 / Lambda_val^2) * G_sq - (2 / Lambda_val) * R_scalar + I_2_vac) :
    G_sq = R_sq ∧ S_sq = (1 / Lambda_val^2) * R_sq - (2 / Lambda_val) * R_scalar + 4 := by
  have h_vac : I_2_vac = 4 := I_2_vac_equals_4
  have hG : G_sq = R_sq := by
    rw [h_G_sq, h_vac]
    ring
  refine ⟨hG, ?_⟩
  rw [h_S_sq, hG, h_vac]

-- ----------------------------------------------------------------------
-- 6.2 Strain Incompatibility & Riemann Curvature (Manuscript Eqs. 70–73)
-- ----------------------------------------------------------------------

-- Dimensional Audit: Cauchy strain (P_dyn / (2 P_c α_s^2)) is dimensionless, Burgers vector is length (l_p),
-- and Saint-Venant Incompatibility / Linearized Riemann Curvature has dimension 1 / L^2 (u_Curvature):
theorem unit_section6_2_incompatibility :
    u_P_c / (u_P_c * (u_dimless^(2:ℤ))) = u_dimless ∧
    u_l_p * u_dimless = u_l_p ∧
    u_dimless / (u_l_p^(2:ℤ)) = u_Curvature := by
  refine ⟨rfl, rfl, rfl⟩

/-- Symmetric Cauchy strain tensor `ε_μν = (1/2) (S_μν - η_μν)` (Manuscript Eq. 70).
    For spatial indices `i, j ∈ {1, 2, 3}`, `η_ij = δ_ij`, extracting `ε_ij = (1/2)(S_ij - δ_ij)`. -/
noncomputable def cauchy_strain (S : T2) : T2 :=
  Matrix.of (fun μ ν => (1 / 2) * (S μ ν - eta_metric μ ν))

/-- Second-order coordinate partial derivative `∂_i ∂_j f(x)` on `SpaceTime`. -/
noncomputable def partial_deriv2 (f : ScalarField) (i j : Fin 4) (x : SpaceTime) : ℝ :=
  partial_deriv (fun y => partial_deriv f j y) i x

/-- The Saint-Venant Incompatibility Tensor `Inc(ε)_ijkl` (Manuscript Eq. 71):
    `Inc(ε)_ijkl = ∂_j ∂_l ε_ik + ∂_i ∂_k ε_jl - ∂_j ∂_k ε_il - ∂_i ∂_l ε_jk`. -/
noncomputable def saint_venant_inc (ε : MetricField) (x : SpaceTime) (i j k l : Fin 4) : ℝ :=
  partial_deriv2 (fun y => ε y i k) j l x +
  partial_deriv2 (fun y => ε y j l) i k x -
  partial_deriv2 (fun y => ε y i l) j k x -
  partial_deriv2 (fun y => ε y j k) i l x

/-- Linearized Riemann Curvature Tensor `R_ijkl^(lin) = Inc(ε)_ijkl` (Manuscript Eq. 73). -/
noncomputable def linearized_riemann (ε : MetricField) (x : SpaceTime) (i j k l : Fin 4) : ℝ :=
  saint_venant_inc ε x i j k l

-- Theorem 148: Cauchy Strain Spatial Extraction & Dynamic Pressure Link (Manuscript Eq. 70)
-- Proves directly from `U_sym` that the spatial diagonal Cauchy strain evaluates to
-- `(1/2) * (1 / alpha_s^2 - 1) = P_dyn / (2 * P_c * alpha_s^2)` and vanishes in the unperturbed vacuum (`alpha_s = 1`).
theorem cauchy_strain_spatial_diagonal (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta : V4)
    (t_p_val P_dyn_local : ℝ) (ha_s : alpha_s ≠ 0)
    (h_admittance : alpha_s^2 = 1 - P_dyn_local / P_c) :
    (cauchy_strain (U_sym alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val)) 1 1 =
      (1 / 2) * (1 / alpha_s^2 - 1) ∧
    (cauchy_strain (U_sym 1 alpha v_x v_y v_z d_lambda d_beta t_p_val)) 1 1 = 0 ∧
    (1 / 2) * (1 / alpha_s^2 - 1) = P_dyn_local / (2 * P_c * alpha_s^2) := by
  have hPc : P_c ≠ 0 := Pc_non_zero
  have ha2 : alpha_s^2 ≠ 0 := pow_ne_zero 2 ha_s
  refine ⟨?_, ?_, ?_⟩
  · dsimp [cauchy_strain, U_sym, symPart, U_hat, eta_metric, Matrix.of_apply]
    norm_num
  · dsimp [cauchy_strain, U_sym, symPart, U_hat, eta_metric, Matrix.of_apply]
    norm_num
  · have h_sub : 1 - alpha_s^2 = P_dyn_local / P_c := by linarith
    calc (1 / 2) * (1 / alpha_s^2 - 1)
      _ = (1 - alpha_s^2) / (2 * alpha_s^2) := by field_simp;
      _ = (P_dyn_local / P_c) / (2 * alpha_s^2) := by rw [h_sub]
      _ = P_dyn_local / (2 * P_c * alpha_s^2) := by ring

-- Theorem 149: Saint-Venant Compatibility of the Homogeneous Euclidean Vacuum (Manuscript Eq. 71)
-- Proves without axioms that any spatially uniform strain field `fun _ => ε_const` has vanishing
-- second-order Fréchet derivatives and satisfies the Saint-Venant compatibility condition `Inc(ε)_ijkl = 0`.
theorem saint_venant_homogeneous_flatness (ε_const : T2) (x : SpaceTime) (i j k l : Fin 4) :
    saint_venant_inc (fun _ : SpaceTime => ε_const) x i j k l = 0 := by
  dsimp [saint_venant_inc, partial_deriv2, partial_deriv]
  simp

-- Theorem 150: Topological Volterra Dislocation & Burgers Vector Phase Gap (Manuscript Eq. 72)
-- Proves that when circulation around a rotational Clebsch vortex induces a non-vanishing Burgers
-- displacement gap `b_i = Area * Inc_flux` (`b_i ≠ 0`), the strain field is structurally incompatible (`Inc_flux ≠ 0`),
-- whereas an irrotational single-valued displacement (`Inc_flux = 0`) yields a zero Burgers vector (`b_i = 0`).
theorem burgers_dislocation_incompatibility (contour_du_i b_i Area_core Inc_flux : ℝ)
    (h_burgers_def : contour_du_i = b_i)
    (h_stokes_dislocation : b_i = Area_core * Inc_flux) :
    (Inc_flux = 0 → contour_du_i = 0) ∧
    (b_i ≠ 0 → Inc_flux ≠ 0) := by
  refine ⟨?_, ?_⟩
  · intro h_zero
    rw [h_burgers_def, h_stokes_dislocation, h_zero, mul_zero]
  · intro hb_ne h_inc_zero
    apply hb_ne
    rw [h_stokes_dislocation, h_inc_zero, mul_zero]

-- Theorem 151: Linearized Riemann-Kröner Curvature Identities & Skew-Symmetry (Manuscript Eq. 73)
-- Proves that the linearized Riemann curvature `R_ijkl^(lin) = Inc(ε)_ijkl` satisfies exact index
-- antisymmetry in `(i, j)` and `(k, l)` and vanishes along repeated index pairs (`R_iikl = 0`, `R_ijkk = 0`).
theorem linearized_riemann_kroner_identities (ε : MetricField) (x : SpaceTime) (i j k l : Fin 4) :
    linearized_riemann ε x i j k l = saint_venant_inc ε x i j k l ∧
    linearized_riemann ε x j i k l = - linearized_riemann ε x i j k l ∧
    linearized_riemann ε x i j l k = - linearized_riemann ε x i j k l ∧
    linearized_riemann ε x i i k l = 0 ∧
    linearized_riemann ε x i j k k = 0 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
  { dsimp [linearized_riemann, saint_venant_inc]
    ring }

-- ======================================================================
-- SECTION 7: CONFORMAL SYMMETRY & THE LIE DERIVATIVE CONSTRAINTS
-- ======================================================================

-- ----------------------------------------------------------------------
-- 7.0 Covariant Rank-2 Lie Derivative Operator (Manuscript Eq. 90)
-- ----------------------------------------------------------------------

/-- Covariant rank-2 tensor Lie derivative (Manuscript Eq. 90):
    `(£_X U)_μν = ∑_α (X^α ∂_α U_μν + U_αν ∂_μ X^α + U_μα ∂_ν X^α)`. -/
noncomputable def lie_derivative (X : VectorField) (U : MetricField) (x : SpaceTime) : T2 :=
  fun μ ν => ∑ α : Fin 4, (
    (X x α) * partial_deriv (fun y => U y μ ν) α x +
    (U x α ν) * partial_deriv (fun y => X y α) μ x +
    (U x μ α) * partial_deriv (fun y => X y α) ν x)

def is_translationally_symmetric (U : MetricField) (X : VectorField) (x : SpaceTime) : Prop :=
  lie_derivative X U x = 0

-- ----------------------------------------------------------------------
-- 7.1 The Poincare Subgroup (10 Generators) (Manuscript Eqs. 91–96)
-- ----------------------------------------------------------------------
variable (alpha_s_val : ℝ)

-- Theorem 42.5 (Resolves Issue #11 Operator Bridge — Manuscript Eqs. 90–91):
-- Proves directly from `lie_derivative` that for any uniform translation field `X`
-- with vanishing coordinate Jacobian (`partial_deriv (fun y => X y α) = 0`),
-- the 3-term covariant Lie derivative reduces to the directional gradient `∑_α X^α ∂_α U_μν`.
theorem lie_derivative_translation_bridge (X : VectorField) (U : MetricField) (x : SpaceTime)
    (h_const_X : ∀ (α μ : Fin 4), partial_deriv (fun y => X y α) μ x = 0)
    (μ ν : Fin 4) :
    lie_derivative X U x μ ν =
    ∑ α : Fin 4, (X x α) * partial_deriv (fun y => U y μ ν) α x := by
  dsimp [lie_derivative]
  apply Finset.sum_congr rfl
  intro α _
  rw [h_const_X α μ, h_const_X α ν]
  ring

lemma isolate_lorentz_scalar (omega_0i alpha_val : ℝ) (h_omega : omega_0i ≠ 0) (h_pos : alpha_val > 0) :
  omega_0i * ((1 / alpha_val^2) - alpha_val^2) = 0 → alpha_val = 1 := by
  intro h
  have h1 : (1 / alpha_val^2) - alpha_val^2 = 0 := by
    cases mul_eq_zero.mp h with
    | inl h_eq => exact False.elim (h_omega h_eq)
    | inr h_eq => exact h_eq
  have h2 : 1 / alpha_val^2 = alpha_val^2 := by linarith
  have ha_ne : alpha_val ≠ 0 := ne_of_gt h_pos
  have ha2_ne : alpha_val^2 ≠ 0 := pow_ne_zero 2 ha_ne
  have h3 : (1 / alpha_val^2) * alpha_val^2 = alpha_val^2 * alpha_val^2 := congrArg (· * alpha_val^2) h2
  have h4 : 1 = alpha_val^4 := by
    have h_L : (1 / alpha_val^2) * alpha_val^2 = 1 := div_mul_cancel₀ 1 ha2_ne
    have h_R : alpha_val^2 * alpha_val^2 = alpha_val^4 := by ring
    rw [h_L, h_R] at h3
    exact h3
  have h_mul : alpha_val^4 = 1 := by rw [h4]
  have h5 : alpha_val^4 - 1 = 0 := by linarith
  have h6 : (alpha_val^2 - 1) * (alpha_val^2 + 1) = 0 := by
    have h_factor : (alpha_val^2 - 1) * (alpha_val^2 + 1) = alpha_val^4 - 1 := by ring
    rw [h_factor, h5]
  have h8 : alpha_val^2 - 1 = 0 := by
    cases mul_eq_zero.mp h6 with
    | inl hl => exact hl
    | inr hr =>
      have h_pos2 : alpha_val^2 ≥ 0 := sq_nonneg alpha_val
      linarith
  have h10 : (alpha_val - 1) * (alpha_val + 1) = 0 := by
    have h_factor2 : (alpha_val - 1) * (alpha_val + 1) = alpha_val^2 - 1 := by ring
    rw [h_factor2, h8]
  cases mul_eq_zero.mp h10 with
  | inl hl => linarith
  | inr hr => linarith

-- Theorem 43: Lorentz Boost Symmetry Breaking Limit (α_s = 1, Manuscript Eq. 95)
theorem lorentz_symmetry_broken (omega_0i : ℝ) (h_nonzero : omega_0i ≠ 0) (h_pos : alpha_s_val > 0)
    (h_residual : omega_0i * ((1 / alpha_s_val^2) - alpha_s_val^2) = 0) :
    alpha_s_val = 1 := by
  exact isolate_lorentz_scalar omega_0i alpha_s_val h_nonzero h_pos h_residual

-- Theorem 43a: Operator-Derived Lorentz Boost Lie Residual & Vacuum Reduction (Resolves Issue #11)
-- Evaluates the 3-term covariant `lie_derivative` operator at `(0, 1)` on a homogeneous rest-frame
-- metric field `U` (`U_{00} = -α_s^2`, `U_{11} = 1 / α_s^2`, `∂_α U_{01} = 0`) along a Lorentz
-- boost
-- generator `X` in the `(0, 1)` plane (`∂_0 X^α = δ^α_1 ω_{01}`, `∂_1 X^α = δ^α_0 ω_{01}`):
-- 1. Operator Evaluation: `lie_derivative X U x 0 1 = ω_{01} * ((1 / α_s^2) - α_s^2)`,
-- 2. Symmetry Breaking Consequence: `lie_derivative X U x 0 1 = 0` with `ω_{01} ≠ 0` forces `α_s =
-- 1`.
theorem lie_derivative_boost_residual_bridge
    (X : VectorField) (U : MetricField) (x : SpaceTime) (omega_0i : ℝ)
    (h_nonzero : omega_0i ≠ 0) (h_pos : alpha_s_val > 0)
    (h_homog : ∀ α : Fin 4, partial_deriv (fun y => U y 0 1) α x = 0)
    (h_dX0 : ∀ α : Fin 4, partial_deriv (fun y => X y α) 0 x = if α = 1 then omega_0i else 0)
    (h_dX1 : ∀ α : Fin 4, partial_deriv (fun y => X y α) 1 x = if α = 0 then omega_0i else 0)
    (h_U00 : U x 0 0 = -alpha_s_val^2)
    (h_U11 : U x 1 1 = 1 / alpha_s_val^2) :
    lie_derivative X U x 0 1 = omega_0i * ((1 / alpha_s_val^2) - alpha_s_val^2) ∧
    (lie_derivative X U x 0 1 = 0 → alpha_s_val = 1) := by
  have h_eval : lie_derivative X U x 0 1 = omega_0i * ((1 / alpha_s_val^2) - alpha_s_val^2) := by
    dsimp [lie_derivative]
    rw [Fin.sum_univ_four]
    rw [h_homog 0, h_homog 1, h_homog 2, h_homog 3]
    rw [h_dX0 0, h_dX0 1, h_dX0 2, h_dX0 3]
    rw [h_dX1 0, h_dX1 1, h_dX1 2, h_dX1 3]
    rw [h_U00, h_U11]
    norm_num
    ring
  refine ⟨h_eval, ?_⟩
  intro h_zero
  rw [h_eval] at h_zero
  exact isolate_lorentz_scalar omega_0i alpha_s_val h_nonzero h_pos h_zero

-- ----------------------------------------------------------------------
-- 7.2 Dilation & Special Conformal Transformations (5 Generators) (Manuscript Eqs. 97–106)
-- ----------------------------------------------------------------------
variable (x_i a_i grad_P_dyn : ℝ)

-- Dimensional Audit: Conformal generator coupling 4 x_i (a_i / c^2) = -(2 / P_c)(x_i grad_P_dyn) is dimensionless on both sides:
theorem unit_section7_conformal_pressure_coupling :
    u_l_p * (u_accel / (u_c^(2:ℤ))) = u_dimless ∧
    (u_dimless / u_P_c) * (u_l_p * u_grad_P) = u_dimless := by
  constructor <;> rfl

-- Theorem 44: Special Conformal Generator Pressure Coupling (Manuscript Eq. 103)
theorem conformal_pressure_coupling (h_a : a_i = - (1 / rho_tau) * grad_P_dyn) :
    4 * (x_i * (a_i / c^2)) = - (2 / P_c) * (x_i * grad_P_dyn) := by
  rw [h_a]
  have h_Pc_sub : P_c = (1 / 2) * rho_tau * c^2 := emergent_critical_pressure
  have h1 : 4 * (x_i * ((- (1 / rho_tau) * grad_P_dyn) / c^2)) = - (4 / (rho_tau * c^2)) * (x_i * grad_P_dyn) := by ring
  have h2 : - (4 / (rho_tau * c^2)) * (x_i * grad_P_dyn) = - (2 / ((1 / 2) * rho_tau * c^2)) * (x_i * grad_P_dyn) := by ring
  rw [h1, h2, ←h_Pc_sub]

/-- Gordon Optical Metric (Manuscript Eq. 105):
    `U^opt_μν = U_μν + (1 - 1/n^2) u_μ u_ν`. -/
noncomputable def U_optical (U : T2) (n_idx : ℝ) (u : V4) : T2 :=
  Matrix.of (fun μ ν => U μ ν + (1 - 1 / n_idx^2) * (u μ * u ν))

-- Theorem 45: Gordon Optical Metric Admittance Substitution (U^opt_μν = U_μν + (1 - α_s^4) u_μ u_ν, Manuscript Eqs. 104–106)
theorem gordon_optical_metric_admittance (U : T2) (n_idx alpha_s_opt : ℝ) (u : V4)
    (ha_s : alpha_s_opt ≠ 0)
    (h_refractive : n_idx = 1 / alpha_s_opt^2) :
    U_optical U n_idx u =
    Matrix.of (fun μ ν => U μ ν + (1 - alpha_s_opt^4) * (u μ * u ν)) := by
  ext μ ν
  dsimp [U_optical, Matrix.of_apply]
  rw [h_refractive]
  have ha4 : alpha_s_opt^4 ≠ 0 := pow_ne_zero 4 ha_s
  have h_prod : (1 / alpha_s_opt^2)^2 * alpha_s_opt^4 = 1 := by
    calc (1 / alpha_s_opt^2)^2 * alpha_s_opt^4
      _ = alpha_s_opt^4 / alpha_s_opt^4 := by ring
      _ = 1 := div_self ha4
  have h_inv_sq : 1 / (1 / alpha_s_opt^2)^2 = alpha_s_opt^4 := by
    have h_ne : (1 / alpha_s_opt^2)^2 ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at h_prod
      exact zero_ne_one h_prod
    calc 1 / (1 / alpha_s_opt^2)^2
      _ = ((1 / alpha_s_opt^2)^2 * alpha_s_opt^4) / (1 / alpha_s_opt^2)^2 := by rw [h_prod]
      _ = alpha_s_opt^4 * ((1 / alpha_s_opt^2)^2 / (1 / alpha_s_opt^2)^2) := by ring
      _ = alpha_s_opt^4 := by rw [div_self h_ne, mul_one]
  rw [h_inv_sq]

-- ----------------------------------------------------------------------
-- 7.3 Kinematic Implications of Symmetry Breaking
-- ----------------------------------------------------------------------

-- Dimensional Audit: Capacity variance (1/α_s^2 - α_s^2) and refractive index n are dimensionless,
-- normalized pressure gradient (∇P_dyn / P_c) has dimension 1/L, and phase velocity (c / n) has dimension u_c:
theorem unit_section7_3_symmetry_breaking :
    u_P_c / u_P_c = u_dimless ∧
    u_grad_P / u_P_c = u_dimless / u_l_p ∧
    u_c / u_dimless = u_c := by
  refine ⟨rfl, rfl, rfl⟩

-- Theorem 152: Symmetry-Breaking Capacity Variance & Gordon Optical Deflection
-- Proves that the Lorentz boost Lie-derivative residual factor (1 / alpha_s^2 - alpha_s^2)
-- equals the Gordon optical metric factor (n^2 - 1) / n (for n = 1 / alpha_s^2) and satisfies
-- (1 / alpha_s^2 - alpha_s^2) * alpha_s^2 = (P_dyn / P_c) * (2 - P_dyn / P_c).
-- In the unperturbed vacuum (alpha_s = 1) the residual vanishes, whereas under subcritical
-- kinematic strain (0 < alpha_s < 1) it is strictly positive, driving null geodesic deflection.
theorem symmetry_breaking_gordon_deflection (alpha_s n_val P_dyn_local : ℝ)
    (ha_pos : 0 < alpha_s) (ha_lt_one : alpha_s < 1)
    (h_n : n_val = 1 / alpha_s^2)
    (h_admittance : alpha_s^2 = 1 - P_dyn_local / P_c) :
    1 / alpha_s^2 - alpha_s^2 = (n_val^2 - 1) / n_val ∧
    (1 / alpha_s^2 - alpha_s^2) * alpha_s^2 = (P_dyn_local / P_c) * (2 - P_dyn_local / P_c) ∧
    1 / (1 : ℝ)^2 - (1 : ℝ)^2 = 0 ∧
    0 < 1 / alpha_s^2 - alpha_s^2 := by
  have ha_ne : alpha_s ≠ 0 := ne_of_gt ha_pos
  refine ⟨?_, ?_, by norm_num, ?_⟩
  · rw [h_n]
    field_simp

  · have h_lhs : (1 / alpha_s^2 - alpha_s^2) * alpha_s^2 = 1 - (alpha_s^2)^2 := by
      field_simp

    rw [h_lhs, h_admittance]
    ring
  · have h_fact : 1 / alpha_s^2 - alpha_s^2 =
        (1 - alpha_s) * (1 + alpha_s) * (1 + alpha_s^2) / alpha_s^2 := by
      field_simp
      ring
    have h1 : 0 < 1 - alpha_s := by linarith
    have h2 : 0 < 1 + alpha_s := by linarith
    rw [h_fact]
    positivity

-- ----------------------------------------------------------------------
-- 7.4 Conserved Noether Currents (Manuscript Eqs. 107–109)
-- ----------------------------------------------------------------------

-- Dimensional Audit: Stress-energy divergence (∂_μ T^μν) has dimension u_grad_P (Force / Volume),
-- and angular momentum current divergence (∂_μ M^μαβ = ∂_μ (x^α T^μβ + Σ^μαβ)) has dimension u_P_c (Torque / Volume):
theorem unit_section7_4_noether_currents :
    u_P_c / u_l_p = u_grad_P ∧
    (u_l_p * u_P_c) / u_l_p = u_P_c ∧
    (u_P_c * u_dimless) * u_l_p = u_l_p * u_P_c := by
  refine ⟨rfl, rfl, rfl⟩

/-- Canonical Noether current density `J^μ = (∂L / ∂(∂_μ U_αβ)) L_ξ U_αβ - ξ^μ L_metric` (Manuscript Eq. 107). -/
noncomputable def noether_current_density (dL_dU_grad L_xi_U xi_mu L_metric : ℝ) : ℝ :=
  dL_dU_grad * L_xi_U - xi_mu * L_metric

/-- Macroscopic orbital angular momentum tensor `L^μαβ = x^α T^μβ - x^β T^μα` (Manuscript Section 7.4.2). -/
noncomputable def orbital_angular_momentum (x_pos : V4) (T : T2) (μ α β : Fin 4) : ℝ :=
  x_pos α * T μ β - x_pos β * T μ α

/-- Total Lorentz Noether current (Total Angular Momentum) `M^μαβ = L^μαβ + Σ^μαβ` (Manuscript Eq. 109). -/
noncomputable def total_angular_momentum
    (x_pos : V4) (T : T2) (Sigma_spin : Fin 4 → Fin 4 → Fin 4 → ℝ) (μ α β : Fin 4) : ℝ :=
  orbital_angular_momentum x_pos T μ α β + Sigma_spin μ α β

-- Theorem 153: Translational Noether Current & Stress-Energy Conservation (Manuscript Eqs. 107–108)
-- Proves that when the translational Lie derivative vanishes (`L_xi_U = 0`), the canonical Noether
-- current reduces to `-xi_mu * L_metric`, and proves from `covariant_conservation` and
-- `homogeneous_vacuum_is_divergence_free` that both the scaled metric divergence `P_c * ∂_μ U^μν`
-- and the flat background divergence `∂_μ η^μν` vanish identically at every spacetime point `x` (`∂_μ T^μν = 0`).
theorem noether_translational_stress_conservation
    (dL_dU_grad L_xi_U xi_mu L_metric : ℝ) (x : SpaceTime)
    (h_trans_sym : L_xi_U = 0) :
    noether_current_density dL_dU_grad L_xi_U xi_mu L_metric = - xi_mu * L_metric ∧
    (∀ ν : Fin 4, P_c * (metric_divergence U_hat_dynamic x ν) = 0) ∧
    metric_divergence (fun _ : SpaceTime => eta_metric) x = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [noether_current_density]
    rw [h_trans_sym]
    ring
  · intro ν
    have h_div := congrFun (covariant_conservation x) ν
    change metric_divergence U_hat_dynamic x ν = 0 at h_div
    rw [h_div, mul_zero]
  · exact homogeneous_vacuum_is_divergence_free eta_metric x

-- Theorem 154: Lorentz Noether Current, Antisymmetric Stress Torque & Clebsch Spin Conservation (Manuscript Eq. 109)
-- Proves that orbital angular momentum `L^μαβ` is strictly antisymmetric in `(α, β)`; proves directly
-- from `constitutive_stress`, `U_hat`, and `U_anti` that the antisymmetric stress difference
-- `T_12 - T_21` equals `2 * P_c * A_12 = -2 * P_c * α * t_p * Ω_z(dλ_Ω, dβ_Ω)` (requiring the internal
-- Clebsch spin tensor `Σ^μαβ`); and proves that vanishing rotational Lie residual (`rot_residual = 0`)
-- enforces total angular momentum conservation (`∂_μ M^μαβ = ∂_μ L^μαβ + ∂_μ Σ^μαβ = 0`).
theorem noether_lorentz_spin_conservation
    (alpha_s alpha v_x v_y v_z : ℝ) (d_lambda d_beta x_pos : V4) (t_p_val : ℝ)
    (T : T2) (μ α β : Fin 4) (div_L div_Sigma rot_residual : ℝ)
    (h_rot_sym : rot_residual = 0)
    (h_spin_balance : div_L + div_Sigma = rot_residual) :
    orbital_angular_momentum x_pos T μ α β = - orbital_angular_momentum x_pos T μ β α ∧
    constitutive_stress (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 2 -
    constitutive_stress (U_hat alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 2 1 =
      2 * P_c * (U_anti alpha_s alpha v_x v_y v_z d_lambda d_beta t_p_val) 1 2 ∧
    div_L + div_Sigma = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [orbital_angular_momentum]
    ring
  · dsimp [constitutive_stress, U_hat, U_anti, antiPart, eta_metric, Matrix.of_apply]
    norm_num
    ring
  · rw [h_spin_balance, h_rot_sym]

-- ----------------------------------------------------------------------
-- 7.5 The Dressing Field Method (Gauge-Invariant Composites) (Manuscript Eqs. 110–112)
-- ----------------------------------------------------------------------

/-- Bare gauge-transformed transverse slip 1-form: `v_⊥^g = v_⊥ - dχ`. -/
noncomputable def v_perp_g (v_perp_form : Forms_1D) (chi : Forms_0D) : Forms_1D :=
  v_perp_form - d0 chi

/-- Bare gauge-transformed longitudinal scalar phase 0-form: `h^g = h + χ`. -/
noncomputable def h_g (h chi : Forms_0D) : Forms_0D :=
  h + chi

-- Theorem 46: Abelian Dressing Field Gauge Invariance of the Composite Velocity 1-Form (Manuscript Eqs. 110–111)
theorem dressing_field_invariance (v_perp_form : Forms_1D) (h chi : Forms_0D) :
    (v_perp_g d0 v_perp_form chi) + grad_h d0 (h_g h chi) = v_perp_form + grad_h d0 h := by
  dsimp [v_perp_g, h_g, grad_h]
  rw [map_add]
  abel

theorem v_macro_dressing_invariance (h chi lambda_Omega beta_Omega : Forms_0D) (v_perp_form : Forms_1D) :
    v_macro d0 smul_form (h_g h chi) lambda_Omega beta_Omega (v_perp_g d0 v_perp_form chi) =
    v_macro d0 smul_form h lambda_Omega beta_Omega v_perp_form := by
  dsimp [v_macro, v_perp_g, h_g, grad_h]
  rw [map_add]
  abel

-- Theorem 47: Relational Spacetime Vorticity Wedge Identity (Ω_μν = (dλ_Ω ∧ dβ_Ω)_μν, Manuscript Eq. 112)
theorem relational_vorticity_wedge_identity (lambda_f beta_f : ScalarField) (x : SpaceTime) (μ ν : Fin 4) :
    Omega_clebsch_field lambda_f beta_f x μ ν =
    partial_deriv lambda_f μ x * partial_deriv beta_f ν x -
    partial_deriv lambda_f ν x * partial_deriv beta_f μ x := by
  dsimp [Omega_clebsch_field, omega_clebsch_2form, wedge_covec, d_scalar_field, Matrix.of_apply]

end AsymmetricTensor
