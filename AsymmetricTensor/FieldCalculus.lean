/-
Copyright (c) 2026 Binyamin Tsadik Bair-Mosheh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Binyamin Tsadik Bair-Mosheh
-/
module

public import AsymmetricTensor.MatrixAlgebra

/-!
# Coordinate fields, derivatives, and conditional conservation

See `docs/modules.md` for the module map and compatibility policy.
The manuscript terminology and the mathematical statements are retained.
-/

@[expose] public section

open Real BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars true

namespace AsymmetricTensor


-- ==========================================
-- SECTION 5: Continuous Differential Geometry & The Equation of Motion (v2.0)
-- ==========================================

-- 5.1 Spacetime Manifold & Continuous Fields
-- We define continuous 4D spacetime natively as a mapping from 4 indices to Reals.
/--
A single global coordinate space ℝ⁴. No connection, curvature, manifold atlas, or causal
structure is supplied by this alias.
-/
abbrev SpaceTime := Fin 4 → ℝ

-- Physical quantities are promoted from static scalars/tensors to dynamic fields.
/--
An arbitrary real function on the fixed coordinate space; regularity must be supplied
separately.
-/
abbrev ScalarField := SpaceTime → ℝ
/-- An arbitrary coordinate-vector-valued function; no differentiability is implicit. -/
abbrev VectorField := SpaceTime → SpaceTime
/-- An arbitrary component-matrix-valued function on the fixed chart.
The Lie derivative treats its entries as covariant `(0,2)` components; this alias
does not impose symmetry, nondegeneracy, regularity, conservation, or a chart-change law. -/
abbrev MetricField := SpaceTime → T2

-- 5.2 Coordinate Partial Derivatives and Divergence
/-- Coordinate derivative in the direction of the μ-th standard basis vector.
For a classical derivative interpretation, the scalar field must be differentiable
at `x`. No connection or covariant derivative is encoded here. -/
noncomputable def partial_deriv (f : ScalarField) (μ : Fin 4) (x : SpaceTime) : ℝ :=
  (fderiv ℝ f x) (fun i => if i = μ then 1 else 0)

/-- Partial divergence of a component matrix in the fixed chart on ℝ⁴.
This is not a general covariant divergence: there are no connection terms. -/
noncomputable def metric_divergence (U : MetricField) (x : SpaceTime) : V4 :=
  fun ν => ∑ μ : Fin 4, partial_deriv (fun y => U y μ ν) μ x

-- 5.3 Conditional Coordinate Conservation
/-- The explicitly assumed coordinate-divergence constraint on an admissible field.
It is not asserted for every `MetricField`, nor derived from equations of motion. -/
def CoordinateConserved (U : MetricField) : Prop :=
  ∀ x : SpaceTime, metric_divergence U x = 0

/-- Constant component fields satisfy the coordinate conservation constraint. -/
theorem constant_coordinate_conserved (A : T2) :
    CoordinateConserved (fun _ => A) := by
  intro x
  ext ν
  simp [metric_divergence, partial_deriv]

/-- The constraint has a nonempty class of solutions, independently of physical axioms. -/
theorem exists_coordinate_conserved : ∃ U : MetricField, CoordinateConserved U :=
  ⟨fun _ => 0, constant_coordinate_conserved 0⟩

/-- The linear coordinate field is a counterexample to universal conservation. -/
theorem coordinate_field_not_conserved :
    ¬ CoordinateConserved (fun x _ _ => x 0) := by
  intro h
  have hd (μ : Fin 4) (x : SpaceTime) :
      partial_deriv (fun y : SpaceTime => y 0) μ x =
        if (0 : Fin 4) = μ then 1 else 0 := by
    simp [partial_deriv, fderiv_apply]
  have h1 : metric_divergence (fun x _ _ => x 0) 0 0 = 1 := by
    simp [metric_divergence, hd]
  have h0 := congrFun (h 0) 0
  simp only [Pi.zero_apply] at h0
  linarith

/-- Time-component projection of an assumed coordinate-conservation law.
This alone is not a derivation of Bernoulli's equation. -/
theorem bernoulli_energy_conservation (U : MetricField)
    (hU : CoordinateConserved U) (x : SpaceTime) :
    (metric_divergence U x) 0 = 0 := by
  rw [hU x]
  rfl

/-- Spatial-component projection of an assumed coordinate-conservation law.
This alone is not a derivation of the Navier–Stokes momentum PDE. -/
theorem navier_stokes_momentum_conservation (U : MetricField)
    (hU : CoordinateConserved U) (x : SpaceTime) (i : Fin 4)
    (_h_spatial : i ≠ 0) :
    (metric_divergence U x) i = 0 := by
  rw [hU x]
  rfl

-- 5.4 The Dynamic Kinematic Fields
opaque alpha_s_f : ScalarField
opaque alpha_f : ScalarField
opaque v_x_f : ScalarField
opaque v_y_f : ScalarField
opaque v_z_f : ScalarField
opaque Omega_x_f : ScalarField
opaque Omega_y_f : ScalarField
opaque Omega_z_f : ScalarField

noncomputable def U_hat_dynamic : MetricField :=
  fun x => U_hat (alpha_s_f x) (alpha_f x) (v_x_f x) (v_y_f x) (v_z_f x)
                 (Omega_x_f x) (Omega_y_f x) (Omega_z_f x) t_p

theorem divergence_expansion (x : SpaceTime) (ν : Fin 4) :
    (metric_divergence U_hat_dynamic x) ν =
    ∑ μ : Fin 4, partial_deriv (fun y => U_hat_dynamic y μ ν) μ x := by
  rfl

-- ==========================================
-- 5.5 Physical Projections (Pressure & Shear)
-- ==========================================

-- We mathematically prove that the Planck pressure of the vacuum is strictly
-- non-zero directly from the bedrock Section 0 axioms (bypassing ne_of_gt entirely).
lemma Pc_non_zero : P_c ≠ 0 := by
  have hc := c_pos
  have hl := l_p_pos
  have hh := hbar_pos
  dsimp [P_c, rho_tau]
  positivity

-- 1. The Pressure Projection (Diagonal)
-- Instead of an opaque variable, we natively define the dynamic pressure field
-- as the geometric spatial compliance deviation from the vacuum.
noncomputable def P_dyn_f : ScalarField :=
  fun x => (1 - (alpha_s_f x)^2) * P_c

-- We prove the dynamic compliance link natively from the definition!
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

-- 2. The Transverse Shear Projection (Off-Diagonal)
-- We natively define the macroscopic transverse stress field as the exact scaled geometric shear.
noncomputable def T_perp_f : ScalarField :=
  fun x => - (alpha_f x) * (v_x_f x / c) * P_c

theorem transverse_shear_link (x : SpaceTime) :
  - (alpha_f x) * (v_x_f x / c) = (T_perp_f x) / P_c := by
  unfold T_perp_f
  have h_cancel : - (alpha_f x) * (v_x_f x / c) * P_c / P_c = - (alpha_f x) * (v_x_f x / c) :=
    mul_div_cancel_right₀ (- (alpha_f x) * (v_x_f x / c)) Pc_non_zero
  rw [h_cancel]

theorem shear_divergence_extraction (μ : Fin 4) (x : SpaceTime) :
    partial_deriv (fun y => - (alpha_f y) * (v_x_f y / c)) μ x =
    partial_deriv (fun y => (T_perp_f y) / P_c) μ x := by
  have h_field : (fun y => - (alpha_f y) * (v_x_f y / c)) = (fun y => (T_perp_f y) / P_c) := by
    ext y
    exact transverse_shear_link y
  rw [h_field]

-- ==========================================
-- 5.6 The Grand Unification (Geometric Navier-Stokes)
-- ==========================================

-- 1. We natively define material kinematic acceleration as the exact
-- temporal derivative of the geometric shear.
noncomputable def kinematic_accel_f : ScalarField :=
  fun x => - (partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x) * P_c

theorem acceleration_link (x : SpaceTime) :
  partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x = - (kinematic_accel_f x) / P_c := by
  unfold kinematic_accel_f
  have h1 : - (- (partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x) * P_c) = (partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x) * P_c := by ring
  rw [h1]
  have h_cancel : (partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x) * P_c / P_c = partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x :=
    mul_div_cancel_right₀ (partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x) Pc_non_zero
  rw [h_cancel]

-- 2. Because we proved in 5.5 that the diagonal derivative is the exact nonlinear
-- compliance gradient, we map the diagonal directly to the exact compliance field.
theorem exact_pressure_link (x : SpaceTime) :
  partial_deriv (fun y => U_hat_dynamic y 1 1) 1 x = partial_deriv (fun y => 1 / (1 - (P_dyn_f y) / P_c)) 1 x := by
  have h_diag : (fun y => U_hat_dynamic y 1 1) = (fun y => 1 / (alpha_s_f y)^2) := by rfl
  rw [h_diag]
  exact pressure_gradient_extraction 1 x

-- 3. We natively define the transverse stress divergence as the spatial
-- derivative of the transverse geometric off-diagonals.
noncomputable def div_T_perp_f : ScalarField :=
  fun x => (partial_deriv (fun y => U_hat_dynamic y 2 1) 2 x +
            partial_deriv (fun y => U_hat_dynamic y 3 1) 3 x) * P_c

theorem transverse_divergence_link (x : SpaceTime) :
  partial_deriv (fun y => U_hat_dynamic y 2 1) 2 x +
  partial_deriv (fun y => U_hat_dynamic y 3 1) 3 x = (div_T_perp_f x) / P_c := by
  unfold div_T_perp_f
  have h_cancel : (partial_deriv (fun y => U_hat_dynamic y 2 1) 2 x + partial_deriv (fun y => U_hat_dynamic y 3 1) 3 x) * P_c / P_c = partial_deriv (fun y => U_hat_dynamic y 2 1) 2 x + partial_deriv (fun y => U_hat_dynamic y 3 1) 3 x :=
    mul_div_cancel_right₀ (partial_deriv (fun y => U_hat_dynamic y 2 1) 2 x + partial_deriv (fun y => U_hat_dynamic y 3 1) 3 x) Pc_non_zero
  rw [h_cancel]

/-- Rewrite an assumed zero coordinate-component derivative sum using the defined
acceleration, pressure, and transverse-stress fields. This is conditional component
algebra, not a derivation of a material-acceleration PDE. Its proof uses the six
physical constant/positivity axioms, so it is not axiom-free. -/
theorem geometric_navier_stokes (x : SpaceTime)
    (h_geometric_zero : partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x +
                        partial_deriv (fun y => U_hat_dynamic y 1 1) 1 x +
                        partial_deriv (fun y => U_hat_dynamic y 2 1) 2 x +
                        partial_deriv (fun y => U_hat_dynamic y 3 1) 3 x = 0) :
    (kinematic_accel_f x) / P_c = partial_deriv (fun y => 1 / (1 - (P_dyn_f y) / P_c)) 1 x + (div_T_perp_f x) / P_c := by

  have h1 := acceleration_link x
  have h2 := exact_pressure_link x
  have h3 := transverse_divergence_link x

  have h_sum : (- (kinematic_accel_f x) / P_c) + partial_deriv (fun y => 1 / (1 - (P_dyn_f y) / P_c)) 1 x + ((div_T_perp_f x) / P_c) = 0 := by
    calc (- (kinematic_accel_f x) / P_c) + partial_deriv (fun y => 1 / (1 - (P_dyn_f y) / P_c)) 1 x + ((div_T_perp_f x) / P_c)
      _ = partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x + partial_deriv (fun y => U_hat_dynamic y 1 1) 1 x + (partial_deriv (fun y => U_hat_dynamic y 2 1) 2 x + partial_deriv (fun y => U_hat_dynamic y 3 1) 3 x) := by rw [h1, h2, h3]
      _ = partial_deriv (fun y => U_hat_dynamic y 0 1) 0 x + partial_deriv (fun y => U_hat_dynamic y 1 1) 1 x + partial_deriv (fun y => U_hat_dynamic y 2 1) 2 x + partial_deriv (fun y => U_hat_dynamic y 3 1) 3 x := by ring
      _ = 0 := h_geometric_zero

  calc (kinematic_accel_f x) / P_c
    _ = (kinematic_accel_f x) / P_c + 0 := by ring
    _ = (kinematic_accel_f x) / P_c + ((- (kinematic_accel_f x) / P_c) + partial_deriv (fun y => 1 / (1 - (P_dyn_f y) / P_c)) 1 x + ((div_T_perp_f x) / P_c)) := by rw [h_sum]
    _ = partial_deriv (fun y => 1 / (1 - (P_dyn_f y) / P_c)) 1 x + (div_T_perp_f x) / P_c := by ring


-- ==========================================
-- 5.7 Continuous Symmetries & Lie Derivatives
-- ==========================================

opaque epsilon_vec_f : VectorField

/-- Componentwise directional transport in the fixed chart `SpaceTime = ℝ⁴`.
This is only the first term of the Lie derivative of a covariant rank-two tensor. -/
noncomputable def directional_transport (X : VectorField) (U : MetricField)
    (x : SpaceTime) : T2 :=
  fun μ ν => ∑ α : Fin 4, X x α * partial_deriv (fun y => U y μ ν) α x

/-- The coordinate formula for the Lie derivative of a `(0,2)` tensor (v9, Eq. 91).
Both lower indices contribute with a plus sign; no symmetry of `U` is assumed.

This is a fixed `ℝ⁴` chart, not a manifold/coordinate-change construction.
As with `partial_deriv`, `fderiv` makes the definition total. Its classical
interpretation at `x` requires every component of `X` and `U` to be differentiable
there; `lie_derivative_eq_of_hasFDerivAt` records that interpretation explicitly.
No classical derivative is claimed at a nondifferentiable point. -/
noncomputable def lie_derivative (X : VectorField) (U : MetricField) (x : SpaceTime) : T2 :=
  fun μ ν => directional_transport X U x μ ν +
    (∑ α : Fin 4, U x α ν * partial_deriv (fun y => X y α) μ x) +
    (∑ α : Fin 4, U x μ α * partial_deriv (fun y => X y α) ν x)

/-- The full coordinate formula evaluated at explicitly supplied component derivatives. -/
theorem lie_derivative_eq_of_hasFDerivAt (X : VectorField) (U : MetricField)
    (x : SpaceTime) (dX : Fin 4 → SpaceTime →L[ℝ] ℝ)
    (dU : Fin 4 → Fin 4 → SpaceTime →L[ℝ] ℝ)
    (hX : ∀ α, HasFDerivAt (fun y => X y α) (dX α) x)
    (hU : ∀ μ ν, HasFDerivAt (fun y => U y μ ν) (dU μ ν) x) :
    lie_derivative X U x = fun μ ν =>
      (∑ α : Fin 4, X x α * dU μ ν (fun i => if i = α then 1 else 0)) +
      (∑ α : Fin 4, U x α ν * dX α (fun i => if i = μ then 1 else 0)) +
      (∑ α : Fin 4, U x μ α * dX α (fun i => if i = ν then 1 else 0)) := by
  ext μ ν
  simp only [lie_derivative, directional_transport, partial_deriv, (hX _).fderiv,
    (hU _ _).fderiv]

/-- Invariance under an arbitrary specified vector field. -/
def is_lie_invariant (U : MetricField) (X : VectorField) (x : SpaceTime) : Prop :=
  lie_derivative X U x = 0

/-- Translation invariance uses a *constant* generator, not an arbitrary vector field. -/
def is_translationally_symmetric (U : MetricField) (v : SpaceTime) (x : SpaceTime) : Prop :=
  lie_derivative (fun _ => v) U x = 0

@[simp] theorem partial_deriv_const (r : ℝ) (μ : Fin 4) (x : SpaceTime) :
    partial_deriv (fun _ => r) μ x = 0 := by
  simp [partial_deriv]

@[simp] theorem directional_transport_const (X : VectorField) (U : T2) (x : SpaceTime) :
    directional_transport X (fun _ => U) x = 0 := by
  ext μ ν
  simp [directional_transport]

/-- Eq. 92: the two index terms vanish for constant translation generators.
No differentiation rule for `U` is used, so this is also a totalized-operator identity. -/
theorem lie_derivative_translation (v : SpaceTime) (U : MetricField) (x : SpaceTime) :
    lie_derivative (fun _ => v) U x = directional_transport (fun _ => v) U x := by
  ext μ ν
  simp [lie_derivative]

/-- Constant tensors are invariant under constant translations. -/
theorem lie_derivative_const_translation (v : SpaceTime) (U : T2) (x : SpaceTime) :
    lie_derivative (fun _ => v) (fun _ => U) x = 0 := by
  rw [lie_derivative_translation, directional_transport_const]

/-- The dilation generator with a constant rate. -/
noncomputable def dilation_vector_field (σ : ℝ) : VectorField := fun x μ => σ * x μ

@[simp] theorem partial_deriv_dilation (σ : ℝ) (α μ : Fin 4) (x : SpaceTime) :
    partial_deriv (fun y => dilation_vector_field σ y α) μ x =
      if α = μ then σ else 0 := by
  unfold partial_deriv dilation_vector_field
  rw [((hasFDerivAt_apply α x).const_mul σ).fderiv]
  simp [smul_apply, ContinuousLinearMap.proj_apply, mul_ite]

/-- Eq. 99, including the two lower-index terms, for arbitrary tensor components.
The generator is differentiable by construction; a classical interpretation of
its transport term additionally requires differentiable tensor components. -/
theorem lie_derivative_dilation (σ : ℝ) (U : MetricField) (x : SpaceTime) :
    lie_derivative (dilation_vector_field σ) U x =
      directional_transport (dilation_vector_field σ) U x + (2 * σ) • U x := by
  ext μ ν
  simp [lie_derivative, mul_ite]
  ring

/-- A constant covariant rank-two tensor has dilation weight two. -/
theorem lie_derivative_const_dilation (σ : ℝ) (U : T2) (x : SpaceTime) :
    lie_derivative (dilation_vector_field σ) (fun _ => U) x = (2 * σ) • U := by
  rw [lie_derivative_dilation, directional_transport_const, zero_add]

/-- In particular, `X(x) = x` gives `L_X U = 2 U`, not zero. -/
theorem lie_derivative_const_identity (U : T2) (x : SpaceTime) :
    lie_derivative (fun y => y) (fun _ => U) x = (2 : ℝ) • U := by
  have hX : dilation_vector_field 1 = (fun y => y) := by
    funext y μ
    simp [dilation_vector_field]
  simpa only [hX, mul_one] using lie_derivative_const_dilation 1 U x

/-- A constant mixed-index matrix defines a linear vector field `Xᵅ = Bᵅᵦ xᵝ`. -/
noncomputable def linear_vector_field (B : T2) : VectorField :=
  fun x α => ∑ β : Fin 4, B α β * x β

@[simp] theorem partial_deriv_linear (B : T2) (α μ : Fin 4) (x : SpaceTime) :
    partial_deriv (fun y => linear_vector_field B y α) μ x = B α μ := by
  have h : HasFDerivAt (fun y : SpaceTime => ∑ β : Fin 4, B α β * y β)
      (∑ β : Fin 4, B α β •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) β)) x := by
    apply HasFDerivAt.fun_sum
    intro β _
    exact (hasFDerivAt_apply β x).const_mul (B α β)
  unfold partial_deriv linear_vector_field
  rw [h.fderiv]
  simp [sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, mul_ite]

/-- Eq. 93 for a fixed linear generator, without assuming tensor symmetry. -/
theorem lie_derivative_linear (B : T2) (U : MetricField) (x : SpaceTime) :
    lie_derivative (linear_vector_field B) U x = fun μ ν =>
      directional_transport (linear_vector_field B) U x μ ν +
      (∑ α : Fin 4, U x α ν * B α μ) + (∑ α : Fin 4, U x μ α * B α ν) := by
  ext μ ν
  simp only [lie_derivative, partial_deriv_linear]

/-- For a constant tensor the linear-generator residual is derived entirely
from its two lower-index terms: in matrix notation, `Bᵀ U + U B`. -/
theorem lie_derivative_const_linear (B U : T2) (x : SpaceTime) :
    lie_derivative (linear_vector_field B) (fun _ => U) x = fun μ ν =>
      (∑ α : Fin 4, U α ν * B α μ) + (∑ α : Fin 4, U μ α * B α ν) := by
  ext μ ν
  simp [lie_derivative_linear]

/-- A boost in the `(0,i)` plane with mixed entries `B⁰ᵢ = Bⁱ₀ = b`.
For `η = diag(-1,1,1,1)` the lowered paper parameter is `ω₀ᵢ = -b`. -/
noncomputable def boost_matrix (b : ℝ) (i : Fin 4) : T2 :=
  fun α β => (if α = 0 ∧ β = i then b else 0) +
    (if α = i ∧ β = 0 then b else 0)

noncomputable def boost_vector_field (b : ℝ) (i : Fin 4) : VectorField :=
  linear_vector_field (boost_matrix b i)

/-- The `(0,i)` boost residual for *any* constant covariant tensor. -/
theorem lie_derivative_const_boost_zero_spatial (b : ℝ) (i : Fin 4) (hi : i ≠ 0)
    (U : T2) (x : SpaceTime) :
    lie_derivative (boost_vector_field b i) (fun _ => U) x 0 i =
      b * (U i i + U 0 0) := by
  rw [boost_vector_field, lie_derivative_const_linear]
  simp [boost_matrix, hi, Ne.symm hi, mul_add, mul_ite]
  ring

/-- The constant diagonal symmetric tensor used for the restricted boost check. -/
noncomputable def isotropic_covariant_tensor (a : ℝ) : T2 :=
  Matrix.diagonal (fun μ : Fin 4 => if μ = 0 then -a^2 else 1 / a^2)

/-- This diagonal tensor is exactly the existing symmetric sector, for arbitrary
constant shear parameters. It does not assume a spacetime-varying field is constant. -/
theorem U_sym_eq_isotropic_covariant_tensor
    (a alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val : ℝ) :
    U_sym a alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val =
      isotropic_covariant_tensor a := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp [U_sym, symPart, U_hat, isotropic_covariant_tensor]

/-- Eqs. 95–96 in the constant isotropic chart: this residual is computed from
`lie_derivative`, rather than supplied as a hypothesis. No cancellation by `a`
or nonzero premise is used; the physical nonsingular domain is addressed by `a > 0`
in `lorentz_symmetry_broken`. -/
theorem lie_derivative_isotropic_boost (b : ℝ) (i : Fin 4) (hi : i ≠ 0)
    (a : ℝ) (x : SpaceTime) :
    lie_derivative (boost_vector_field b i) (fun _ => isotropic_covariant_tensor a) x 0 i =
      b * (1 / a^2 - a^2) := by
  rw [lie_derivative_const_boost_zero_spatial b i hi]
  simp [isotropic_covariant_tensor, hi, sub_eq_add_neg]

/-- With the paper's lowered `ω₀ᵢ`, the same residual has the printed minus sign. -/
theorem lie_derivative_isotropic_boost_lowered (omega_0i : ℝ) (i : Fin 4) (hi : i ≠ 0)
    (a : ℝ) (x : SpaceTime) :
    lie_derivative (boost_vector_field (-omega_0i) i)
      (fun _ => isotropic_covariant_tensor a) x 0 i =
      -omega_0i * (1 / a^2 - a^2) :=
  lie_derivative_isotropic_boost (-omega_0i) i hi a x

end AsymmetricTensor
