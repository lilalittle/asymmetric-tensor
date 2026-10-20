import AsymmetricTensor
import ProofAudit

/-! Regression migration for the v4.5 field APIs. These checks do not reinstate
v2's removed admissible-field API or strengthen the physical postulate. -/

open AsymmetricTensor BigOperators

namespace V45FieldRegression

-- The inventory alone would accept a stronger axiom under an unchanged name.
-- v5.0 replaces six axioms with three definitions and three positivity theorems.
-- Pin their kinds and signatures; the remaining postulate is checked below.
open Lean Elab Command in
run_cmd do
  let checkFoundation (decl : Name) (isTheorem : Bool)
      (expectedSyntax : TSyntax `term) : CommandElabM Unit := do
    let info ← getConstInfo decl
    let correctKind := match info with
      | .thmInfo _ => isTheorem
      | .defnInfo _ => !isTheorem
      | _ => false
    unless correctKind do
      throwError "FOUNDATIONAL_KIND: {decl} has the wrong declaration kind"
    liftTermElabM do
      let expected ← Term.elabType expectedSyntax
      unless ← Meta.isDefEq info.type expected do
        throwError "FOUNDATIONAL_TYPE: {decl} no longer has its reviewed signature"
  checkFoundation `AsymmetricTensor.c false (← `(ℝ))
  checkFoundation `AsymmetricTensor.l_p false (← `(ℝ))
  checkFoundation `AsymmetricTensor.hbar false (← `(ℝ))
  checkFoundation `AsymmetricTensor.c_pos true (← `(0 < AsymmetricTensor.c))
  checkFoundation `AsymmetricTensor.l_p_pos true (← `(0 < AsymmetricTensor.l_p))
  checkFoundation `AsymmetricTensor.hbar_pos true (← `(0 < AsymmetricTensor.hbar))
  logInfo "FOUNDATIONAL_TYPES_OK: three real definitions and three positivity theorems"

-- Compare the declaration type itself, so even an implicit general-field binder
-- cannot silently broaden this postulate while the examples keep compiling.
open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `AsymmetricTensor.covariant_conservation
  unless info matches .axiomInfo _ do
    throwError "CONSERVATION_SCOPE: expected the reviewed physical postulate"
  liftTermElabM do
    let expected ← Term.elabType (← `(∀ x : SpaceTime,
      metric_divergence U_hat_dynamic x = 0))
    unless ← Meta.isDefEq info.type expected do
      throwError "CONSERVATION_SCOPE: postulate is no longer scoped to U_hat_dynamic"
  logInfo "CONSERVATION_SCOPE_OK: exactly U_hat_dynamic"

-- This ascription pins the postulate to U_hat_dynamic, not an arbitrary field.
example : ∀ x : SpaceTime, metric_divergence U_hat_dynamic x = 0 :=
  covariant_conservation

example (x : SpaceTime) : metric_divergence U_hat_dynamic x 0 = 0 :=
  bernoulli_energy_conservation x

example (x : SpaceTime) (i : Fin 4) (hi : i ≠ 0) :
    metric_divergence U_hat_dynamic x i = 0 :=
  navier_stokes_momentum_conservation x i hi

-- Generic coordinate calculus remains independent of the physical postulate.
theorem constant_partial (r : ℝ) (μ : Fin 4) (x : SpaceTime) :
    partial_deriv (fun _ => r) μ x = 0 := by
  simp [partial_deriv]

theorem coordinate_partial (i μ : Fin 4) (x : SpaceTime) :
    partial_deriv (fun y => y i) μ x = if i = μ then 1 else 0 := by
  simp [partial_deriv, (hasFDerivAt_apply i x).fderiv,
    ContinuousLinearMap.proj_apply]

theorem constant_field_divergence (A : T2) (x : SpaceTime) :
    metric_divergence (fun _ => A) x = 0 := by
  ext ν
  simp [metric_divergence, constant_partial]

theorem coordinate_field_divergence (x : SpaceTime) (ν : Fin 4) :
    metric_divergence (fun y _ _ => y 0) x ν = 1 := by
  simp [metric_divergence, coordinate_partial]

-- The gradient-based replacement really constructs a nonzero exterior wedge.
theorem coordinate_clebsch_vorticity (x : SpaceTime) :
    Omega_clebsch_field (fun y => y 2) (fun y => y 1) x 2 1 = 1 := by
  simp [Omega_clebsch_field, omega_clebsch_2form, wedge_covec, d_scalar_field,
    coordinate_partial]

-- The old universal-field inconsistency must not be reintroduced.
theorem coordinate_field_not_divergence_free (x : SpaceTime) :
    ¬ is_divergence_free (fun y _ _ => y 0) x := by
  intro h
  have h0 := congrFun h 0
  rw [coordinate_field_divergence] at h0
  norm_num at h0

-- A constant nonsymmetric tensor still has both lower-index terms.
theorem constant_tensor_dilation (A : T2) (x : SpaceTime) :
    lie_derivative (fun y => y) (fun _ => A) x = (2 : ℝ) • A := by
  ext μ ν
  simp [lie_derivative, constant_partial, coordinate_partial, mul_ite,
    Finset.sum_add_distrib]
  ring

example (A : T2) (v x : SpaceTime) :
    lie_derivative (fun _ => v) (fun _ => A) x = 0 := by
  ext μ ν
  simp [lie_derivative, constant_partial]

-- Transport is not lost when the tensor varies.
example (x : SpaceTime) :
    lie_derivative (fun _ _ => (1 : ℝ)) (fun y _ _ => y 0) x 0 0 = 1 := by
  simp [lie_derivative, constant_partial, coordinate_partial]

-- Transport plus the two index terms under dilation gives 3*x_0.
example (x : SpaceTime) :
    lie_derivative (fun y => y) (fun y _ _ => y 0) x 0 0 = 3 * x 0 := by
  simp [lie_derivative, coordinate_partial, mul_ite, Finset.sum_add_distrib]
  ring

-- Off-diagonal linear flow isolates each covariant-index term independently.
theorem first_index_response (A : T2) (x : SpaceTime) :
    lie_derivative (fun y i => if i = 0 then y 1 else 0)
      (fun _ => A) x 1 2 = A 0 2 := by
  norm_num [lie_derivative, Fin.sum_univ_succ, constant_partial, coordinate_partial]

theorem second_index_response (A : T2) (x : SpaceTime) :
    lie_derivative (fun y i => if i = 0 then y 1 else 0)
      (fun _ => A) x 2 1 = A 2 0 := by
  norm_num [lie_derivative, Fin.sum_univ_succ, constant_partial, coordinate_partial]

-- Newly supplied field operator: all three spatial transport components appear.
example (f : ScalarField) (x : SpaceTime) :
    material_deriv f x = partial_deriv f 0 x +
      (v_x_f x * partial_deriv f 1 x + v_y_f x * partial_deriv f 2 x +
        v_z_f x * partial_deriv f 3 x) := rfl

-- A nontrivial continuity instance checks cancellation of density transport.
example : (7 : ℝ) + 11 + 13 + 21 = 2 * (3 + (5 * 1 + 7 * 1 + 11 * 1)) := by
  exact material_acceleration_from_continuity
    2 1 1 3 1 (-1) (-1) 5 7 11 1 1 1 7 11 13 21
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#audit_theorem V45FieldRegression.constant_partial custom []
#audit_theorem V45FieldRegression.coordinate_partial custom []
#audit_theorem V45FieldRegression.coordinate_clebsch_vorticity custom []
#audit_theorem V45FieldRegression.constant_field_divergence custom []
#audit_theorem V45FieldRegression.coordinate_field_divergence custom []
#audit_theorem V45FieldRegression.coordinate_field_not_divergence_free custom []
#audit_theorem V45FieldRegression.constant_tensor_dilation custom []
#audit_theorem V45FieldRegression.first_index_response custom []
#audit_theorem V45FieldRegression.second_index_response custom []
#audit_theorem AsymmetricTensor.material_acceleration_from_continuity custom []
#audit_theorem AsymmetricTensor.material_derivative_continuity_field_link custom []
#audit_theorem AsymmetricTensor.eulerian_momentum_pde_eq46 custom []

end V45FieldRegression

-- Audit this test module's retained declarations for completeness, too.
#audit_current_module declared []
