import AsymmetricTensor

/-! Focused regressions for issue #11. Run with `lake env lean tests/LieDerivative.lean`. -/

open AsymmetricTensor
open BigOperators

namespace LieDerivativeRegression

-- Arbitrary constant tensors, including nonsymmetric ones, carry two covariant indices.
example (U : T2) (x : SpaceTime) :
    lie_derivative (fun y => y) (fun _ => U) x = (2 : ℝ) • U :=
  lie_derivative_const_identity U x

-- The original counterexample: dilation of constant Minkowski components is nonzero.
example (x : SpaceTime) :
    lie_derivative (fun y => y) (fun _ => isotropic_covariant_tensor 1) x 0 0 = -2 := by
  rw [lie_derivative_const_identity]
  norm_num [isotropic_covariant_tensor]

-- Directional transport still returns zero on constants, so it cannot replace the full operator.
example (x : SpaceTime) :
    directional_transport (fun y => y) (fun _ => isotropic_covariant_tensor 1) x = 0 :=
  directional_transport_const _ _ _

example (v : SpaceTime) (U : MetricField) (x : SpaceTime) :
    lie_derivative (fun _ => v) U x = directional_transport (fun _ => v) U x :=
  lie_derivative_translation v U x

example (v : SpaceTime) (U : T2) (x : SpaceTime) :
    lie_derivative (fun _ => v) (fun _ => U) x = 0 :=
  lie_derivative_const_translation v U x

-- A varying tensor verifies that the retained transport term has not been dropped.
example (x : SpaceTime) :
    lie_derivative (fun _ => (fun _ => (1 : ℝ)))
      (fun y => Matrix.of (fun _ _ => y 0)) x 0 0 = 1 := by
  rw [lie_derivative_translation]
  simp [directional_transport, partial_deriv, (hasFDerivAt_apply 0 x).fderiv,
    ContinuousLinearMap.proj_apply]

-- A nonconstant tensor combines transport with the two index terms under dilation.
example (σ : ℝ) (x : SpaceTime) :
    lie_derivative (dilation_vector_field σ)
      (fun y => Matrix.of (fun _ _ => y 0)) x 0 0 = 3 * σ * x 0 := by
  rw [lie_derivative_dilation]
  simp [directional_transport, partial_deriv, (hasFDerivAt_apply 0 x).fderiv,
    ContinuousLinearMap.proj_apply, dilation_vector_field]
  ring

-- This tests both lower indices on a nonsymmetric constant tensor and a general matrix.
example (B U : T2) (x : SpaceTime) :
    lie_derivative (linear_vector_field B) (fun _ => U) x = fun μ ν =>
      (∑ α : Fin 4, U α ν * B α μ) + (∑ α : Fin 4, U μ α * B α ν) :=
  lie_derivative_const_linear B U x

-- All three spatial boost directions are covered by the generic theorem.
example (i : Fin 4) (hi : i ≠ 0) (x : SpaceTime) :
    lie_derivative (boost_vector_field 1 i)
      (fun _ => isotropic_covariant_tensor 2) x 0 i = -(15 / 4 : ℝ) := by
  rw [lie_derivative_isotropic_boost 1 i hi]
  norm_num

-- The paper uses a lowered boost parameter, reversing the mixed-entry sign.
example (x : SpaceTime) :
    lie_derivative (boost_vector_field (-1) 1)
      (fun _ => isotropic_covariant_tensor 2) x 0 1 = (15 / 4 : ℝ) := by
  rw [lie_derivative_isotropic_boost_lowered 1 1 (by decide)]
  norm_num

-- Flat Minkowski components are invariant under this entire boost, not just its 01 component.
example (b : ℝ) (x : SpaceTime) :
    lie_derivative (boost_vector_field b 1)
      (fun _ => isotropic_covariant_tensor 1) x = 0 := by
  rw [boost_vector_field, lie_derivative_const_linear]
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    norm_num [boost_matrix, isotropic_covariant_tensor, Fin.sum_univ_succ]

-- The symmetry theorem now takes actual invariance rather than assuming the residual equation.
example (a b : ℝ) (ha : 0 < a) (hb : b ≠ 0) (i : Fin 4) (hi : i ≠ 0)
    (x : SpaceTime)
    (h : lie_derivative (boost_vector_field b i)
      (fun _ => isotropic_covariant_tensor a) x = 0) : a = 1 :=
  lorentz_symmetry_broken a b hb ha i hi x h

#print axioms lie_derivative_eq_of_hasFDerivAt
#print axioms lie_derivative_translation
#print axioms lie_derivative_dilation
#print axioms lie_derivative_const_identity
#print axioms lie_derivative_const_linear
#print axioms U_sym_eq_isotropic_covariant_tensor
#print axioms lie_derivative_isotropic_boost
#print axioms lorentz_symmetry_broken

end LieDerivativeRegression
