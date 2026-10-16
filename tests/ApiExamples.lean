import AsymmetricTensor

open AsymmetricTensor

-- Start with an arbitrary component matrix, not a physical-model assumption.
example (U : T2) : U = symPart U + antiPart U := matrix_decomposition U

-- A nonsymmetric off-diagonal example: U_01 = 2 and other components zero.
def sampleMatrix : T2 := fun i j => if i = 0 ∧ j = 1 then 2 else 0

example : symPart sampleMatrix 0 1 = 1 := by norm_num [symPart, sampleMatrix]
example : antiPart sampleMatrix 0 1 = 1 := by norm_num [antiPart, sampleMatrix]
example : antiPart sampleMatrix 1 0 = -1 := by norm_num [antiPart, sampleMatrix]
example : sampleMatrix = symPart sampleMatrix + antiPart sampleMatrix :=
  matrix_decomposition sampleMatrix

-- Independently, the repaired field constraint admits every constant matrix.
example : CoordinateConserved (fun _ => sampleMatrix) :=
  constant_coordinate_conserved sampleMatrix

-- Both lower-index terms matter even for a constant covariant tensor.
example (x : SpaceTime) :
    lie_derivative (fun y => y) (fun _ => sampleMatrix) x = (2 : ℝ) • sampleMatrix :=
  lie_derivative_const_identity sampleMatrix x

-- Choose the contraction explicitly: the same electric component has opposite signs.
example : frobenius_contract (electricBivector 1) (electricBivector 1) = 2 := by
  norm_num [frobenius_contract, tensor_contract, electricBivector]
example : lorentzian_action_density (electricBivector 1) = -2 := by
  norm_num [lorentzian_action_density, electric_lorentzian_contraction]

-- The base-10 normalization and finite-path inequality are distinct API facts.
example : 5 * decimalLog 10 = 5 := tenfold_distance_magnitude_anomaly
example (L r : ℝ) (hL : 0 < L) (hr : 0 < r) : r < optical_distance L r :=
  optical_distance_gt L r hL hr
example (L r : ℝ) (hL : 0 < L) (hr : 0 < r) :
    0 < 5 * decimalLog (optical_distance L r / r) :=
  optical_magnitude_anomaly_pos L r hL hr

-- The manuscript baseline uses no extra coupling factor on F_fund.
example (m α a₀ : ℝ) (hm : m ≠ 0) (hα : α ≠ 0)
    (ha₀ : a₀ = hbar / (α * m * c)) :
    F_fund a₀ = (α^2 * m^2 * c^3) / hbar :=
  interaction_hierarchy_em m α a₀ hm hα ha₀

#print axioms matrix_decomposition
#print axioms constant_coordinate_conserved
#print axioms lie_derivative_const_identity
#print axioms electric_lorentzian_contraction
#print axioms tenfold_distance_magnitude_anomaly
#print axioms optical_distance_gt
#print axioms optical_magnitude_anomaly_pos
#print axioms interaction_hierarchy_em
