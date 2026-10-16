/-
Copyright (c) 2026 Binyamin Tsadik Bair-Mosheh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Binyamin Tsadik Bair-Mosheh
-/
module

public import AsymmetricTensor.MatrixAlgebra
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Admissible scalar domain and one-sided saturation limits

The raw `U_hat` is a totalized algebraic formula. `admissibleTensor` restricts its
scalar admittance to `(0, 1]`. This does not assert invertibility under arbitrary
antisymmetric loads. The author's discrete zero-division convention is separate from these
continuum limits; no transition law is derived here. See `docs/saturation-limits.md`.
-/

@[expose] public section

open Real Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedSectionVars true

namespace AsymmetricTensor

/-- Positive scalar admittance with nonnegative normalized pressure. Zero is excluded. -/
abbrev AdmissibleAdmittance := {a : ℝ // 0 < a ∧ a ≤ 1}

/-- Positive capacity and nonnegative total applied pressure strictly below that capacity. -/
def SubcriticalPressure (capacity pressure : ℝ) : Prop :=
  0 < capacity ∧ 0 ≤ pressure ∧ pressure < capacity

/-- Square-root pressure parametrization. Only its subcritical restriction is admissible. -/
noncomputable def pressureAdmittance (capacity pressure : ℝ) : ℝ :=
  Real.sqrt (1 - pressure / capacity)

/-- Subcritical pressure makes the inverse denominator and square-root/log argument positive. -/
theorem subcritical_gap_bounds {capacity pressure : ℝ}
    (h : SubcriticalPressure capacity pressure) :
    0 < 1 - pressure / capacity ∧ 1 - pressure / capacity ≤ 1 := by
  exact ⟨sub_pos.mpr ((div_lt_one h.1).mpr h.2.2),
    sub_le_self _ (div_nonneg h.2.1 h.1.le)⟩

/-- The positive square-root branch lies in `(0, 1]` on the subcritical domain. -/
theorem pressure_admittance_bounds {capacity pressure : ℝ}
    (h : SubcriticalPressure capacity pressure) :
    0 < pressureAdmittance capacity pressure ∧ pressureAdmittance capacity pressure ≤ 1 := by
  have hg := subcritical_gap_bounds h
  exact ⟨Real.sqrt_pos.mpr hg.1, Real.sqrt_le_one.mpr hg.2⟩

/-- Squaring the admissible pressure parametrization recovers the positive capacity gap. -/
theorem pressure_admittance_sq {capacity pressure : ℝ}
    (h : SubcriticalPressure capacity pressure) :
    pressureAdmittance capacity pressure ^ 2 = 1 - pressure / capacity := by
  exact Real.sq_sqrt (subcritical_gap_bounds h).1.le

/-- The inverse spatial coefficient agrees with the pressure expression on its valid domain. -/
theorem pressure_admittance_inverse_sq {capacity pressure : ℝ}
    (h : SubcriticalPressure capacity pressure) :
    1 / pressureAdmittance capacity pressure ^ 2 = 1 / (1 - pressure / capacity) := by
  rw [pressure_admittance_sq h]

/-- The logarithm is used at a positive argument, so its exponential recovers that argument. -/
theorem pressure_admittance_exp_log {capacity pressure : ℝ}
    (h : SubcriticalPressure capacity pressure) :
    Real.exp (Real.log (pressureAdmittance capacity pressure)) =
      pressureAdmittance capacity pressure := by
  exact Real.exp_log (pressure_admittance_bounds h).1

/-- Bundled pressure-derived admittance; the hypotheses are enforced by the subtype. -/
noncomputable def subcriticalAdmittance (capacity pressure : ℝ)
    (h : SubcriticalPressure capacity pressure) : AdmissibleAdmittance :=
  ⟨pressureAdmittance capacity pressure, pressure_admittance_bounds h⟩

/-- The original component formula restricted to admissible scalar inputs.
Arbitrary off-diagonal loads can still make this matrix singular. -/
noncomputable def admissibleTensor (a : AdmissibleAdmittance)
    (alpha vx vy vz ox oy oz tp : ℝ) : T2 :=
  U_hat a.val alpha vx vy vz ox oy oz tp

/-- Scalar admissibility gives negative temporal and positive spatial diagonal entries. -/
theorem admissible_tensor_diagonal_signs (a : AdmissibleAdmittance)
    (alpha vx vy vz ox oy oz tp : ℝ) :
    admissibleTensor a alpha vx vy vz ox oy oz tp 0 0 < 0 ∧
      0 < admissibleTensor a alpha vx vy vz ox oy oz tp 1 1 := by
  simp only [admissibleTensor, U_hat, Matrix.of_apply]
  norm_num
  exact pow_pos a.property.1 2

/-- The restricted component family is continuous in scalar admittance for fixed loads. -/
theorem continuous_admissible_tensor (alpha vx vy vz ox oy oz tp : ℝ) :
    Continuous (fun a : AdmissibleAdmittance => admissibleTensor a alpha vx vy vz ox oy oz tp) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hinv : Continuous (fun a : AdmissibleAdmittance => 1 / a.val ^ 2) :=
    continuous_const.div (continuous_subtype_val.pow 2)
      (fun a => pow_ne_zero 2 (ne_of_gt a.property.1))
  fin_cases i <;> fin_cases j <;>
    simp only [admissibleTensor, U_hat, Matrix.of_apply] <;>
    norm_num <;> first | simpa only [one_div] using hinv | fun_prop

/-- The spatial coefficient diverges as positive admittance tends to zero. -/
theorem inverse_sq_tendsto_at_top :
    Tendsto (fun a : ℝ => 1 / a ^ 2) (𝓝[>] 0) atTop := by
  simpa only [one_div, inv_pow] using
    (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).atTop_pow₀ (by norm_num : (2 : ℕ) ≠ 0)

/-- The same divergence holds entirely inside the admissible scalar domain `(0, 1]`. -/
theorem admissible_inverse_sq_tendsto_at_top :
    Tendsto (fun a : ℝ => 1 / a ^ 2) (𝓝[Ioc 0 1] 0) atTop := by
  rw [nhdsWithin_Ioc_eq_nhdsGT (by norm_num : (0 : ℝ) < 1)]
  exact inverse_sq_tendsto_at_top

/-- At positive capacity the remaining pressure fraction approaches zero from above. -/
theorem pressure_gap_tendsto_zero_right (capacity : ℝ) (hc : 0 < capacity) :
    Tendsto (fun p : ℝ => 1 - p / capacity) (𝓝[Ico 0 capacity] capacity) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hcont : Continuous (fun p : ℝ => 1 - p / capacity) := by fun_prop
    have hlim : Tendsto (fun p : ℝ => 1 - p / capacity) (𝓝 capacity) (𝓝 0) := by
      simpa [ne_of_gt hc] using hcont.tendsto capacity
    exact hlim.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with p hp
    exact sub_pos.mpr ((div_lt_one hc).mpr hp.2)

/-- The spatial pressure coefficient diverges on nonnegative, strictly subcritical pressures. -/
theorem subcritical_pressure_tendsto_at_top (capacity : ℝ) (hc : 0 < capacity) :
    Tendsto (fun p : ℝ => 1 / (1 - p / capacity))
      (𝓝[Ico 0 capacity] capacity) atTop := by
  simpa only [one_div, Function.comp_def] using
    tendsto_inv_nhdsGT_zero.comp (pressure_gap_tendsto_zero_right capacity hc)

/-- The actual square-root parametrized spatial coefficient diverges on subcritical pressures. -/
theorem pressure_admittance_inverse_sq_tendsto_at_top (capacity : ℝ) (hc : 0 < capacity) :
    Tendsto (fun p : ℝ => 1 / pressureAdmittance capacity p ^ 2)
      (𝓝[Ico 0 capacity] capacity) atTop := by
  apply (subcritical_pressure_tendsto_at_top capacity hc).congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (pressure_admittance_inverse_sq ⟨hc, hp⟩).symm

/-- A finite real value cannot be the one-sided limit of the spatial coefficient. -/
theorem inverse_sq_has_no_finite_limit (value : ℝ) :
    ¬ Tendsto (fun a : ℝ => 1 / a ^ 2) (𝓝[>] 0) (𝓝 value) :=
  not_tendsto_nhds_of_tendsto_atTop inverse_sq_tendsto_at_top value

/-- The actual `U_hat` spatial diagonal has this divergent limit, independently of fixed loads. -/
theorem tensor_spatial_diagonal_tendsto_at_top (alpha vx vy vz ox oy oz tp : ℝ) :
    Tendsto (fun a : ℝ => U_hat a alpha vx vy vz ox oy oz tp 1 1)
      (𝓝[>] 0) atTop := by
  simpa [U_hat] using inverse_sq_tendsto_at_top

/-- No finite matrix is the raw one-sided limit, since its spatial diagonal diverges. -/
theorem tensor_has_no_finite_limit (alpha vx vy vz ox oy oz tp : ℝ) (value : T2) :
    ¬ Tendsto (fun a : ℝ => U_hat a alpha vx vy vz ox oy oz tp) (𝓝[>] 0) (𝓝 value) := by
  intro h
  have h11 := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h 1) 1
  exact inverse_sq_has_no_finite_limit (value 1 1) (by simpa [U_hat] using h11)

/-- The reciprocal of the spatial coefficient gives a bounded scalar observable.
This algebra does not identify it with a nonlinear tensor strain or a post-yield metric. -/
theorem inverse_derived_scalar_strain (a : ℝ) :
    (1 - 1 / (1 / a ^ 2)) / 2 = (1 - a ^ 2) / 2 := by
  simp

/-- A bounded inverse-derived scalar can tend to `1/2` while raw spatial coefficients diverge. -/
theorem inverse_derived_scalar_strain_tendsto :
    Tendsto (fun a : ℝ => (1 - a ^ 2) / 2) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have hcont : Continuous (fun a : ℝ => (1 - a ^ 2) / 2) := by fun_prop
  simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds

/-- Multiplication by `a²` changes the divergent spatial diagonal into a unit punctured limit.
This is an explicit normalization, not the raw component or a post-yield phase definition. -/
theorem normalized_spatial_diagonal_tendsto_one :
    Tendsto (fun a : ℝ => a ^ 2 * (1 / a ^ 2)) (𝓝[>] 0) (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  field_simp [ne_of_gt ha]

/-- The normalized temporal coefficient tends to zero. -/
theorem normalized_temporal_diagonal_tendsto_zero :
    Tendsto (fun a : ℝ => a ^ 2 * (-a ^ 2)) (𝓝[>] 0) (𝓝 0) := by
  have hcont : Continuous (fun a : ℝ => a ^ 2 * (-a ^ 2)) := by fun_prop
  simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds

/-- For fixed loads, the explicitly normalized family has a finite punctured matrix limit.
This does not define a physical boundary value or a post-yield matching law. -/
theorem normalized_tensor_tendsto (alpha vx vy vz ox oy oz tp : ℝ) :
    Tendsto (fun a : ℝ => a ^ 2 • U_hat a alpha vx vy vz ox oy oz tp)
      (𝓝[>] 0) (𝓝 (Matrix.diagonal (fun i : Fin 4 => if i = 0 then 0 else 1))) := by
  have hscaled (k : ℝ) : Tendsto (fun a : ℝ => a ^ 2 * k) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun a : ℝ => a ^ 2 * k) := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, smul_eq_mul, U_hat, Matrix.of_apply, Matrix.diagonal] <;>
    norm_num <;> first
    | simpa only [one_div] using normalized_spatial_diagonal_tendsto_one
    | simpa only [mul_neg] using normalized_temporal_diagonal_tendsto_zero
    | exact hscaled _
    | simpa only [neg_zero] using (hscaled _).neg

/-- The exact value of the totalized normalized matrix at zero is still zero,
so it must not be confused with the punctured normalized limit. -/
theorem normalized_tensor_at_zero (alpha vx vy vz ox oy oz tp : ℝ) :
    (0 : ℝ) ^ 2 • U_hat 0 alpha vx vy vz ox oy oz tp = 0 := by
  simp

/-- At exactly zero admittance and zero loads, the totalized formula is the zero matrix.
It is not a finite limit of the admissible component family. -/
theorem unloaded_tensor_at_zero (alpha tp : ℝ) :
    U_hat 0 alpha 0 0 0 0 0 0 tp = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [U_hat]

/-- In the aligned transverse specialization, the totalized boundary matrix has a zero last row.
Thus its determinant vanishes for every slip and rotation, including nonzero rotation. -/
theorem aligned_boundary_determinant (alpha vx vy oz tp : ℝ) :
    Matrix.det (U_hat 0 alpha vx vy 0 0 0 oz tp) = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero 3
  intro j
  fin_cases j <;> simp [U_hat]

/-- Explicit nonzero-rotation boundary: actual determinant zero does not imply a spin lock. -/
theorem boundary_determinant_does_not_force_zero_rotation :
    Matrix.det (U_hat 0 1 0 0 0 0 0 1 1) = 0 ∧ (1 * 1 * 1 : ℝ) ^ 2 ≠ 0 := by
  exact ⟨aligned_boundary_determinant 1 0 0 1 1, by norm_num⟩

/-- Denominator clearing is an equivalence only with nonzero scalar admittance.
The left side is a scalar expression, not an unconditional determinant identity. -/
theorem cavitation_formula_iff_of_ne_zero (a electric magnetic : ℝ) (ha : a ≠ 0) :
    (-(1 / a ^ 4) - magnetic ^ 2 + (1 / a ^ 4) * electric ^ 2 = 0) ↔
      electric ^ 2 - a ^ 4 * magnetic ^ 2 = 1 := by
  have ha4 : a ^ 4 ≠ 0 := pow_ne_zero 4 ha
  constructor <;> intro h
  · field_simp at h
    nlinarith [h]
  · field_simp
    nlinarith [h]

/-- At zero, the totalized rational expression and the denominator-cleared equation disagree. -/
theorem cavitation_formula_not_equivalent_at_zero :
    (-(1 / (0 : ℝ) ^ 4) - 0 ^ 2 + (1 / (0 : ℝ) ^ 4) * 0 ^ 2 = 0) ∧
      ¬ ((0 : ℝ) ^ 2 - 0 ^ 4 * 0 ^ 2 = 1) := by
  norm_num

/-- The rational expression at zero disagrees with the actual aligned boundary determinant. -/
theorem totalized_formula_not_boundary_determinant :
    Matrix.det (U_hat 0 1 0 0 0 0 0 1 1) ≠
      -(1 / (0 : ℝ) ^ 4) - (1 * 1 * 1) ^ 2 + (1 / (0 : ℝ) ^ 4) * 0 ^ 2 := by
  rw [aligned_boundary_determinant]
  norm_num

end AsymmetricTensor
