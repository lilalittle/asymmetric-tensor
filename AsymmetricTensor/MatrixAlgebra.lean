/-
Copyright (c) 2026 Binyamin Tsadik Bair-Mosheh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Binyamin Tsadik Bair-Mosheh
-/
module

public import AsymmetricTensor.Model

/-!
# Matrix decomposition, contractions, averaging, and the unified action

See `docs/modules.md` for the module map and compatibility policy.
The manuscript terminology and the mathematical statements are retained.
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
/--
Symmetric part (U + Uᵀ)/2 of any real component matrix. No invertibility or physical assumptions
are required.
-/
noncomputable def symPart (U : T2) : T2 :=
  fun i j => (U i j + U j i) / 2

/--
Antisymmetric part (U − Uᵀ)/2 of any real component matrix. This is algebraic projection, not a
volume average.
-/
noncomputable def antiPart (U : T2) : T2 :=
  fun i j => (U i j - U j i) / 2

-- Proof: 4x4 real matrix decomposition.
/--
Every real 4×4 matrix is the sum of its symmetric and antisymmetric parts. The proof is
pointwise ring algebra and uses no physical axioms.
-/
theorem matrix_decomposition (U : T2) :
    U = symPart U + antiPart U := by
  ext i j
  change U i j = (U i j + U j i) / 2 + (U i j - U j i) / 2
  ring

-- 3.2 The Bilinear Form Bridge
/--
Convert a component matrix to the bilinear form (x,y) ↦ ∑ᵢⱼ xᵢ Uᵢⱼ yⱼ, in the fixed standard
basis. No metric is inserted.
-/
noncomputable def asBilinear (U : T2) : LinearMap.BilinForm ℝ V4 :=
  Matrix.toBilin' U

-- 3.3 Concrete Tensor Contractions
-- A and V have two covariant (lower) indices. gInv supplies the contravariant
-- inverse metric; raiseBoth raises both indices of its second argument.
/--
Raise both component indices using the supplied matrix gInv: ∑αβ gInv μα gInv νβ A αβ. Callers
must establish that gInv is the intended inverse metric; this definition does not impose
symmetry or inverse laws.
-/
noncomputable def raiseBoth (gInv A : T2) : T2 :=
  fun μ ν => ∑ α : Fin 4, ∑ β : Fin 4, gInv μ α * gInv ν β * A α β

/--
Contract U with V after raising both indices of V with gInv. This is metric-dependent; with a
Lorentzian inverse metric it need not be nonnegative.
-/
noncomputable def contract2 (gInv U V : T2) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, U μ ν * raiseBoth gInv V μ ν

-- 3.4 Assembly of the Specific Asymmetric Metric-Tensor
-- Foundation tensor matrix.
/--
Assemble the manuscript-inspired component matrix in its fixed comoving chart. Inputs are scalar
admittance, velocity, rotation, and time-scale parameters. The formula is totalized at zero
denominators; physical use requires a separately justified admissible domain.
-/
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
/--
Symmetric algebraic projection of U_hat. In this fixed chart it is diagonal; this does not
construct a covariant tensor in arbitrary frames.
-/
noncomputable def U_sym (alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val : ℝ) : T2 :=
  symPart (U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val)

/--
Antisymmetric algebraic projection of U_hat, containing the off-diagonal velocity/rotation
terms. Antisymmetry alone does not imply finite volume preservation.
-/
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
/--
Specialization of matrix_decomposition to U_hat. It proves the algebraic split for all scalar
parameters, not an independent physical decomposition law.
-/
theorem tensor_decomposition_proven (alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val : ℝ) :
    U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val =
    U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val +
    U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val := by
  exact matrix_decomposition (U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val)

-- ==========================================
-- 4.3 The Macroscopic Reduction (The Einstein Field Equation)
-- ==========================================

-- The Volumetric Average operator acts as the symmetric spatial projection.
-- Bundled as a LinearMap over ℝ.
/--
The implemented linear map is symPart. Despite its historical name it is not integration,
expectation, or a general spatial coarse-graining operation.
-/
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

-- The volumetric average of the antisymmetric shear is 0.
lemma VolAvg_U_anti (alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val : ℝ) :
    VolAvg (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) = 0 := by
  ext i j
  dsimp [VolAvg, U_anti, symPart, antiPart]
  ring

-- The incompatibility operator.
variable (Inc : T2 →ₗ[ℝ] T2)

theorem macroscopic_torsion_nullification (alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val : ℝ)
    (h_commute : ∀ (A : T2), Inc (VolAvg A) = VolAvg (Inc A)) :
    VolAvg (Inc (U_hat alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val)) =
    VolAvg (Inc (U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val)) := by
  have h_decomp := tensor_decomposition_proven alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val
  rw [h_decomp]

  have h2 : Inc (U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val +
                 U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) =
            Inc (U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) +
            Inc (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) := map_add Inc _ _
  rw [h2]

  have h3 : VolAvg (Inc (U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) +
                    Inc (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val)) =
            VolAvg (Inc (U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val)) +
            VolAvg (Inc (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val)) := map_add VolAvg _ _
  rw [h3]

  have h4 : VolAvg (Inc (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val)) =
            Inc (VolAvg (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val)) := by
    exact (h_commute (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val)).symm
  rw [h4]

  have h5 : VolAvg (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) = 0 := by
    exact VolAvg_U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val
  rw [h5]

  have h6 : Inc (0 : T2) = 0 := map_zero Inc
  rw [h6, add_zero]

-- ==========================================
-- SECTION 6: Unified Action & Singularity Resolution
-- ==========================================

-- ==========================================
-- 6.1 Unified Action
-- ==========================================
-- Legacy algebraic contraction: the Euclidean/Frobenius component product.
-- It does not raise either index and is not the Lorentzian action scalar.
-- The explicit frobenius_* names below preserve this valid algebra; the physical
-- convention is implemented separately by lorentzian_action_density.
/-- Legacy Frobenius component pairing ∑ᵢⱼ Aᵢⱼ Bᵢⱼ; `frobenius_contract` is its explicit alias.
Use `contract2` with an explicit inverse metric for raised-index contraction, or
`lorentzian_action_density` for the fixed background-Minkowski quadratic scalar. -/
noncomputable def tensor_contract (A B : T2) : ℝ :=
  (A 0 0 * B 0 0) + (A 0 1 * B 0 1) + (A 0 2 * B 0 2) + (A 0 3 * B 0 3) +
  (A 1 0 * B 1 0) + (A 1 1 * B 1 1) + (A 1 2 * B 1 2) + (A 1 3 * B 1 3) +
  (A 2 0 * B 2 0) + (A 2 1 * B 2 1) + (A 2 2 * B 2 2) + (A 2 3 * B 2 3) +
  (A 3 0 * B 3 0) + (A 3 1 * B 3 1) + (A 3 2 * B 3 2) + (A 3 3 * B 3 3)

-- Legacy Frobenius orthogonality for the concrete component matrix.
theorem contract_sym_anti_proven (alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val : ℝ) :
    tensor_contract
      (U_sym alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val)
      (U_anti alpha_s alpha v_x v_y v_z Omega_x Omega_y Omega_z t_p_val) = 0 := by
  dsimp [tensor_contract, U_sym, U_anti, symPart, antiPart, U_hat, Matrix.of_apply]
  simp

-- Legacy Frobenius decomposition. This historical API name is retained for
-- compatibility; use lorentzian_action_separation for the manuscript contraction.
/-- Legacy Frobenius quadratic separation of the symmetric and antisymmetric projections.
Use `frobenius_action_separation` for the same algebra with an explicit name, or
`lorentzian_action_separation` for the manuscript background-Minkowski contraction. -/
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


/-- Explicit name for the legacy Euclidean/Frobenius component product. -/
noncomputable abbrev frobenius_contract (A B : T2) : ℝ := tensor_contract A B

-- Accurate aliases preserve all legacy theorem types.
alias frobenius_sym_anti_orthogonality := contract_sym_anti_proven
alias frobenius_action_separation := unified_action_separation

-- 6.1.1 Background-Minkowski contraction: η = η⁻¹ = diag(-1,1,1,1).
-- This is the g of manuscript p. 3 and the convention of Eqs. (121), (123).

noncomputable def minkowskiSign (μ : Fin 4) : ℝ := if μ = 0 then -1 else 1

/-- Background inverse Minkowski metric `diag(-1,1,1,1)`. Its inverse law is
proved by `minkowskiInv_sq`; it is distinct from the inverse of the parameterized `U_sym`. -/
noncomputable def minkowskiInv : T2 := fun μ ν => if μ = ν then minkowskiSign μ else 0

lemma raiseBoth_minkowskiInv (A : T2) (μ ν : Fin 4) :
    raiseBoth minkowskiInv A μ ν = minkowskiSign μ * minkowskiSign ν * A μ ν := by
  simp [raiseBoth, minkowskiInv]

lemma contract2_minkowskiInv_components (A B : T2) :
    contract2 minkowskiInv A B =
      A 0 0 * B 0 0 - A 0 1 * B 0 1 - A 0 2 * B 0 2 - A 0 3 * B 0 3 -
      A 1 0 * B 1 0 + A 1 1 * B 1 1 + A 1 2 * B 1 2 + A 1 3 * B 1 3 -
      A 2 0 * B 2 0 + A 2 1 * B 2 1 + A 2 2 * B 2 2 + A 2 3 * B 2 3 -
      A 3 0 * B 3 0 + A 3 1 * B 3 1 + A 3 2 * B 3 2 + A 3 3 * B 3 3 := by
  simp [contract2, raiseBoth_minkowskiInv, minkowskiSign, Fin.sum_univ_succ]
  ring

/-- Orthogonality of arbitrary symmetric and antisymmetric parts using the
same two-index Minkowski contraction as the action. No U_hat ansatz is needed. -/

lemma lorentzian_sym_anti_orthogonality (U V : T2) :
    contract2 minkowskiInv (symPart U) (antiPart V) = 0 := by
  rw [contract2_minkowskiInv_components]
  dsimp [symPart, antiPart]
  ring

/-- Quadratic separation for an arbitrary component matrix under the fixed
Minkowski two-index contraction. This finite matrix identity does not vary or integrate
an action. -/
lemma lorentzian_matrix_action_separation (U : T2) :
    contract2 minkowskiInv U U =
      contract2 minkowskiInv (symPart U) (symPart U) +
      contract2 minkowskiInv (antiPart U) (antiPart U) := by
  simp only [contract2_minkowskiInv_components]
  dsimp [symPart, antiPart]
  ring

/-- Exact coordinate identity. At zero admittance Lean totalizes division;
this identity by itself does not describe a finite physical saturation limit. -/

lemma symmetric_action_components (alpha_s alpha vx vy vz Ox Oy Oz tp : ℝ) :
    contract2 minkowskiInv (U_sym alpha_s alpha vx vy vz Ox Oy Oz tp)
      (U_sym alpha_s alpha vx vy vz Ox Oy Oz tp) = alpha_s^4 + 3 / alpha_s^4 := by
  rw [contract2_minkowskiInv_components]
  simp [U_sym, U_hat, symPart, Matrix.of_apply]
  ring

/-- Manuscript Eq. (121), on the physical nonzero-admittance domain.
The component identity is algebraically totalized in symmetric_action_components. -/

lemma symmetric_action_eq121 (alpha_s alpha vx vy vz Ox Oy Oz tp : ℝ)
    (_has : alpha_s ≠ 0) :
    contract2 minkowskiInv (U_sym alpha_s alpha vx vy vz Ox Oy Oz tp)
      (U_sym alpha_s alpha vx vy vz Ox Oy Oz tp) = alpha_s^4 + 3 / alpha_s^4 := by
  exact symmetric_action_components alpha_s alpha vx vy vz Ox Oy Oz tp

lemma antisymmetric_action_components (alpha_s alpha vx vy vz Ox Oy Oz tp : ℝ) :
    contract2 minkowskiInv (U_anti alpha_s alpha vx vy vz Ox Oy Oz tp)
      (U_anti alpha_s alpha vx vy vz Ox Oy Oz tp) =
      -2 * alpha^2 * (vx^2 + vy^2 + vz^2) / c^2 +
      2 * alpha^2 * tp^2 * (Ox^2 + Oy^2 + Oz^2) := by
  rw [contract2_minkowskiInv_components]
  simp [U_anti, U_hat, antiPart, Matrix.of_apply]
  ring

-- 6.1.2 Explicit comoving frame already encoded by U_hat.
-- These are LOWER-index covectors: u_0 = -1, while u^0 = 1.
-- v_0 = 0 and ω_0ν = 0 make the required spatial orthogonality explicit.

noncomputable def restCovector : V4 := ![-1, 0, 0, 0]

noncomputable def restSpatialMetric : T2 := !![0,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1]

noncomputable def spatialSlipCovector (vx vy vz : ℝ) : V4 := ![0, vx, vy, vz]

noncomputable def spatialVorticity (Ox Oy Oz : ℝ) : T2 :=
  !![0,0,0,0; 0,0,-Oz,Oy; 0,Oz,0,-Ox; 0,-Oy,Ox,0]

noncomputable def minkowskiPair (u v : V4) : ℝ :=
  ∑ μ : Fin 4, minkowskiSign μ * u μ * v μ

/-- The manuscript's normalization and orthogonality constraints are proved
for the selected frame, rather than added as scientific axioms. -/

lemma rest_frame_constraints (vx vy vz Ox Oy Oz : ℝ) :
    minkowskiPair restCovector restCovector = -1 ∧
    minkowskiPair restCovector (spatialSlipCovector vx vy vz) = 0 ∧
    (∀ ν, ∑ μ : Fin 4, minkowskiSign μ * restCovector μ * restSpatialMetric μ ν = 0) ∧
    (∀ ν, ∑ μ : Fin 4, minkowskiSign μ * restCovector μ * spatialVorticity Ox Oy Oz μ ν = 0) := by
  norm_num [minkowskiPair, restCovector, spatialSlipCovector, minkowskiSign,
    restSpatialMetric, spatialVorticity, Fin.sum_univ_succ]
  intro ν
  fin_cases ν <;> rfl

lemma rest_symmetric_covariant_form (as a vx vy vz Ox Oy Oz tp : ℝ) :
    U_sym as a vx vy vz Ox Oy Oz tp = fun μ ν =>
      -as^2 * restCovector μ * restCovector ν + 1 / as^2 * restSpatialMetric μ ν := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp [U_sym, U_hat, symPart, restCovector, restSpatialMetric, Matrix.of_apply]

lemma rest_antisymmetric_covariant_form (as a vx vy vz Ox Oy Oz tp : ℝ) :
    U_anti as a vx vy vz Ox Oy Oz tp = fun μ ν =>
      a / c * (restCovector μ * spatialSlipCovector vx vy vz ν -
        restCovector ν * spatialSlipCovector vx vy vz μ) + a * tp * spatialVorticity Ox Oy Oz μ ν := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp [U_anti, U_hat, antiPart, restCovector, spatialSlipCovector, spatialVorticity, Matrix.of_apply] <;> ring

lemma spatial_vorticity_contraction (Ox Oy Oz : ℝ) :
    contract2 minkowskiInv (spatialVorticity Ox Oy Oz) (spatialVorticity Ox Oy Oz) =
      2 * (Ox^2 + Oy^2 + Oz^2) := by
  rw [contract2_minkowskiInv_components]
  simp [spatialVorticity]
  ring

lemma spatial_slip_norm (vx vy vz : ℝ) :
    minkowskiPair (spatialSlipCovector vx vy vz) (spatialSlipCovector vx vy vz) =
      vx^2 + vy^2 + vz^2 := by
  simp [minkowskiPair, minkowskiSign, spatialSlipCovector, Fin.sum_univ_succ]
  ring

/-- Manuscript Eq. (123) for U_hat's explicit comoving frame.
spatial_slip_norm gives v_perp²; spatial_vorticity_contraction fixes ω's
normalization as 2(Ω_x² + Ω_y² + Ω_z²), without an extra hidden factor. -/

lemma antisymmetric_action_eq123 (as a vx vy vz Ox Oy Oz tp : ℝ) :
    contract2 minkowskiInv (U_anti as a vx vy vz Ox Oy Oz tp)
      (U_anti as a vx vy vz Ox Oy Oz tp) =
      -2 * a^2 * minkowskiPair (spatialSlipCovector vx vy vz) (spatialSlipCovector vx vy vz) / c^2 +
      a^2 * tp^2 * contract2 minkowskiInv (spatialVorticity Ox Oy Oz) (spatialVorticity Ox Oy Oz) := by
  rw [antisymmetric_action_components, spatial_slip_norm, spatial_vorticity_contraction]
  ring

-- 6.1.3 Sign witnesses: time-space shear is negative, spatial shear positive.

noncomputable def electricBivector (e : ℝ) : T2 :=
  !![0,e,0,0; -e,0,0,0; 0,0,0,0; 0,0,0,0]

noncomputable def magneticBivector (b : ℝ) : T2 :=
  !![0,0,0,0; 0,0,b,0; 0,-b,0,0; 0,0,0,0]

lemma electric_lorentzian_contraction (e : ℝ) :
    contract2 minkowskiInv (electricBivector e) (electricBivector e) = -2 * e^2 := by
  rw [contract2_minkowskiInv_components]
  simp [electricBivector]
  ring

lemma magnetic_lorentzian_contraction (b : ℝ) :
    contract2 minkowskiInv (magneticBivector b) (magneticBivector b) = 2 * b^2 := by
  rw [contract2_minkowskiInv_components]
  simp [magneticBivector]
  ring

lemma pure_electric_negative (e : ℝ) (he : e ≠ 0) :
    contract2 minkowskiInv (electricBivector e) (electricBivector e) < 0 := by
  rw [electric_lorentzian_contraction]
  nlinarith [sq_pos_of_ne_zero he]

lemma pure_magnetic_positive (b : ℝ) (hb : b ≠ 0) :
    0 < contract2 minkowskiInv (magneticBivector b) (magneticBivector b) := by
  rw [magnetic_lorentzian_contraction]
  exact mul_pos (by norm_num) (sq_pos_of_ne_zero hb)

-- 6.1.4 The separate p. 56 measurement raises ONE index with S⁻¹.
-- It is not the background-η quadratic action contraction.

noncomputable def raiseFirst (gInv A : T2) : T2 :=
  fun μ ν => ∑ ρ : Fin 4, gInv μ ρ * A ρ ν

/-- Candidate inverse of U_sym. The inverse identity below requires as ≠ 0;
its totalized value at zero is not an inverse or a physical limiting value. -/

noncomputable def symmetricMetricInv (as : ℝ) : T2 :=
  !![-1/as^2,0,0,0; 0,as^2,0,0; 0,0,as^2,0; 0,0,0,as^2]

lemma symmetricMetricInv_left_inverse (as a vx vy vz Ox Oy Oz tp : ℝ) (has : as ≠ 0) :
    symmetricMetricInv as * U_sym as a vx vy vz Ox Oy Oz tp = 1 := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, symmetricMetricInv, U_sym, U_hat, symPart, Matrix.of_apply, has]

lemma mixed_electric_measurement (as a vx vy vz Ox Oy Oz tp : ℝ) :
    raiseFirst (symmetricMetricInv as) (U_anti as a vx vy vz Ox Oy Oz tp) 0 1 =
      (a / as^2) * (vx / c) := by
  simp [raiseFirst, Fin.sum_univ_succ, symmetricMetricInv, U_anti, U_hat, antiPart, Matrix.of_apply]
  ring

lemma mixed_magnetic_measurement (as a vx vy vz Ox Oy Oz tp : ℝ) :
    raiseFirst (symmetricMetricInv as) (U_anti as a vx vy vz Ox Oy Oz tp) 1 2 =
      -(a * as^2) * tp * Oz := by
  simp [raiseFirst, Fin.sum_univ_succ, symmetricMetricInv, U_anti, U_hat, antiPart, Matrix.of_apply]
  ring

-- η is its own inverse; restSpatialMetric is h = η + u ⊗ u.

lemma minkowskiInv_sq : minkowskiInv * minkowskiInv = (1 : T2) := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, minkowskiInv, minkowskiSign]

lemma restSpatialMetric_eq_background_projector :
    restSpatialMetric = fun μ ν => minkowskiInv μ ν + restCovector μ * restCovector ν := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;> norm_num [restSpatialMetric, minkowskiInv, minkowskiSign, restCovector]

-- 6.1.5 Dimensionless quadratic action scalar used in Eqs. (65)-(66).
-- No spacetime integral or Euler-Lagrange variation is asserted here.

/-- Dimensionless quadratic scalar `contract2 minkowskiInv U U` in the
fixed background metric. Time-space and spatial antisymmetric components have
opposite signs. This is not a spacetime integral or an Euler–Lagrange derivation. -/
noncomputable def lorentzian_action_density (U : T2) : ℝ := contract2 minkowskiInv U U

/-- Specialize the fixed-Minkowski quadratic separation to `U_hat`.
This is the Lorentzian counterpart of the separately retained Frobenius theorem. -/
lemma lorentzian_action_separation (as a vx vy vz Ox Oy Oz tp : ℝ) :
    lorentzian_action_density (U_hat as a vx vy vz Ox Oy Oz tp) =
      lorentzian_action_density (U_sym as a vx vy vz Ox Oy Oz tp) +
      lorentzian_action_density (U_anti as a vx vy vz Ox Oy Oz tp) := by
  exact lorentzian_matrix_action_separation _

/-- Exact pressure normalization from the first line of Eq. (124).
No weak-field Taylor approximation, mass derivation, or field equation is used. -/

noncomputable def kinematic_lagrangian_density (U : T2) : ℝ :=
  (1 / 4) * P_c * (lorentzian_action_density U - 4)

lemma kinematic_lagrangian_separation (U : T2) :
    kinematic_lagrangian_density U =
      (1 / 4) * P_c * (lorentzian_action_density (symPart U) - 4) +
      (1 / 4) * P_c * lorentzian_action_density (antiPart U) := by
  unfold kinematic_lagrangian_density lorentzian_action_density
  rw [lorentzian_matrix_action_separation]
  ring

end AsymmetricTensor
