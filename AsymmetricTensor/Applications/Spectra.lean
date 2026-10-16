/-
Copyright (c) 2026 Binyamin Tsadik Bair-Mosheh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Binyamin Tsadik Bair-Mosheh
-/
module

public import AsymmetricTensor.MatrixAlgebra
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Aligned full-matrix spectra and the transverse invariant plane

These are finite matrix identities. Complex roots of the transverse block lift
only under the stated decoupling condition; no impedance or mass law follows.
See `docs/full-tensor-spectra.md` for the manuscript correction proposal.
-/

@[expose] public section

open Polynomial

set_option autoImplicit false
set_option linter.unusedSectionVars true

namespace AsymmetricTensor

/--
An aligned matrix with temporal diagonal `a`, spatial diagonal `d`, transverse
slip entries `x,y`, and rotation entry `r`. This definition has no physical axioms.
-/
def alignedMatrix {R : Type*} [CommRing R] (a d x y r : R) :
    Matrix (Fin 4) (Fin 4) R :=
  !![a, -x, -y, 0; x, d, -r, 0; y, r, d, 0; 0, 0, 0, d]

/-- Exact determinant of the aligned matrix, including both transverse slips. -/
theorem aligned_matrix_det {R : Type*} [CommRing R] (a d x y r : R) :
    Matrix.det (alignedMatrix a d x y r) =
      d * (a * (d ^ 2 + r ^ 2) + (x ^ 2 + y ^ 2) * d) := by
  norm_num [alignedMatrix, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- The cubic factor left after removing the invariant longitudinal root. -/
noncomputable def alignedCubic {R : Type*} [CommRing R] (a d x y r : R) : R[X] :=
  (X - C a) * ((X - C d) ^ 2 + C (r ^ 2)) + C (x ^ 2 + y ^ 2) * (X - C d)

/-- The characteristic polynomial is computed from `Matrix.charpoly`, not assumed. -/
theorem aligned_matrix_charpoly {R : Type*} [CommRing R] (a d x y r : R) :
    Matrix.charpoly (alignedMatrix a d x y r) =
      (X - C d) * alignedCubic a d x y r := by
  have h : Matrix.charmatrix (alignedMatrix a d x y r) =
      alignedMatrix (X - C a) (X - C d) (-C x) (-C y) (-C r) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [alignedMatrix]
  rw [Matrix.charpoly, h, aligned_matrix_det]
  simp [alignedCubic]

/-- The shifted determinant uses the paper's `U - λI` convention (dimension four). -/
theorem aligned_matrix_shift_det {R : Type*} [CommRing R] (a d x y r z : R) :
    Matrix.det (alignedMatrix a d x y r - z • (1 : Matrix (Fin 4) (Fin 4) R)) =
      (d - z) * ((a - z) * ((d - z) ^ 2 + r ^ 2) +
        (x ^ 2 + y ^ 2) * (d - z)) := by
  have h : alignedMatrix a d x y r - z • (1 : Matrix (Fin 4) (Fin 4) R) =
      alignedMatrix (a - z) (d - z) x y r := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [alignedMatrix]
  rw [h, aligned_matrix_det]

/-- Bridge from the actual `U_hat`, aligned along the rotation axis with `v_z = 0`. -/
theorem U_hat_aligned_eq (s b vx vy w t : ℝ) :
    U_hat s b vx vy 0 0 0 w t =
      alignedMatrix (-s ^ 2) (1 / s ^ 2) (b * (vx / c)) (b * (vy / c)) (b * t * w) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [U_hat, alignedMatrix] <;> ring

/--
The aligned determinant formula is valid for nonzero admittance. In particular,
this theorem does not evaluate a singular limit or justify substituting `s = 0`.
-/
theorem U_hat_aligned_det (s b vx vy w t : ℝ) (hs : s ≠ 0) :
    Matrix.det (U_hat s b vx vy 0 0 0 w t) =
      -(1 / s ^ 4) - (b * t * w) ^ 2 +
        ((b * (vx / c)) ^ 2 + (b * (vy / c)) ^ 2) / s ^ 4 := by
  rw [U_hat_aligned_eq, aligned_matrix_det]
  field_simp [hs]
  ring

/--
Characteristic polynomial of the actual aligned tensor. The formula with explicit
`1 / s²` entries is totalized; physical use of the nonzero-admittance model needs `s ≠ 0`.
-/
theorem U_hat_aligned_charpoly (s b vx vy w t : ℝ) :
    Matrix.charpoly (U_hat s b vx vy 0 0 0 w t) =
      (X - C (1 / s ^ 2)) *
        alignedCubic (-s ^ 2) (1 / s ^ 2) (b * (vx / c)) (b * (vy / c)) (b * t * w) := by
  rw [U_hat_aligned_eq, aligned_matrix_charpoly]

/-- Evaluation of the coupled cubic at the separate longitudinal root. -/
theorem aligned_cubic_eval_spatial {R : Type*} [CommRing R] (a d x y r : R) :
    (alignedCubic a d x y r).eval d = (d - a) * r ^ 2 := by
  simp [alignedCubic]

/--
For real nonzero admittance, the coupled cubic shares the longitudinal root
exactly when the rotation coupling vanishes. This does not by itself imply `Ω = 0`.
-/
theorem aligned_cubic_spatial_root_iff (s x y r : ℝ) (hs : s ≠ 0) :
    (alignedCubic (-s ^ 2) (1 / s ^ 2) x y r).eval (1 / s ^ 2) = 0 ↔ r = 0 := by
  rw [aligned_cubic_eval_spatial]
  have hp : 0 < 1 / s ^ 2 - -s ^ 2 := by
    have hsq : 0 < s ^ 2 := sq_pos_of_ne_zero hs
    have hinv : 0 < 1 / s ^ 2 := one_div_pos.mpr hsq
    linarith
  rw [mul_eq_zero]
  exact (or_iff_right (ne_of_gt hp)).trans sq_eq_zero_iff

/-- Isolated spatial block; its eigenvalues need not be full-matrix eigenvalues. -/
def transverseBlock (d r : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![d, -r; r, d]

/-- Coordinate embedding of the transverse spatial plane into four components. -/
def embedTransverse (v : Fin 2 → ℂ) : Fin 4 → ℂ := ![0, v 0, v 1, 0]

/-- The positive circular vector has eigenvalue `d + r i`. -/
def circularPlus : Fin 2 → ℂ := ![1, -Complex.I]

/-- The negative circular vector has eigenvalue `d - r i`. -/
def circularMinus : Fin 2 → ℂ := ![1, Complex.I]

/-- The circular vectors are nonzero, independently of the matrix parameters. -/
theorem circular_vectors_ne_zero : circularPlus ≠ 0 ∧ circularMinus ≠ 0 := by
  constructor <;> intro h <;> have h0 := congrFun h 0 <;>
    norm_num [circularPlus, circularMinus] at h0

/-- An actual complex block eigenvector equation, with an explicit nonzero witness. -/
theorem transverse_eigenvector_plus (d r : ℂ) :
    circularPlus ≠ 0 ∧
      (transverseBlock d r).mulVec circularPlus = (d + r * Complex.I) • circularPlus := by
  refine ⟨circular_vectors_ne_zero.1, ?_⟩
  ext i
  fin_cases i <;>
    simp [transverseBlock, circularPlus, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

/-- The conjugate circular eigenvector equation. -/
theorem transverse_eigenvector_minus (d r : ℂ) :
    circularMinus ≠ 0 ∧
      (transverseBlock d r).mulVec circularMinus = (d - r * Complex.I) • circularMinus := by
  refine ⟨circular_vectors_ne_zero.2, ?_⟩
  ext i
  fin_cases i <;>
    simp [transverseBlock, circularMinus, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

/--
The transverse plane is invariant, with the displayed block action, if and only
if both temporal slip couplings vanish. The condition is proved, not presumed.
-/
theorem transverse_plane_invariant_iff (a d x y r : ℂ) :
    (∀ v, (alignedMatrix a d x y r).mulVec (embedTransverse v) =
      embedTransverse ((transverseBlock d r).mulVec v)) ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hx := congrFun (h ![1, 0]) 0
    have hy := congrFun (h ![0, 1]) 0
    simp [alignedMatrix, embedTransverse, transverseBlock, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] at hx hy
    exact ⟨hx, hy⟩
  · rintro ⟨rfl, rfl⟩ v
    ext i
    fin_cases i <;>
      simp [alignedMatrix, embedTransverse, transverseBlock, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]

/-- The positive block eigenvector lifts to the full matrix under zero slip. -/
theorem aligned_eigenvector_plus (a d r : ℂ) :
    embedTransverse circularPlus ≠ 0 ∧
      (alignedMatrix a d 0 0 r).mulVec (embedTransverse circularPlus) =
        (d + r * Complex.I) • embedTransverse circularPlus := by
  constructor
  · intro h
    have h1 := congrFun h 1
    norm_num [embedTransverse, circularPlus] at h1
  · rw [(transverse_plane_invariant_iff a d 0 0 r).2 ⟨rfl, rfl⟩,
      (transverse_eigenvector_plus d r).2]
    ext i
    fin_cases i <;> simp [embedTransverse]

/-- The negative block eigenvector lifts to the full matrix under zero slip. -/
theorem aligned_eigenvector_minus (a d r : ℂ) :
    embedTransverse circularMinus ≠ 0 ∧
      (alignedMatrix a d 0 0 r).mulVec (embedTransverse circularMinus) =
        (d - r * Complex.I) • embedTransverse circularMinus := by
  constructor
  · intro h
    have h1 := congrFun h 1
    norm_num [embedTransverse, circularMinus] at h1
  · rw [(transverse_plane_invariant_iff a d 0 0 r).2 ⟨rfl, rfl⟩,
      (transverse_eigenvector_minus d r).2]
    ext i
    fin_cases i <;> simp [embedTransverse]

/-- The longitudinal root has a nonzero eigenvector even in the coupled case. -/
theorem aligned_longitudinal_eigenvector (a d x y r : ℂ) :
    (![0, 0, 0, 1] : Fin 4 → ℂ) ≠ 0 ∧
      (alignedMatrix a d x y r).mulVec ![0, 0, 0, 1] =
        d • (![0, 0, 0, 1] : Fin 4 → ℂ) := by
  constructor
  · intro h
    have h3 := congrFun h 3
    norm_num at h3
  · ext i
    fin_cases i <;> simp [alignedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The temporal diagonal is an eigenvalue in the zero-slip aligned case. -/
theorem aligned_temporal_eigenvector (a d r : ℂ) :
    (![1, 0, 0, 0] : Fin 4 → ℂ) ≠ 0 ∧
      (alignedMatrix a d 0 0 r).mulVec ![1, 0, 0, 0] =
        a • (![1, 0, 0, 0] : Fin 4 → ℂ) := by
  constructor
  · intro h
    have h0 := congrFun h 0
    norm_num at h0
  · ext i
    fin_cases i <;> simp [alignedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The issue's explicit matrix, with nonzero transverse slip `1/2`. -/
noncomputable def nonzeroSlipExample : Matrix (Fin 4) (Fin 4) ℂ := alignedMatrix (-1) 1 (1 / 2) 0 1

/--
At unit admittance and unit rotation coupling, inserting the positive block
root in the full determinant leaves minus the squared transverse slip.
-/
theorem schwinger_shift_det (x y : ℝ) :
    Matrix.det (alignedMatrix (-1 : ℂ) 1 x y 1 - (1 + Complex.I) •
      (1 : Matrix (Fin 4) (Fin 4) ℂ)) = -((x : ℂ) ^ 2 + (y : ℂ) ^ 2) := by
  rw [aligned_matrix_shift_det]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The conjugate block root gives the same nonzero-slip obstruction. -/
theorem schwinger_shift_det_minus (x y : ℝ) :
    Matrix.det (alignedMatrix (-1 : ℂ) 1 x y 1 - (1 - Complex.I) •
      (1 : Matrix (Fin 4) (Fin 4) ℂ)) = -((x : ℂ) ^ 2 + (y : ℂ) ^ 2) := by
  rw [aligned_matrix_shift_det]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The candidate root `1+i` is a full determinant root exactly at zero transverse slip. -/
theorem schwinger_root_iff_zero_slip (x y : ℝ) :
    Matrix.det (alignedMatrix (-1 : ℂ) 1 x y 1 - (1 + Complex.I) •
      (1 : Matrix (Fin 4) (Fin 4) ℂ)) = 0 ↔ x = 0 ∧ y = 0 := by
  rw [schwinger_shift_det, neg_eq_zero]
  norm_cast
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- `1+i` is not a root of the full characteristic determinant in this example. -/
theorem nonzero_slip_shift_det :
    Matrix.det (nonzeroSlipExample - (1 + Complex.I) •
      (1 : Matrix (Fin 4) (Fin 4) ℂ)) = -1 / 4 := by
  have h := schwinger_shift_det (1 / 2) 0
  norm_num [nonzeroSlipExample] at h ⊢
  exact h

/-- Complexification changes coefficients, not the underlying component matrix. -/
noncomputable def complexify (U : T2) : Matrix (Fin 4) (Fin 4) ℂ :=
  U.map (fun x => (x : ℂ))

/-- The complex aligned matrix is derived from the actual real `U_hat`. -/
theorem complex_U_hat_aligned_eq (s b vx vy w t : ℝ) :
    complexify (U_hat s b vx vy 0 0 0 w t) =
      alignedMatrix (-(s : ℂ) ^ 2) (1 / (s : ℂ) ^ 2)
        (b * (vx / c) : ℝ) (b * (vy / c) : ℝ) (b * t * w : ℝ) := by
  rw [U_hat_aligned_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [complexify, alignedMatrix]

/-- The counterexample also specializes `U_hat` with `v_x/c = 1/2`. -/
theorem nonzero_slip_example_from_U_hat :
    complexify (U_hat 1 1 (c / 2) 0 0 0 0 1 1) = nonzeroSlipExample := by
  rw [complex_U_hat_aligned_eq]
  have hc : c ≠ 0 := ne_of_gt c_pos
  have hv : c / 2 / c = (1 / 2 : ℝ) := by field_simp
  simp [nonzeroSlipExample, hv]

end AsymmetricTensor
