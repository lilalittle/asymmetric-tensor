import AsymmetricTensor
import ProofAudit

/-!
Regression tests use actual matrices, characteristic polynomials, and complex
eigenvector equations. They do not assume a desired determinant or eigenvalue.
-/
open Polynomial

namespace AsymmetricTensor

example (a d x y r : ℝ) :
    Matrix.charpoly (alignedMatrix a d x y r) =
      (X - C d) * ((X - C a) * ((X - C d) ^ 2 + C (r ^ 2)) +
        C (x ^ 2 + y ^ 2) * (X - C d)) :=
  aligned_matrix_charpoly a d x y r

example : Matrix.det (U_hat 1 1 0 0 0 0 0 0 1) = -1 := by
  rw [U_hat_aligned_det 1 1 0 0 0 1 (by norm_num)]
  norm_num

example : Matrix.det (U_hat 1 1 (c / 2) 0 0 0 0 0 1) = -3 / 4 := by
  rw [U_hat_aligned_det 1 1 (c / 2) 0 0 1 (by norm_num)]
  have hc : c ≠ 0 := ne_of_gt c_pos
  have hv : c / 2 / c = (1 / 2 : ℝ) := by field_simp
  norm_num [hv]

example : Matrix.det (U_hat 1 1 (c / 2) (c / 2) 0 0 0 1 1) = -3 / 2 := by
  rw [U_hat_aligned_det 1 1 (c / 2) (c / 2) 1 1 (by norm_num)]
  have hc : c ≠ 0 := ne_of_gt c_pos
  have hv : c / 2 / c = (1 / 2 : ℝ) := by field_simp
  norm_num [hv]

example : Matrix.charpoly (U_hat 1 1 (c / 2) (c / 2) 0 0 0 1 1) =
    (X - 1) * ((X + 1) * ((X - 1) ^ 2 + 1) + C (1 / 2 : ℝ) * (X - 1)) := by
  rw [U_hat_aligned_charpoly]
  have hc : c ≠ 0 := ne_of_gt c_pos
  have hv : c / 2 / c = (1 / 2 : ℝ) := by field_simp
  norm_num [alignedCubic, hv]

example : Matrix.det (U_hat 2 1 0 0 0 0 0 0 1) = -1 / 16 := by
  rw [U_hat_aligned_det 2 1 0 0 0 1 (by norm_num)]
  norm_num

example : Matrix.det (U_hat 1 1 0 0 0 0 0 1 1) = -2 := by
  rw [U_hat_aligned_det 1 1 0 0 1 1 (by norm_num)]
  norm_num

example : Matrix.det (U_hat 1 1 c 0 0 0 0 0 1) = 0 := by
  rw [U_hat_aligned_det 1 1 c 0 0 1 (by norm_num)]
  simp [ne_of_gt c_pos]

example :
    Matrix.det (complexify (U_hat 1 1 (c / 2) 0 0 0 0 1 1) -
      (1 + Complex.I) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) = -1 / 4 := by
  rw [nonzero_slip_example_from_U_hat]
  exact nonzero_slip_shift_det

example :
    Matrix.det (nonzeroSlipExample - (1 + Complex.I) •
      (1 : Matrix (Fin 4) (Fin 4) ℂ)) ≠ 0 := by
  rw [nonzero_slip_shift_det]
  norm_num

example :
    ¬∀ v, (alignedMatrix (-1 : ℂ) 1 (1 / 2) 0 1).mulVec (embedTransverse v) =
      embedTransverse ((transverseBlock 1 1).mulVec v) := by
  rw [transverse_plane_invariant_iff]
  norm_num

example (d r : ℂ) :
    circularPlus ≠ 0 ∧
      (transverseBlock d r).mulVec circularPlus = (d + r * Complex.I) • circularPlus :=
  transverse_eigenvector_plus d r

example :
    (complexify (U_hat 1 1 0 0 0 0 0 1 1)).mulVec (embedTransverse circularPlus) =
      (1 + Complex.I) • embedTransverse circularPlus := by
  exact (schwinger_limit_eigenvalues 1 1 1 1 rfl (by norm_num)).1.2

example :
    (complexify (U_hat 1 1 0 0 0 0 0 1 1)).mulVec (embedTransverse circularMinus) =
      (1 - Complex.I) • embedTransverse circularMinus := by
  exact (schwinger_limit_eigenvalues 1 1 1 1 rfl (by norm_num)).2.2

example (x y : ℝ) : (alignedCubic (-1 : ℝ) 1 x y 1).eval 1 ≠ 0 := by
  norm_num [aligned_cubic_eval_spatial]

example (s x y r : ℝ) (hs : s ≠ 0) :
    (alignedCubic (-s ^ 2) (1 / s ^ 2) x y r).eval (1 / s ^ 2) = 0 ↔ r = 0 :=
  aligned_cubic_spatial_root_iff s x y r hs

#audit_theorem AsymmetricTensor.aligned_matrix_det custom []
#audit_theorem AsymmetricTensor.aligned_matrix_charpoly custom []
#audit_theorem AsymmetricTensor.aligned_matrix_shift_det custom []
#audit_theorem AsymmetricTensor.U_hat_aligned_eq custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.U_hat_aligned_det custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.U_hat_aligned_charpoly custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.aligned_cubic_spatial_root_iff custom []
#audit_theorem AsymmetricTensor.transverse_plane_invariant_iff custom []
#audit_theorem AsymmetricTensor.transverse_eigenvector_plus custom []
#audit_theorem AsymmetricTensor.transverse_eigenvector_minus custom []
#audit_theorem AsymmetricTensor.aligned_eigenvector_plus custom []
#audit_theorem AsymmetricTensor.aligned_eigenvector_minus custom []
#audit_theorem AsymmetricTensor.aligned_longitudinal_eigenvector custom []
#audit_theorem AsymmetricTensor.aligned_temporal_eigenvector custom []
#audit_theorem AsymmetricTensor.schwinger_shift_det custom []
#audit_theorem AsymmetricTensor.schwinger_shift_det_minus custom []
#audit_theorem AsymmetricTensor.schwinger_root_iff_zero_slip custom []
#audit_theorem AsymmetricTensor.nonzero_slip_shift_det custom []
#audit_theorem AsymmetricTensor.complex_U_hat_aligned_eq custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.nonzero_slip_example_from_U_hat custom
  [AsymmetricTensor.c, AsymmetricTensor.c_pos]
#audit_theorem AsymmetricTensor.schwinger_limit_eigenvalues custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.transverse_eigenvalues_are_real_iff_no_spin custom []

#print axioms U_hat_aligned_det
#print axioms U_hat_aligned_charpoly
#print axioms transverse_plane_invariant_iff
#print axioms schwinger_limit_eigenvalues
#print axioms nonzero_slip_shift_det

end AsymmetricTensor
