import AsymmetricTensor
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
Well-typed specifications for the bounded determinant task.
These definitions are propositions, not theorems or axioms: this file supplies
no proof of the proposed determinant or volume results. Production remains unchanged.
-/
namespace AsymmetricTensor.Roadmap

noncomputable def alignedU_hat (a b v w t : ℝ) : T2 :=
  U_hat a b v 0 0 0 0 w t

noncomputable def spatialS (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal (fun _ => 1 / a ^ 2)

def alignedDeterminantTarget : Prop :=
  ∀ a b v w t : ℝ, a ≠ 0 →
    Matrix.det (alignedU_hat a b v w t) =
      -(1 / a ^ 4) - (b * t * w) ^ 2 + (b * (v / c)) ^ 2 / a ^ 4

def classicalIsochoricTarget : Prop :=
  ∀ b v w t : ℝ,
    (Matrix.det (alignedU_hat 1 b v w t) = -1 ↔
      (b * (v / c)) ^ 2 = (b * t * w) ^ 2)

def antisymmetricPartTarget : Prop :=
  ∀ U : T2, (antiPart U).transpose = -antiPart U ∧ Matrix.trace (antiPart U) = 0

def tracefreeNonIsochoricTarget : Prop :=
  let W := alignedU_hat 1 1 0 1 1
  (antiPart W).transpose = -antiPart W ∧ Matrix.trace (antiPart W) = 0 ∧
    Matrix.det W = -2 ∧ Matrix.det W ≠ -1

def symmetricDeterminantTarget : Prop :=
  ∀ a b v w t : ℝ, a ≠ 0 →
    Matrix.det (symPart (alignedU_hat a b v w t)) = -(1 / a ^ 4)

def spatialBlockTarget : Prop :=
  ∀ a b v w t : ℝ,
    (symPart (alignedU_hat a b v w t)).submatrix Fin.succ Fin.succ = spatialS a

def spatialDeterminantTarget : Prop :=
  ∀ a : ℝ, a ≠ 0 → Matrix.det (spatialS a) = 1 / a ^ 6

def spatialDensityTarget : Prop :=
  ∀ a : ℝ, 0 < a → Real.sqrt (Matrix.det (spatialS a)) = 1 / a ^ 3

def symmetricSpacetimeDensityTarget : Prop :=
  ∀ a b v w t : ℝ, 0 < a →
    Real.sqrt |Matrix.det (symPart (alignedU_hat a b v w t))| = 1 / a ^ 2

#check alignedDeterminantTarget
#check classicalIsochoricTarget
#check antisymmetricPartTarget
#check tracefreeNonIsochoricTarget
#check symmetricDeterminantTarget
#check spatialBlockTarget
#check spatialDeterminantTarget
#check spatialDensityTarget
#check symmetricSpacetimeDensityTarget

end AsymmetricTensor.Roadmap
