module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Determinants and orthogonality of matrix exponentials
-/

public section

namespace KVApproximation.Tensor

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Appendix D.3 (`app:cp3d_loading_sampling`), supporting determinant
identity: the exponential of a real square matrix has positive determinant. -/
theorem matrix_exp_det_pos (A : Matrix n n ℝ) :
    0 < (NormedSpace.exp A).det := by
  sorry

/-- Appendix D.3: a skew matrix exponentiates to an orientation-preserving
orthogonal matrix, for every finite matrix size. -/
theorem matrix_exp_skew_orthogonal (A : Matrix n n ℝ) (hA : A.transpose = -A) :
    (NormedSpace.exp A).transpose * NormedSpace.exp A = 1 ∧
      (NormedSpace.exp A).det = 1 := by
  sorry

/-- Appendix D.3: the determinant of the exponential of a real symmetric
matrix is the exponential of its trace. -/
theorem matrix_exp_symmetric_det (A : Matrix n n ℝ) (hA : A.transpose = A) :
    (NormedSpace.exp A).det = Real.exp A.trace := by
  sorry

end KVApproximation.Tensor
