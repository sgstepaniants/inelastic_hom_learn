module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Exponential

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
  let B := (1 / 2 : ℝ) • A
  have hsum : B + B = A := by dsimp only [B]; module
  have hunit : IsUnit (NormedSpace.exp B).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp B)
  calc
    0 < ((NormedSpace.exp B).det) ^ 2 := sq_pos_of_ne_zero hunit.ne_zero
    _ = (NormedSpace.exp A).det := by
      conv_rhs => rw [← hsum, Matrix.exp_add_of_commute B B (Commute.refl B), Matrix.det_mul]
      ring

/-- Appendix D.3: a skew matrix exponentiates to an orientation-preserving
orthogonal matrix, for every finite matrix size. -/
theorem matrix_exp_skew_orthogonal (A : Matrix n n ℝ) (hA : A.transpose = -A) :
    (NormedSpace.exp A).transpose * NormedSpace.exp A = 1 ∧
      (NormedSpace.exp A).det = 1 := by
  have horth : (NormedSpace.exp A).transpose * NormedSpace.exp A = 1 := by
    rw [← Matrix.exp_transpose, hA, ← Matrix.exp_add_of_commute (-A) A (Commute.neg_left (Commute.refl A))]
    simp
  refine ⟨horth, ?_⟩
  have hdet := congrArg Matrix.det horth
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  have hpos := matrix_exp_det_pos A
  nlinarith

/-- Appendix D.3: the determinant of the exponential of a real symmetric
matrix is the exponential of its trace. -/
theorem matrix_exp_symmetric_det (A : Matrix n n ℝ) (hA : A.transpose = A) :
    (NormedSpace.exp A).det = Real.exp A.trace := by
  have hH : A.IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  let U := hH.eigenvectorUnitary
  have hU : IsUnit (U : Matrix n n ℝ) := Unitary.isUnit_coe
  have hinv : (U : Matrix n n ℝ)⁻¹ = (star U : Matrix n n ℝ) :=
    Matrix.inv_eq_left_inv (Unitary.coe_star_mul_self U)
  have hdiag : A = (U : Matrix n n ℝ) * Matrix.diagonal hH.eigenvalues *
      (U : Matrix n n ℝ)⁻¹ := by
    rw [hinv]
    simpa only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp]
      using hH.spectral_theorem
  calc
    (NormedSpace.exp A).det = (NormedSpace.exp (Matrix.diagonal hH.eigenvalues)).det := by
      conv_lhs => rw [hdiag, Matrix.exp_conj _ _ hU, Matrix.det_conj hU]
    _ = Real.exp (∑ i, hH.eigenvalues i) := by
      rw [Matrix.exp_diagonal, Matrix.det_diagonal]
      simp only [Pi.exp_def, ← Real.exp_eq_exp_ℝ]
      exact (Real.exp_sum Finset.univ hH.eigenvalues).symm
    _ = Real.exp A.trace := by rw [hH.trace_eq_sum_eigenvalues]; rfl

end KVApproximation.Tensor
