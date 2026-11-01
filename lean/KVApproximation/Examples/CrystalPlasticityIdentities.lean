module

public import KVApproximation.Examples.CrystalPlasticity
public import KVApproximation.Tensor.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exact identities of the crystal-plasticity appendix
-/

public section

open KVApproximation.Tensor

namespace KVApproximation.Examples.CrystalPlasticity

/-- Appendix D.1 (`app:cp3d_constitutive`): an orthogonal initial orientation
gives zero elastic strain, zero elastic stress, and zero first Piola stress. -/
theorem initially_stress_free (O : Mat3) (hO : O * O.transpose = 1)
    (C11 C12 C44 : ℝ) :
    greenStrain O.transpose = 0 ∧
      cubicStress C11 C12 C44 (greenStrain O.transpose) = 0 ∧
      firstPiola O.transpose (cubicStress C11 C12 C44 (greenStrain O.transpose)) O = 0 := by
  have hE : greenStrain O.transpose = 0 := by
    simp [greenStrain, hO]
  have hS : cubicStress C11 C12 C44 (greenStrain O.transpose) = 0 := by
    rw [hE]
    ext i j
    simp [cubicStress]
  exact ⟨hE, hS, by simp [firstPiola, hS]⟩

/-- Appendix D.1: the elastic initial distortion is the transpose of the
orientation, since the total initial distortion is the identity. -/
theorem initial_multiplicative_decomposition (O : Mat3) (hO : O.transpose * O = 1) :
    O.transpose * O = 1 ∧ O⁻¹ = O.transpose := by
  exact ⟨hO, Matrix.inv_eq_left_inv hO⟩

/-- Appendix D.1: the initial multiplicative decomposition determines the
elastic distortion from the orientation. -/
theorem elastic_initial_factor (Fe O : Mat3) (hO : O * O.transpose = 1)
    (hInitial : Fe * O = 1) : Fe = O.transpose := by
  calc
    Fe = Fe * (O * O.transpose) := by rw [hO, mul_one]
    _ = (Fe * O) * O.transpose := (mul_assoc _ _ _).symm
    _ = O.transpose := by rw [hInitial, one_mul]

/-- Appendix D.2 (`app:cp3d_microstructure_sampling`): scaling both
resistances by the same positive factor preserves their stated ratio. -/
theorem resistance_ratio {scale : ℝ} (hscale : 0 < scale) :
    (31 * scale) / ((482 / 5 : ℝ) * scale) = (155 / 482 : ℝ) := by
  field_simp [hscale.ne']
  norm_num

/-- Appendix D.3: the skew matrix agrees with cross product. -/
theorem skew_mulVec (w v : Fin 3 → ℝ) : (skew w).mulVec v = crossProduct w v := by
  funext i
  fin_cases i <;> simp [skew, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, crossProduct] <;> ring

/-- Appendix D.3: exponentiating the skew matrix gives an orientation-preserving
orthogonal matrix, without restrictions on the rotation vector. -/
theorem rotation_orthogonal (w : Fin 3 → ℝ) :
    (rotation w).transpose * rotation w = 1 ∧ (rotation w).det = 1 := by
  apply matrix_exp_skew_orthogonal (skew w)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew, Matrix.transpose_apply]

/-- Appendix D.3: the five deviatoric coordinates preserve symmetry and zero trace. -/
theorem deviatoric_combination (B : Fin 5 → Mat3)
    (hSymm : ∀ a, (B a).transpose = B a) (hTrace : ∀ a, (B a).trace = 0)
    (coeff : Fin 5 → ℝ) :
    (∑ a, coeff a • B a).transpose = ∑ a, coeff a • B a ∧
      (∑ a, coeff a • B a).trace = 0 := by
  constructor
  · simp only [Matrix.transpose_sum, Matrix.transpose_smul, hSymm]
  · simp only [Matrix.trace_sum, Matrix.trace_smul, hTrace, smul_zero, Finset.sum_const_zero]

/-- Appendix D.3: the chosen explicit basis gives every symmetric
trace-free strain uniquely. -/
theorem deviatoric_coordinate_equivalence :
    (∀ c : Fin 5 → ℝ,
      (deviatoricFromCoordinates c).transpose = deviatoricFromCoordinates c ∧
        (deviatoricFromCoordinates c).trace = 0 ∧
        deviatoricCoordinates (deviatoricFromCoordinates c) = c) ∧
      ∀ D : Mat3, D.transpose = D → D.trace = 0 →
        deviatoricFromCoordinates (deviatoricCoordinates D) = D := by
  constructor
  · intro c
    refine ⟨?_, ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [deviatoricFromCoordinates, Matrix.transpose_apply]
    · simp [deviatoricFromCoordinates, Matrix.trace, Fin.sum_univ_succ]
    · funext i
      fin_cases i <;> simp [deviatoricCoordinates, deviatoricFromCoordinates]
  · intro D hSymm hTrace
    have h10 : D 1 0 = D 0 1 := congrFun (congrFun hSymm 0) 1
    have h20 : D 2 0 = D 0 2 := congrFun (congrFun hSymm 0) 2
    have h21 : D 2 1 = D 1 2 := congrFun (congrFun hSymm 1) 2
    have ht : D 0 0 + D 1 1 + D 2 2 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_succ, add_assoc] using hTrace
    ext i j
    fin_cases i <;> fin_cases j <;> simp [deviatoricFromCoordinates, deviatoricCoordinates] <;> linarith

/-- Appendix D.3: the exponential reconstruction has exactly the prescribed
positive determinant, so its logarithm recovers the volumetric coordinate. -/
theorem deformation_determinant (w : Fin 3 → ℝ) (volumeLog : ℝ) (D : Mat3)
    (hSymm : D.transpose = D) (hTrace : D.trace = 0) :
    (deformation w volumeLog D).det = Real.exp volumeLog ∧
      0 < (deformation w volumeLog D).det ∧
      Real.log (deformation w volumeLog D).det = volumeLog := by
  have hL : (logarithmicStrain volumeLog D).transpose = logarithmicStrain volumeLog D := by
    simp [logarithmicStrain, hSymm]
  have ht : (logarithmicStrain volumeLog D).trace = volumeLog := by
    simp [logarithmicStrain, Matrix.trace_add, Matrix.trace_smul, hTrace]
  have hd : (deformation w volumeLog D).det = Real.exp volumeLog := by
    rw [deformation, Matrix.det_mul, matrix_exp_symmetric_det _ hL,
      (rotation_orthogonal w).2, ht, one_mul]
  exact ⟨hd, hd ▸ Real.exp_pos volumeLog, by rw [hd, Real.log_exp]⟩

/-- Appendix D.3: zero initial loading coordinates give the identity deformation. -/
theorem deformation_zero : deformation 0 0 0 = 1 := by
  have hs : skew (0 : Fin 3 → ℝ) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skew]
  rw [deformation, rotation, hs]
  simp [logarithmicStrain]

end KVApproximation.Examples.CrystalPlasticity
