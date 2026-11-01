module

public import KVApproximation.OperatorTheory.FieldForm

/-!
# Coefficient multiplication and its variational inverse
-/

public section

namespace KVApproximation.Tensor

/-- Section 3.1 and Remark 1.2: the energy form depends on the actual field,
independently of its ellipticity certificates. -/
theorem CoerciveField.toForm_congr {d : ℕ} {A B : CoerciveField d}
    (h : A.field = B.field) : A.toForm = B.toForm := by
  sorry

/-- Section 3.1: the variational Riesz operator is the actual bounded
pointwise coefficient multiplication on periodic L² strains. -/
theorem CoerciveField.riesz_eq_multiplication {d : ℕ} (A : CoerciveField d) :
    A.toForm.riesz.toContinuousLinearMap = multiplication A.field := by
  sorry

/-- Section 3.2 (`eq:operator_L`): the inverse Riesz operator is a left inverse
of multiplication by the coefficient field. -/
theorem CoerciveField.inverse_multiplication {d : ℕ} (A : CoerciveField d) :
    A.toForm.riesz.symm.toContinuousLinearMap.comp (multiplication A.field) =
      ContinuousLinearMap.id ℝ (StrainField d) := by
  sorry

/-- Section 3.2 (`eq:operator_L`): the inverse Riesz operator is also a right inverse
of multiplication by the coefficient field. -/
theorem CoerciveField.multiplication_inverse {d : ℕ} (A : CoerciveField d) :
    (multiplication A.field).comp A.toForm.riesz.symm.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ (StrainField d) := by
  sorry

end KVApproximation.Tensor
