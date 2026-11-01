module

public import KVApproximation.OperatorTheory.FieldForm
public import KVApproximation.OperatorTheory.VariationalIdentities

/-!
# Coefficient multiplication and its variational inverse
-/

public section

open scoped InnerProductSpace

namespace KVApproximation.Tensor

/-- Section 3.1 and Remark 1.2: the energy form depends on the actual field,
independently of its ellipticity certificates. -/
theorem CoerciveField.toForm_congr {d : ℕ} {A B : CoerciveField d}
    (h : A.field = B.field) : A.toForm = B.toForm := by
  unfold CoerciveField.toForm
  congr 1
  exact congrArg boundedFieldForm h

/-- Section 3.1: the variational Riesz operator is the actual bounded
pointwise coefficient multiplication on periodic L² strains. -/
theorem CoerciveField.riesz_eq_multiplication {d : ℕ} (A : CoerciveField d) :
    A.toForm.riesz.toContinuousLinearMap = multiplication A.field := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  exact A.toForm.riesz_spec u v

/-- Section 3.2 (`eq:operator_L`): the inverse Riesz operator is a left inverse
of multiplication by the coefficient field. -/
theorem CoerciveField.inverse_multiplication {d : ℕ} (A : CoerciveField d) :
    A.toForm.riesz.symm.toContinuousLinearMap.comp (multiplication A.field) =
      ContinuousLinearMap.id ℝ (StrainField d) := by
  rw [← A.riesz_eq_multiplication]
  apply ContinuousLinearMap.ext
  intro u
  exact A.toForm.riesz.symm_apply_apply u

/-- Section 3.2 (`eq:operator_L`): the inverse Riesz operator is also a right inverse
of multiplication by the coefficient field. -/
theorem CoerciveField.multiplication_inverse {d : ℕ} (A : CoerciveField d) :
    (multiplication A.field).comp A.toForm.riesz.symm.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ (StrainField d) := by
  rw [← A.riesz_eq_multiplication]
  apply ContinuousLinearMap.ext
  intro u
  exact A.toForm.riesz.apply_symm_apply u

end KVApproximation.Tensor
