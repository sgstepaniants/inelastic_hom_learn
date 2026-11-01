module

public import KVApproximation.OperatorTheory.FieldFormIdentities
public import KVApproximation.Tensor.FieldBounds
public import KVApproximation.Tensor.InverseAction

/-!
# Pointwise coefficient inverses on periodic strains
-/

public section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.Tensor

/-- Section 3.2 (`eq:operator_L`): the inverse variational Riesz operator
is pointwise multiplication by the inverse coefficient action. -/
theorem CoerciveField.inverse_apply_ae {d : ℕ} (A : CoerciveField d)
    (e : StrainField d) :
    A.toForm.riesz.symm e =ᵐ[cellMeasure d]
      fun y => (actionL d (A.field y)).inverse (e y) := by
  have hmul : multiplication A.field (A.toForm.riesz.symm e) = e :=
    congrArg (fun L : StrainField d →L[ℝ] StrainField d => L e) A.multiplication_inverse
  have hrep := multiplication_apply_ae A.field (A.toForm.riesz.symm e)
  rw [hmul] at hrep
  filter_upwards [(hasFieldBounds_iff_ae A.field).mp A.bounds, hrep] with y hy he
  exact ((hy.action_isInvertible A.lower_pos).inverse_apply_eq.mpr he).symm

/-- Section 3.2 (`eq:operator_L`): the relative Riesz map is the bounded
L² operator of pointwise multiplication by `V⁻¹E`. -/
theorem CoerciveField.relativeRiesz_apply_ae {d : ℕ} (V E : CoerciveField d)
    (e : StrainField d) :
    V.toForm.riesz.symm (E.toForm.riesz e) =ᵐ[cellMeasure d]
      fun y => (actionL d (V.field y)).inverse (action (E.field y) (e y)) := by
  have he : E.toForm.riesz e = multiplication E.field e :=
    congrArg (fun L : StrainField d →L[ℝ] StrainField d => L e) E.riesz_eq_multiplication
  filter_upwards [V.inverse_apply_ae (E.toForm.riesz e), multiplication_apply_ae E.field e]
    with y hy heq
  rw [he, heq] at hy
  simpa only [he] using hy

end KVApproximation.Tensor
