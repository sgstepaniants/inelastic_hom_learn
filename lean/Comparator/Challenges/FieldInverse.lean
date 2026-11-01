module

public import KVApproximation.OperatorTheory.FieldForm
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

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
  sorry

/-- Section 3.2 (`eq:operator_L`): the relative Riesz map is the bounded
L² operator of pointwise multiplication by `V⁻¹E`. -/
theorem CoerciveField.relativeRiesz_apply_ae {d : ℕ} (V E : CoerciveField d)
    (e : StrainField d) :
    V.toForm.riesz.symm (E.toForm.riesz e) =ᵐ[cellMeasure d]
      fun y => (actionL d (V.field y)).inverse (action (E.field y) (e y)) := by
  sorry

end KVApproximation.Tensor
