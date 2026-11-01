module

public import KVApproximation.Homogenization.CorrectorSpace
public import KVApproximation.OperatorTheory.FieldForm

/-!
# Static periodic cell operators
-/

@[expose] public section

noncomputable section

open KVApproximation.Analysis KVApproximation.Tensor
open scoped InnerProductSpace

namespace KVApproximation.Homogenization

/-- Section 3.2 (`eqns:operator_P`): the coefficient-weighted projection
onto the concrete periodic strain-corrector space. -/
def cellProjection {d : ℕ} (A : CoerciveField d) :
    StrainField d →L[ℝ] correctorSubspace d :=
  A.toForm.projection (correctorSubspace d)

/-- Theorem 3.1 (`eq:homogenized_tensors`): the static effective form,
obtained by embedding constant strains and solving the periodic cell problem. -/
def effectiveForm {d : ℕ} (A : CoerciveField d) :
    Symmetric d →L[ℝ] Symmetric d →L[ℝ] ℝ :=
  A.toForm.homogenizedForm (correctorSubspace d) (constantStrainL d)

end KVApproximation.Homogenization
