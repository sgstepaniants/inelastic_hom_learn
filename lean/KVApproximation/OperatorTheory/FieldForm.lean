module

public import KVApproximation.OperatorTheory.CoerciveForm
public import KVApproximation.Tensor.MultiplicationIdentities

/-!
# Variational forms of periodic coefficient fields
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Tensor

/-- Section 3.1: the symmetric coercive form of the actual coefficient
field. Boundedness comes from Hölder multiplication; coercivity comes from
the stated field lower bound. -/
def CoerciveField.toForm {d : ℕ} (A : CoerciveField d) :
    OperatorTheory.CoerciveForm (StrainField d) where
  form := boundedFieldForm A.field
  symmetric := boundedFieldForm_symmetric A.field
  coercive := by
    refine ⟨A.lower, A.lower_pos, ?_⟩
    intro e
    rw [boundedFieldForm_apply]
    simpa only [pow_two, mul_assoc] using (A.bounds e).1

end KVApproximation.Tensor
