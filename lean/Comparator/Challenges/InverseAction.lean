module

public import KVApproximation.Tensor.LinearAction
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Inverse coefficient action
-/

public section

namespace KVApproximation.Tensor

/-- Section 3.2 (`eq:operator_L`): a coercive elasticity tensor acts
invertibly on the finite-dimensional symmetric strain space. -/
theorem HasBounds.action_isInvertible {d : ℕ} {α β : ℝ} {A : Elasticity d}
    (hα : 0 < α) (hA : HasBounds α β A) :
    (actionL d A).IsInvertible := by
  sorry

/-- Section 3.2 (`eq:operator_L`): the pointwise inverse has the
reciprocal coercivity bound in the Frobenius norm. -/
theorem HasBounds.inverse_action_norm_le {d : ℕ} {α β : ℝ} {A : Elasticity d}
    (hα : 0 < α) (hA : HasBounds α β A) (v : Symmetric d) :
    ‖(actionL d A).inverse v‖ ≤ ‖v‖ / α := by
  sorry

end KVApproximation.Tensor
