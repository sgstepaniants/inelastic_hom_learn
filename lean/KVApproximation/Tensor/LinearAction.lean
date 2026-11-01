module

public import KVApproximation.Tensor.Action
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Linear tensor contraction
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Tensor

/-- Section 2.1: contraction with a fixed tensor as a linear map. -/
def actionLinear {d : ℕ} (A : Elasticity d) :
    Symmetric d →ₗ[ℝ] Symmetric d where
  toFun := action A
  map_add' e f := by
    apply Subtype.ext
    apply PiLp.ext
    intro ij
    simp [action, mul_add, Finset.sum_add_distrib]
  map_smul' r e := by
    apply Subtype.ext
    apply PiLp.ext
    intro ij
    simp [action, mul_left_comm, Finset.mul_sum]

/-- Section 2.1, tensor contraction: the continuous bilinear action of
an elasticity tensor on a symmetric strain. -/
def actionL (d : ℕ) : Elasticity d →L[ℝ] Symmetric d →L[ℝ] Symmetric d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => (actionLinear A).toContinuousLinearMap
      map_add' := by
        intro A B
        apply ContinuousLinearMap.ext
        intro e
        apply Subtype.ext
        apply PiLp.ext
        intro ij
        simp [actionLinear, action, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r A
        apply ContinuousLinearMap.ext
        intro e
        apply Subtype.ext
        apply PiLp.ext
        intro ij
        simp [actionLinear, action, mul_assoc, Finset.mul_sum] }

end KVApproximation.Tensor
