module

public import KVApproximation.Tensor.LinearAction

/-!
# Operator and Frobenius bounds for elasticity tensors
-/

public section

namespace KVApproximation.Tensor

/-- Lemma B.2, Frobenius bound: summing squared images of an orthonormal
strain basis gives the full physical-index Frobenius norm. -/
theorem norm_sq_eq_sum_norm_action {d : ℕ} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Symmetric d)) (A : Elasticity d) :
    ‖A‖ ^ 2 = ∑ i, ‖action A (b i)‖ ^ 2 := by
  sorry

/-- Lemma B.2 and Proposition B.3: the positive tensor action has the quadratic upper
bound as an operator-norm bound. -/
theorem HasBounds.action_opNorm_le {d : ℕ} {α β : ℝ} {A : Elasticity d}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hA : HasBounds α β A) :
    ‖actionL d A‖ ≤ β := by
  sorry

/-- Proposition B.3: the same upper bound controls the action on each strain. -/
theorem HasBounds.norm_action_le {d : ℕ} {α β : ℝ} {A : Elasticity d}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hA : HasBounds α β A) (e : Symmetric d) :
    ‖action A e‖ ≤ β * ‖e‖ := by
  sorry

/-- Lemma B.2 (`lem:bv_compact`), coefficient bound: the exact Frobenius
factor is the square root of the symmetric-strain dimension. -/
theorem HasBounds.norm_le_sqrt_dimension {d : ℕ} {α β : ℝ} {A : Elasticity d}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hA : HasBounds α β A) :
    ‖A‖ ≤ Real.sqrt (strainDimension d) * β := by
  sorry

end KVApproximation.Tensor
