module

public import KVApproximation.Tensor.Symmetrization

/-!
# Frobenius contraction under symmetrization
-/

public section

namespace KVApproximation.Tensor

open scoped InnerProductSpace

/-- Theorem 3.1, static flux pairing: a symmetric stress has the same
Frobenius pairing with the full gradient and its symmetric part. -/
theorem inner_symmetrize {d : ℕ} (s : Symmetric d) (g : SecondOrder d) :
    ⟪s, symmetrize g⟫_ℝ = ⟪s.val, g⟫_ℝ := by
  sorry

/-- Theorem 3.1, strain estimates: taking the symmetric part contracts
the physical-index Frobenius norm, in every dimension. -/
theorem norm_symmetrize_le {d : ℕ} (g : SecondOrder d) :
    ‖symmetrize g‖ ≤ ‖g‖ := by
  sorry

end KVApproximation.Tensor
