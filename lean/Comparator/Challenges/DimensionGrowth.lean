module

public import KVApproximation.Approximation.Dimension

/-!
# Ceiling bounds for the logarithmic construction
-/

public section

namespace KVApproximation.Approximation

/-- Theorem 4.5, asymptotic estimate: the logarithmic partition count is linear
in the span, including span zero as an algebraic boundary case. -/
theorem logPartitionCount_le {R : ℝ} (hR : 0 ≤ R) :
    (logPartitionCount R : ℝ) ≤ 2 * (1 + R) := by
  sorry

/-- Theorem 4.5, asymptotic estimate: a fixed interpolation constant contributes
only a multiplicative constant to logarithmic tolerance growth. -/
theorem interpolationOrder_le (κ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (interpolationOrder κ ε : ℝ) ≤
      (2 + (|Real.log κ| + 1) / Real.log 2) *
        (1 + max 0 (Real.log (1 / ε))) := by
  sorry

/-- Theorem 4.5, asymptotic estimate: the nonsingleton formula has a uniform
constant depending only on the tensor dimension. -/
theorem nonsingletonStateDimension_uniform_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ (n : ℝ) ≤ C ∧ ∀ R E : ℝ, 0 ≤ R → 0 < E →
      (nonsingletonStateDimension n R E : ℝ) ≤
        C * (1 + R) * (1 + max 0 (Real.log (1 / E))) := by
  sorry

end KVApproximation.Approximation
