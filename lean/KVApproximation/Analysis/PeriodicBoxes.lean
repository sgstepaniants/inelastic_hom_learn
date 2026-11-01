module

public import KVApproximation.Analysis.PeriodicCell

/-!
# Half-open cells in physical space
-/

@[expose] public section

namespace KVApproximation.Analysis

/-- Theorem 3.1, static periodic homogenization: a half-open unit cell
in rescaled physical coordinates. The preimage convention also covers
negative nonzero scales without changing the endpoint convention. -/
def periodicBox {d : ℕ} (a : Fin d → ℝ) (ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, a i < (ε⁻¹ • x) i ∧ (ε⁻¹ • x) i ≤ a i + 1}

end KVApproximation.Analysis
