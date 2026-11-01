module

public import KVApproximation.Analysis.PeriodicSmooth
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Distributionally divergence-free periodic fields
-/

@[expose] public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Theorem 3.1, static flux tests: a periodic vector field has zero
distributional divergence when it annihilates all scalar periodic C¹ gradients. -/
def HasPeriodicZeroDivergence {d : ℕ}
    (q : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d)) : Prop :=
  ∀ φ : PeriodicC1 d ℝ,
    (∫ y, ∑ j, q y j * φ.partial j y ∂cellMeasure d) = 0

end KVApproximation.Analysis
