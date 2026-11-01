module

public import KVApproximation.Analysis.VectorMeasureIntegral
public import Mathlib.MeasureTheory.VectorMeasure.Order

/-!
# Positive scalar tests of vector measures
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Proposition 3.3, uniqueness bridge: a positive scalar test of a vector
measure defines a finite scalar measure, vanishing on variation-null sets. -/
theorem exists_finite_positive_scalarization {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ν : VectorMeasure X F) (φ : F →L[ℝ] ℝ)
    (hpos : ∀ s : Set X, MeasurableSet s → 0 ≤ φ (ν s)) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧
      (∀ s : Set X, MeasurableSet s → μ.real s = φ (ν s)) ∧
      (∀ s : Set X, MeasurableSet s → ν.variation s = 0 → μ s = 0) := by
  sorry

end KVApproximation.Analysis
