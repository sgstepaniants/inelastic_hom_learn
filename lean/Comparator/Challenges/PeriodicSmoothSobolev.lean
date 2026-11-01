module

public import KVApproximation.Analysis.PeriodicSobolev

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Theorem 3.1, periodic flux tests: a C¹ periodic displacement is an
actual periodic H¹ element, with its prescribed value and full gradient. -/
theorem PeriodicC1.exists_periodicH1 {d : ℕ}
    (φ : PeriodicC1 d (EuclideanSpace ℝ (Fin d))) :
    ∃ u : PeriodicH1 d,
      (PeriodicH1.valueL d u =ᵐ[cellMeasure d] φ.value) ∧
      (PeriodicH1.gradientL d u =ᵐ[cellMeasure d] periodicGradient φ.value) := by
  sorry

end KVApproximation.Analysis
