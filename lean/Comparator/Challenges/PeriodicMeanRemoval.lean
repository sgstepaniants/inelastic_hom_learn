module

public import KVApproximation.Analysis.PeriodicSobolev

/-!
# Removing the mean from periodic displacement tests
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Section 3.1 and Appendix A.3: every constant displacement is a
periodic H¹ field with zero gradient. -/
theorem PeriodicH1.exists_constant {d : ℕ} (c : EuclideanSpace ℝ (Fin d)) :
    ∃ u : PeriodicH1 d,
      PeriodicH1.valueL d u = Lp.const 2 (cellMeasure d) c ∧
      PeriodicH1.gradientL d u = 0 := by
  sorry

/-- Appendix A.3, testing the balance equation in `eq:cell_weak`:
subtracting the mean leaves the full periodic weak gradient unchanged. -/
theorem PeriodicH1.exists_zeroMean_same_gradient {d : ℕ} (u : PeriodicH1 d) :
    ∃ v : ZeroMeanPeriodicH1 d,
      PeriodicH1.valueL d (v : PeriodicH1 d) = PeriodicH1.valueL d u -
        Lp.const 2 (cellMeasure d) (cellAverageL d (PeriodicH1.valueL d u)) ∧
      PeriodicH1.gradientL d (v : PeriodicH1 d) = PeriodicH1.gradientL d u := by
  sorry

end KVApproximation.Analysis
