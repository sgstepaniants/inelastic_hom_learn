module

public import KVApproximation.Analysis.PeriodicDivergence

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Theorem 3.1, static flux tests: the Fourier coefficient of a
divergence-free periodic field is orthogonal to its lattice frequency. -/
theorem HasPeriodicZeroDivergence.fourier_coefficient {d : ℕ}
    {q : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d)}
    (h : HasPeriodicZeroDivergence q) (n : Fin d → ℤ) :
    (∑ j, (n j : ℂ) *
      ∫ y, UnitAddTorus.mFourier (-n) y * (q y j : ℂ) ∂cellMeasure d) = 0 := by
  sorry

end KVApproximation.Analysis
