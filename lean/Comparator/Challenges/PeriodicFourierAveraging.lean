module

public import KVApproximation.Analysis.PeriodicCell
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Averaging of rescaled Fourier modes
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Theorem 3.1, periodic weak averaging: every nonconstant rescaled
Fourier mode vanishes against a fixed spatial test as the positive scale
tends to zero; the constant mode retains the test integral. -/
theorem tendsto_integral_rescale_mFourier_mul {d : ℕ} (n : Fin d → ℤ)
    (g : EuclideanSpace ℝ (Fin d) → ℂ) :
    Tendsto (fun ε : ℝ => ∫ x, rescalePeriodic (UnitAddTorus.mFourier n) ε x * g x)
      (𝓝[>] (0 : ℝ)) (𝓝 (if n = 0 then ∫ x, g x else 0)) := by
  sorry

end KVApproximation.Analysis
