module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Uniform local averaging of a compact continuous family
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Remark 4.3, Fourier projection ingredient: a single local average
approximates evaluation at a fixed point uniformly over a compact parameter
family. The neighborhood has strictly positive finite measure. -/
theorem exists_uniform_local_average
    {P X E : Type*} [TopologicalSpace P] [CompactSpace P]
    [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (F : C(P × X, E)) (x₀ : X) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ 0 < μ.real (Metric.ball x₀ r) ∧ ∀ p : P,
      ‖(μ.real (Metric.ball x₀ r))⁻¹ •
          (∫ x in Metric.ball x₀ r, F (p, x) ∂μ) - F (p, x₀)‖ < ε := by
  sorry

end KVApproximation.Analysis
