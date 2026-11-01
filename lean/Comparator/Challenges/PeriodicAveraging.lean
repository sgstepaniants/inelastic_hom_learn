module

public import KVApproximation.Analysis.PeriodicCell
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Weak averaging of periodic L² fields
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Theorem 3.1, static periodic homogenization: every periodic L² field
converges weakly on a bounded measurable physical domain to its cell mean.
The test is an arbitrary physical L² function. -/
theorem tendsto_integral_rescalePeriodic_mul {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Bornology.IsBounded Ω)
    (hΩm : MeasurableSet Ω) {f : PeriodicCell d → ℂ}
    (hf : MemLp f 2 (cellMeasure d)) {g : EuclideanSpace ℝ (Fin d) → ℂ}
    (hg : MemLp g 2 (volume.restrict Ω)) :
    Tendsto (fun ε : ℝ => ∫ x in Ω, rescalePeriodic f ε x * g x)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((∫ y, f y ∂cellMeasure d) * ∫ x in Ω, g x)) := by
  sorry

end KVApproximation.Analysis
