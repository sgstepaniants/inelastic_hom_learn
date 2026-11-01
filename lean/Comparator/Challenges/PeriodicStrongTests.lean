module

public import KVApproximation.Analysis.PeriodicCell
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

public section

open MeasureTheory Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Theorem 3.1, localized oscillating tests: periodic weak averaging
persists when the physical L² test field converges strongly. -/
theorem tendsto_integral_rescalePeriodic_inner_strong_along {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Bornology.IsBounded Ω)
    (hΩm : MeasurableSet Ω) {f : PeriodicCell d → F}
    (hf : MemLp f 2 (cellMeasure d))
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : Tendsto ε l (𝓝[>] (0 : ℝ)))
    {g : ι → Lp F 2 (volume.restrict Ω)} {g₀ : Lp F 2 (volume.restrict Ω)}
    (hg : Tendsto g l (𝓝 g₀)) :
    Tendsto (fun i => ∫ x in Ω, inner ℝ (rescalePeriodic f (ε i) x) (g i x))
      l
      (𝓝 (inner ℝ (∫ y, f y ∂cellMeasure d) (∫ x in Ω, g₀ x))) := by
  sorry

/-- Theorem 3.1, localized oscillating tests: periodic weak averaging
persists when the physical L² test field converges strongly. -/
theorem tendsto_integral_rescalePeriodic_inner_strong {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Bornology.IsBounded Ω)
    (hΩm : MeasurableSet Ω) {f : PeriodicCell d → F}
    (hf : MemLp f 2 (cellMeasure d))
    {g : ℝ → Lp F 2 (volume.restrict Ω)} {g₀ : Lp F 2 (volume.restrict Ω)}
    (hg : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 g₀)) :
    Tendsto (fun ε : ℝ => ∫ x in Ω, inner ℝ (rescalePeriodic f ε x) (g ε x))
      (𝓝[>] (0 : ℝ))
      (𝓝 (inner ℝ (∫ y, f y ∂cellMeasure d) (∫ x in Ω, g₀ x))) := by
  sorry

end KVApproximation.Analysis
