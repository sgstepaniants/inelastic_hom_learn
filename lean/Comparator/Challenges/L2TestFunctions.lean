module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Function.L2Space

public section

open MeasureTheory TopologicalSpace
open scoped Distributions InnerProductSpace

namespace KVApproximation.Analysis

/-- Theorem 3.1, identification of weak stress limits: smooth localized
constant-vector pairings determine an L² field on any open domain. -/
theorem eq_of_integral_testFunction_inner_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    {Ω : Opens E}
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (p q : Lp F 2 (μ.restrict (Ω : Set E)))
    (h : ∀ (χ : 𝓓(Ω, ℝ)) (e : F),
      (∫ x in (Ω : Set E), χ x * ⟪p x, e⟫_ℝ ∂μ) =
        ∫ x in (Ω : Set E), χ x * ⟪q x, e⟫_ℝ ∂μ) : p = q := by
  sorry

end KVApproximation.Analysis
