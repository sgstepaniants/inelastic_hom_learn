module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Uniqueness from compactly supported exponential moments
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Proposition 3.3, uniqueness bridge: on a positive compact interval,
the weighted exponential moments at nonnegative integer times determine a
finite positive measure. -/
theorem measure_eq_of_weighted_exponential_moments {a b : ℝ} (ha : 0 < a)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (Set.Icc a b)ᶜ = 0) (hν : ν (Set.Icc a b)ᶜ = 0)
    (hmom : ∀ n : ℕ, (∫ r, r * (Real.exp (-r)) ^ n ∂μ) =
      ∫ r, r * (Real.exp (-r)) ^ n ∂ν) : μ = ν := by
  sorry

end KVApproximation.Analysis
