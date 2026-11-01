module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Decay comparison for absolutely continuous trajectories
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Proposition B.13 (`eq:zeta_uniform_bound`), scalar comparison step:
an almost-everywhere differential inequality gives the exact finite-time
decay bound for an absolutely continuous function. -/
theorem ac_linear_decay_bound {f : ℝ → ℝ} {a b rate forcing : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hRate : 0 < rate)
    (hderiv : ∀ᵐ s ∂volume.restrict (Set.Icc a b),
      deriv f s ≤ forcing - rate * f s) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    f t ≤ f a * Real.exp (-rate * (t - a)) +
      forcing / rate * (1 - Real.exp (-rate * (t - a))) := by
  sorry

end KVApproximation.Analysis
