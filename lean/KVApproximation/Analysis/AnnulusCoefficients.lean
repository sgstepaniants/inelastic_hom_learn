module

public import Mathlib.MeasureTheory.Integral.CircleIntegral

@[expose] public section

noncomputable section

namespace KVApproximation.Analysis

open scoped Real

/-- Lemma B.9, analytic coefficient proof: a nonnegative Laurent coefficient
computed on a circle centered at zero. -/
def circleCoefficient {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℂ → F) (radius : ℝ) (k : ℕ) : F :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    ∮ z in C(0, radius), (z ^ (k + 1))⁻¹ • f z

end KVApproximation.Analysis
