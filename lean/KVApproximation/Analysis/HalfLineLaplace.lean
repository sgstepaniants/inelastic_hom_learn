module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Real Laplace transforms on the nonnegative time axis
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Theorem 3.1, Laplace-domain argument: the Bochner integral of a trajectory
against the decaying real exponential on the positive half-line. -/
def halfLineLaplace {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ℝ → F) (s : ℝ) : F :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-s * t) • u t

end KVApproximation.Analysis
