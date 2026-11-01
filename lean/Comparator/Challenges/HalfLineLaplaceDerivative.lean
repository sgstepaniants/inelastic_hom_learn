module

public import KVApproximation.Analysis.HalfLineLaplace
public import Mathlib.Analysis.Calculus.Deriv.Basic

public section

namespace KVApproximation.Analysis

/-- Theorem 3.1, Laplace-domain argument: integration by parts for a
bounded classical trajectory and its bounded continuous velocity.
Only positive-time derivatives and the trace at zero enter the formula. -/
theorem halfLineLaplace_derivative {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (f f' : ℝ → F)
    (hf : ContinuousOn f (Set.Ici (0 : ℝ)))
    (hf' : ContinuousOn f' (Set.Ici (0 : ℝ)))
    (hder : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    {M N : ℝ} (hbound : ∀ t ∈ Set.Ici (0 : ℝ), ‖f t‖ ≤ M)
    (hbound' : ∀ t ∈ Set.Ici (0 : ℝ), ‖f' t‖ ≤ N)
    {s : ℝ} (hs : 0 < s) :
    halfLineLaplace f' s = s • halfLineLaplace f s - f 0 := by
  sorry

end KVApproximation.Analysis
