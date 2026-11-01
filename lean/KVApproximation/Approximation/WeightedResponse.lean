module

public import KVApproximation.Dynamics.Trajectory
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# The weighted relaxation response
-/

@[expose] public section

noncomputable section

open KVApproximation.Dynamics

namespace KVApproximation.Approximation

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

/-- Lemma B.7 (`eq:weighted_response_def`): the complex weighted response,
with `J` the real-linear embedding into the complexified strain space. -/
def weightedResponse (J : E →L[ℝ] F) (c : ℝ) (e : BoundedTrajectory E)
    (t : ℝ) (z : ℂ) : F :=
  ((c : ℂ) + z) •
    ∫ s in (0 : ℝ)..t, Complex.exp (-z * ((t - s : ℝ) : ℂ)) • J (e.velocity s)

end KVApproximation.Approximation
