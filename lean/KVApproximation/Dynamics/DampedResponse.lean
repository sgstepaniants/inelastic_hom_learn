module

public import KVApproximation.Dynamics.Trajectory
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Exponential response to a measurable forcing
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Dynamics

/-- Proposition B.10 (`eq:q_i_duhamel`): the zero-initial-value response
of a scalar relaxation rate acting on a Banach-valued forcing. -/
def dampedResponse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (rate : ℝ) (v : ℝ → E) (t : ℝ) : E :=
  ∫ s in (0 : ℝ)..t, Real.exp (-rate * (t - s)) • v s

end KVApproximation.Dynamics
