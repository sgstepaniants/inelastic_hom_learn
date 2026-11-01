module

public import KVApproximation.Approximation.LocalResponse
public import KVApproximation.Dynamics.DampedResponse

/-!
# Real weighted relaxation responses
-/

@[expose] public section

noncomputable section

open KVApproximation.Dynamics

namespace KVApproximation.Approximation

/-- Lemma B.7 (`eq:weighted_response_def`) and Proposition B.10: the
weighted response at a real relaxation rate, in the original strain space. -/
def realWeightedResponse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (c : ℝ) (e : BoundedTrajectory E) (t r : ℝ) : E :=
  (c + r) • dampedResponse r e.velocity t

/-- Definition B.8 and Proposition B.10: the real vector-valued Lagrange
interpolant on a logarithmic patch. Its scalar coefficients may have either sign. -/
def realLocalResponseInterpolant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (c lower R : ℝ) (m : ℕ) (j : Fin (logPartitionCount R))
    (e : BoundedTrajectory E) (t x : ℝ) : E :=
  ∑ i : Fin m, (chebyshevLagrange m i).eval x •
    realWeightedResponse c e t (localRate lower R j (chebyshevNode m i))

end KVApproximation.Approximation
