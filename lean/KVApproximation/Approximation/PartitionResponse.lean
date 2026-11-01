module

public import KVApproximation.Approximation.RealResponse

/-!
# Partitioned weighted response
-/

@[expose] public section

noncomputable section

open KVApproximation.Dynamics

namespace KVApproximation.Approximation

/-- Proposition B.10, proof: combine the local real interpolants using
the spectral partition of unity before integration against the weighted measure. -/
def partitionResponse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (c lower upper : ℝ) (m : ℕ)
    (e : BoundedTrajectory E) (t r : ℝ) : E :=
  ∑ j, spectralWeight lower upper j r •
    realLocalResponseInterpolant c lower (logarithmicSpan lower upper) m j e t
      (localCoordinate lower (logarithmicSpan lower upper) j r)

end KVApproximation.Approximation
