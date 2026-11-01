module

public import KVApproximation.Approximation.AlternativeProny
public import KVApproximation.Approximation.RealResponse

/-!
# Responses on one logarithmic spectral interval
-/

@[expose] public section

noncomputable section

open KVApproximation.Dynamics

namespace KVApproximation.Approximation

/-- Remark 4.6: the entire extension of the global logarithmic rate map. -/
def complexGlobalLogRate (lower upper : ℝ) (z : ℂ) : ℂ :=
  lower * Complex.exp ((logarithmicSpan lower upper / 2 : ℝ) * (1 + z))

/-- Remark 4.6: the weighted response in the global reference coordinate. -/
def globalWeightedResponse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (J : E →L[ℝ] F) (c lower upper : ℝ) (e : BoundedTrajectory E)
    (t : ℝ) (z : ℂ) : F :=
  weightedResponse J c e t (complexGlobalLogRate lower upper z)

/-- Remark 4.6: the real interpolant at a spectral rate, with one global set of nodes. -/
def globalResponseInterpolant {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c lower upper : ℝ) (n : ℕ) (e : BoundedTrajectory E) (t r : ℝ) : E :=
  ∑ i : Fin n, (chebyshevLagrange n i).eval (globalLogCoordinate lower upper r) •
    realWeightedResponse c e t (globalLogRate lower upper (chebyshevNode n i))

end KVApproximation.Approximation
