module

public import KVApproximation.Approximation.LogPartition
public import KVApproximation.Approximation.Interpolation
public import KVApproximation.Approximation.WeightedResponse

/-!
# Weighted responses in local spectral coordinates
-/

@[expose] public section

noncomputable section

open KVApproximation.Dynamics

namespace KVApproximation.Approximation

/-- Lemma B.9: the entire extension of the local logarithmic rate map. -/
def complexLocalRate (lower R : ℝ) (j : Fin (logPartitionCount R)) (z : ℂ) : ℂ :=
  lower * Complex.exp (((logPatchLeft R j + logPatchRight R j) / 2 : ℝ) +
    ((logPatchRight R j - logPatchLeft R j) / 2 : ℝ) * z)

/-- Lemma B.9: the weighted response composed with the local rate map. -/
def localWeightedResponse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (J : E →L[ℝ] F) (c lower R : ℝ) (j : Fin (logPartitionCount R))
    (e : BoundedTrajectory E) (t : ℝ) (z : ℂ) : F :=
  weightedResponse J c e t (complexLocalRate lower R j z)

end KVApproximation.Approximation
