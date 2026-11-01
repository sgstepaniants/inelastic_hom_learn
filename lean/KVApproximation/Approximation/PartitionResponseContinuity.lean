module

public import KVApproximation.Approximation.PartitionResponse
public import KVApproximation.Approximation.SpectralPartition

/-!
# Continuity of the partitioned interpolant
-/

public section

open KVApproximation.Dynamics

namespace KVApproximation.Approximation

/-- Proposition B.10: the partitioned interpolant is continuous on the
positive spectral interval, with signed Lagrange coefficients. -/
theorem continuousOn_partitionResponse {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c : ℝ) {lower upper : ℝ} (hlower : 0 < lower) (m : ℕ)
    (e : BoundedTrajectory E) (t : ℝ) :
    ContinuousOn (partitionResponse c lower upper m e t) (Set.Icc lower upper) := by
  unfold partitionResponse
  apply continuousOn_finsetSum
  intro j _
  apply (continuousOn_spectralWeight hlower j).smul
  unfold realLocalResponseInterpolant
  apply continuousOn_finsetSum
  intro i _
  exact ((chebyshevLagrange m i).continuous.continuousOn.comp
    ((continuousOn_localCoordinate hlower _ j).mono
      (fun _ hr => hlower.trans_le hr.1)) (Set.mapsTo_univ _ _)).smul continuousOn_const

end KVApproximation.Approximation
