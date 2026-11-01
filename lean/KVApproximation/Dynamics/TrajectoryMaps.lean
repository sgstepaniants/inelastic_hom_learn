module

public import KVApproximation.Dynamics.TrajectoryBounds

/-!
# Linear maps of bounded trajectories
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Dynamics

/-- Proposition B.13, change of state coordinates: applying a continuous
linear map to both value and velocity preserves the integral trajectory. -/
def BoundedTrajectory.map {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) (q : BoundedTrajectory E) : BoundedTrajectory F where
  value := fun t => A (q.value t)
  velocity := fun t => A (q.velocity t)
  value_memLp := q.value_memLp.continuousLinearMap_comp A
  velocity_memLp := q.velocity_memLp.continuousLinearMap_comp A
  integral_eq := by
    intro t ht
    rw [A.intervalIntegral_comp_comm (q.velocity_intervalIntegrable le_rfl ht),
      ← map_add, q.integral_eq t ht]

end KVApproximation.Dynamics
