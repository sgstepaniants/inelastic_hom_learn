module

public import KVApproximation.Dynamics.Trajectory
public import Mathlib.Topology.ContinuousOn

public section

open MeasureTheory

namespace KVApproximation.Dynamics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Section 4.1 and Lemma B.7: the velocity is bounded almost everywhere
by its essential supremum on the nonnegative time axis. -/
theorem BoundedTrajectory.norm_velocity_ae_le (e : BoundedTrajectory E) :
    ∀ᵐ t ∂timeMeasure, ‖e.velocity t‖ ≤ e.velocityBound := by
  sorry

/-- Lemma B.7 and Appendix B.3: the velocity is integrable on every
finite interval whose endpoints are nonnegative. -/
theorem BoundedTrajectory.velocity_intervalIntegrable (e : BoundedTrajectory E)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable e.velocity volume a b := by
  sorry

/-- Section 4.1 and Lemma B.7: the integral representative has the sharp
Lipschitz bound furnished by its essentially bounded velocity. -/
theorem BoundedTrajectory.norm_value_sub_le (e : BoundedTrajectory E)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖e.value b - e.value a‖ ≤ e.velocityBound * |b - a| := by
  sorry

/-- Section 4.1 and Lemma B.7: the integral representative is continuous
on the closed nonnegative time axis, including the initial time. -/
theorem BoundedTrajectory.continuousOn_value (e : BoundedTrajectory E) :
    ContinuousOn e.value (Set.Ici 0) := by
  sorry

/-- Lemma B.7, integration-by-parts estimate: the value bound holds
pointwise for the integral representative, including time zero. -/
theorem BoundedTrajectory.norm_value_le (e : BoundedTrajectory E)
    {t : ℝ} (ht : 0 ≤ t) : ‖e.value t‖ ≤ e.valueBound := by
  sorry

end KVApproximation.Dynamics
