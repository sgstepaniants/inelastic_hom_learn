module

public import KVApproximation.Dynamics.DampedResponse

/-!
# Bounded exponential responses and their evolution equation
-/

public section

open MeasureTheory

namespace KVApproximation.Dynamics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Lemma B.11, convolution estimate: the finite-time exponential factor
is retained in the bound for a bounded forcing. -/
theorem norm_dampedResponse_le (v : ℝ → E) {rate M t : ℝ}
    (hrate : 0 < rate) (ht : 0 ≤ t)
    (hbound : ∀ᵐ s ∂timeMeasure, ‖v s‖ ≤ M) :
    ‖dampedResponse rate v t‖ ≤ M * (1 - Real.exp (-rate * t)) / rate := by
  sorry

/-- Proposition B.10, Duhamel formula: locally integrable forcing gives
a continuous response on the nonnegative time axis. -/
theorem continuousOn_dampedResponse (rate : ℝ) (v : ℝ → E)
    (hv : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable v volume 0 t) :
    ContinuousOn (dampedResponse rate v) (Set.Ici 0) := by
  sorry

/-- Proposition B.10 (`eq:q_i_ode`, `eq:q_i_duhamel`): the exponential
convolution satisfies the integral form of the linear evolution equation. -/
theorem dampedResponse_integral_eq (rate : ℝ) (v : ℝ → E)
    (hv : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable v volume 0 t)
    {t : ℝ} (ht : 0 ≤ t) :
    dampedResponse rate v t =
      ∫ s in (0 : ℝ)..t, v s - rate • dampedResponse rate v s := by
  sorry

/-- Proposition B.10: positive damping and essentially bounded forcing
give a bounded Sobolev trajectory with the prescribed convolution values. -/
theorem dampedResponse_trajectory {rate : ℝ} (hrate : 0 < rate)
    (v : ℝ → E) (hv : MemLp v ⊤ timeMeasure) :
    ∃ q : BoundedTrajectory E,
      (∀ t : ℝ, 0 ≤ t → q.value t = dampedResponse rate v t) ∧
      q.value 0 = 0 ∧
      ∀ᵐ t ∂timeMeasure, q.velocity t = v t - rate • q.value t := by
  sorry

end KVApproximation.Dynamics
