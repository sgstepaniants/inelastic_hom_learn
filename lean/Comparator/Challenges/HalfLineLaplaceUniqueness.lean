module

public import KVApproximation.Analysis.HalfLineLaplace

public section

namespace KVApproximation.Analysis

/-- Theorem 3.1, injectivity of the time-domain Laplace transform:
positive integer rates determine a bounded continuous scalar trajectory
on the entire nonnegative time axis, including its initial value. -/
theorem eq_zero_of_halfLineLaplace_nat_eq_zero
    (h : ℝ → ℝ) (hcont : ContinuousOn h (Set.Ici (0 : ℝ))) {M : ℝ}
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖h t‖ ≤ M)
    (hmom : ∀ n : ℕ, halfLineLaplace h ((n : ℝ) + 1) = 0) :
    ∀ t : ℝ, 0 ≤ t → h t = 0 := by
  sorry

/-- Theorem 3.1, identification of the homogeneous limit:
bounded continuous Banach-valued trajectories with equal positive-rate
Laplace transforms agree at every nonnegative time. -/
theorem eqOn_of_halfLineLaplace_eq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    (u v : ℝ → F) (hu : ContinuousOn u (Set.Ici (0 : ℝ)))
    (hv : ContinuousOn v (Set.Ici (0 : ℝ))) {Mu Mv : ℝ}
    (huBound : ∀ t : ℝ, 0 ≤ t → ‖u t‖ ≤ Mu)
    (hvBound : ∀ t : ℝ, 0 ≤ t → ‖v t‖ ≤ Mv)
    (hLap : ∀ s : ℝ, 0 < s → halfLineLaplace u s = halfLineLaplace v s) :
    Set.EqOn u v (Set.Ici (0 : ℝ)) := by
  sorry

end KVApproximation.Analysis
