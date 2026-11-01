module

public import KVApproximation.NeuralOperators.FourierMapping
public import Mathlib.Topology.ContinuousMap.Compact

public section

noncomputable section

open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Remark 4.3, compact-family observation: one finite Fourier projection
approximates evaluation uniformly on a jointly continuous compact family. -/
theorem exists_fourierProjection_approx_eval
    {P : Type*} [TopologicalSpace P] [CompactSpace P] {d n : ℕ}
    (F : C(P × PeriodicCell d, Channels n)) (y₀ : PeriodicCell d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : FourierProjection d n n, ∀ p : P,
      ‖Q.eval (fun y => F (p, y)) - F (p, y₀)‖ < ε := by
  sorry

end KVApproximation.NeuralOperators
