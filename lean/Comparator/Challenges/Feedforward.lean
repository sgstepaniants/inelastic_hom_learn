module

public import KVApproximation.NeuralOperators.Feedforward
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Regularity of finite feedforward networks
-/

public section

namespace KVApproximation.NeuralOperators

/-- Example 2.1 and Remarks 4.2–4.3: globally Lipschitz activations give a
globally Lipschitz finite feedforward network on its full input space. -/
theorem Feedforward.lipschitz {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {output : ℕ} (P : Feedforward E output) {σ : ℝ → ℝ} {K : NNReal}
    (hσ : LipschitzWith K σ) : ∃ L : NNReal, LipschitzWith L (P.eval σ) := by
  sorry

/-- Remarks 4.2–4.3: locally Lipschitz activations suffice for the
finite-dimensional feedforward output map to be locally Lipschitz. -/
theorem Feedforward.locallyLipschitz {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {output : ℕ} (P : Feedforward E output) {σ : ℝ → ℝ}
    (hσ : LocallyLipschitz σ) : LocallyLipschitz (P.eval σ) := by
  sorry

end KVApproximation.NeuralOperators
