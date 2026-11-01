module

public import KVApproximation.NeuralOperators.FourierMapping

/-!
# Nonlinear lifting into periodic L²
-/

public section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Example 2.1 and Remark 4.3: a globally Lipschitz pointwise lifting
defines a globally Lipschitz map into L² for all vector and L² field inputs.
The global hypothesis supplies the required growth control. -/
theorem exists_lipschitz_channel_lifting {d vectorInput functionInput width : ℕ}
    {S : WithLp 2 (Channels vectorInput × Channels functionInput) → Channels width}
    {K : NNReal} (hS : LipschitzWith K S) :
    ∃ L : NNReal, ∃ A : Channels vectorInput × ChannelField d functionInput → ChannelField d width,
      LipschitzWith L A ∧ ∀ x : Channels vectorInput × ChannelField d functionInput,
        (A x : PeriodicCell d → Channels width) =ᵐ[cellMeasure d]
          fun y => S (WithLp.toLp 2 (x.1, x.2 y)) := by
  sorry

end KVApproximation.NeuralOperators
