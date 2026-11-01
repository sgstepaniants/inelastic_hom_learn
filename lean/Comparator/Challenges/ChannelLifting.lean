module

public import KVApproximation.NeuralOperators.FourierMapping

/-!
# Linear lifting of vector and field inputs
-/

public section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Example 2.1 and Remark 4.3, linear lifting: a pointwise linear map of
the vector and field channels induces a continuous linear map into L². -/
theorem exists_channel_liftingCLM {d vectorInput functionInput width : ℕ}
    (S : WithLp 2 (Channels vectorInput × Channels functionInput) →ₗ[ℝ] Channels width) :
    ∃ A : (Channels vectorInput × ChannelField d functionInput) →L[ℝ]
        ChannelField d width,
      ∀ x : Channels vectorInput × ChannelField d functionInput,
        (A x : PeriodicCell d → Channels width) =ᵐ[cellMeasure d]
          fun y => S (WithLp.toLp 2 (x.1, x.2 y)) := by
  sorry

/-- Remark 4.3, information-preserving lifting: vector and field inputs
admit one injective continuous linear L² realization by the stated pointwise
linear lifting, with finite channel width. -/
theorem exists_injective_channel_lifting (d vectorInput functionInput : ℕ) :
    ∃ width : ℕ,
      ∃ S : WithLp 2 (Channels vectorInput × Channels functionInput) →ₗ[ℝ] Channels width,
        ∃ A : (Channels vectorInput × ChannelField d functionInput) →L[ℝ]
            ChannelField d width,
          Function.Injective A ∧
            ∀ x : Channels vectorInput × ChannelField d functionInput,
              (A x : PeriodicCell d → Channels width) =ᵐ[cellMeasure d]
                fun y => S (WithLp.toLp 2 (x.1, x.2 y)) := by
  sorry

end KVApproximation.NeuralOperators
