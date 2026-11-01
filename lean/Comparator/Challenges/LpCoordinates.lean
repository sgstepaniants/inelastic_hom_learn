module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Isometric coordinates for coefficient fields
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Lemma B.12, material-coordinate step: a value-space linear isometry
induces an Lp linear isometry, acting pointwise almost everywhere. This
also covers infinite measures and `p = ∞`. -/
theorem lp_coordinates {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure Ω) (p : ENNReal) [Fact (1 ≤ p)] (T : E ≃ₗᵢ[ℝ] F) :
    ∃ U : Lp E p μ ≃ₗᵢ[ℝ] Lp F p μ,
      ∀ f : Lp E p μ, ∀ᵐ y ∂μ, U f y = T (f y) := by
  sorry

end KVApproximation.Analysis
