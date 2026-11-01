module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Combining two L² fields
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Lemma B.12, material-coordinate step: two L² fields are continuously
equivalent to a single field with a Euclidean product value space. The
ordinary product of L² spaces carries its usual maximum norm. -/
theorem lp_product_coordinates {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (μ : Measure Ω) :
    ∃ U : (Lp E 2 μ × Lp F 2 μ) ≃L[ℝ] Lp (WithLp 2 (E × F)) 2 μ,
      ∀ f : Lp E 2 μ × Lp F 2 μ,
        ∀ᵐ y ∂μ, U f y = WithLp.toLp 2 (f.1 y, f.2 y) := by
  sorry

end KVApproximation.Analysis
