module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Composition on Lp over a finite measure space
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Example 2.1 and Remark 4.3, activation ingredient: a globally Lipschitz
map acts on Lp over a finite measure space with the same Lipschitz constant.
The map need not fix zero. -/
theorem exists_lipschitz_compositionLp
    {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (μ : Measure X) [IsFiniteMeasure μ] (p : ENNReal) [Fact (1 ≤ p)]
    {g : E → F} {K : NNReal} (hg : LipschitzWith K g) :
    ∃ G : Lp E p μ → Lp F p μ, LipschitzWith K G ∧
      ∀ f : Lp E p μ, (G f : X → F) =ᵐ[μ] fun x => g (f x) := by
  sorry

end KVApproximation.Analysis
