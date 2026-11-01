module

public import KVApproximation.Tensor.Fields
public import KVApproximation.Analysis.PeriodicVariation

/-!
# Closed coefficient constraints
-/

public section

open MeasureTheory Filter
open scoped Topology
open KVApproximation.Analysis

namespace KVApproximation.Tensor

/-- Lemma B.2 (`lem:bv_compact`), closedness step: an L¹ limit preserves
the essential boundedness, quadratic-form bounds and full periodic BV bound. -/
theorem coefficient_constraints_of_tendsto_L1 {d : ℕ}
    {A : CoefficientField d 1} {Aseq : ℕ → CoefficientField d 1}
    {α β : ℝ} {C : ENNReal} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hseq : ∀ n, MemLp (Aseq n) ⊤ (cellMeasure d) ∧
      HasFieldBounds α β (Aseq n) ∧ periodicBVNorm (Aseq n) ≤ C)
    (hconv : Tendsto Aseq atTop (𝓝 A)) :
    MemLp A ⊤ (cellMeasure d) ∧ HasFieldBounds α β A ∧ periodicBVNorm A ≤ C := by
  sorry

end KVApproximation.Tensor
