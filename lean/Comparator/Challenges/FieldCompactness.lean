module

public import KVApproximation.Tensor.Fields
public import KVApproximation.Analysis.PeriodicVariation

/-!
# Compactness of coefficient fields
-/

public section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.Tensor

/-- Lemma B.2 (`lem:bv_compact`): the compact L² coefficient class before
taking the product of viscosity and elasticity fields. -/
theorem isCompact_coefficient_constraints {d : ℕ} {α β : ℝ} {C : ENNReal}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hC : C ≠ ⊤) :
    IsCompact {A : CoefficientField d 2 | MemLp A ⊤ (cellMeasure d) ∧
      HasFieldBounds α β A ∧ periodicBVNorm A ≤ C} := by
  sorry

end KVApproximation.Tensor
