module

public import KVApproximation.Analysis.PeriodicDistributionalGradient
public import KVApproximation.Tensor.Fields
public import Mathlib.Topology.Compactness.Compact

/-!
# Compact closure of smoother coefficient classes
-/

public section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.Tensor

/-- Remark 4.1 (Bounded Variation): a uniformly bounded periodic W¹,p
coefficient class with common L∞ and ellipticity bounds has compact L²
closure. This includes p=1; no closedness of a Sobolev sublevel is asserted. -/
theorem isCompact_closure_sobolev_coefficients {d : ℕ} {p C : ENNReal}
    {α β : ℝ} {S : Set (CoefficientField d 2)}
    (hp : 1 ≤ p) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hC : C ≠ ⊤)
    (hS : ∀ A ∈ S, MemLp A ⊤ (cellMeasure d) ∧ HasFieldBounds α β A ∧
      ∃ G : PeriodicCell d → PiLp 2 (fun _ : Fin d => Elasticity d),
        MemLp G p (cellMeasure d) ∧ HasPeriodicDistributionalGradient A G ∧
          eLpNorm A p (cellMeasure d) + eLpNorm G p (cellMeasure d) ≤ C) :
    IsCompact (closure S) := by
  sorry

/-- Remark 4.1 (Bounded Variation): a closed smoother coefficient class
with the same uniform Sobolev and coefficient bounds is compact in L². -/
theorem isCompact_sobolev_coefficients_of_isClosed {d : ℕ} {p C : ENNReal}
    {α β : ℝ} {S : Set (CoefficientField d 2)}
    (hp : 1 ≤ p) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hC : C ≠ ⊤) (hclosed : IsClosed S)
    (hS : ∀ A ∈ S, MemLp A ⊤ (cellMeasure d) ∧ HasFieldBounds α β A ∧
      ∃ G : PeriodicCell d → PiLp 2 (fun _ : Fin d => Elasticity d),
        MemLp G p (cellMeasure d) ∧ HasPeriodicDistributionalGradient A G ∧
          eLpNorm A p (cellMeasure d) + eLpNorm G p (cellMeasure d) ≤ C) :
    IsCompact S := by
  sorry

end KVApproximation.Tensor
