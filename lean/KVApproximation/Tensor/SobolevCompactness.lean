module

public import KVApproximation.Analysis.PeriodicSobolevBV
public import KVApproximation.Tensor.FieldCompactness

/-!
# Compact closure of smoother coefficient classes

The common Sobolev bound places the class inside the compact BV constraint
set. Its L² closure is compact even when the Sobolev class itself is not closed.
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
  have hcompact := isCompact_coefficient_constraints (d := d) hα hβ hC
  apply hcompact.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hcompact.isClosed
  intro A hA
  obtain ⟨hAtop, hAbounds, G, hG, hgrad, hbound⟩ := hS A hA
  exact ⟨hAtop, hAbounds,
    (periodicBVNorm_le_sobolevBound hp (hAtop.mono_exponent le_top) hG hgrad).trans hbound⟩

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
  simpa only [hclosed.closure_eq] using
    isCompact_closure_sobolev_coefficients hp hα hβ hC hS

end KVApproximation.Tensor
