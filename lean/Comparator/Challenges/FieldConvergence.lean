module

public import KVApproximation.Tensor.Multiplication

/-!
# Coefficient norm bounds and strong multiplication convergence
-/

public section

open MeasureTheory Filter
open scoped Topology
open KVApproximation.Analysis

namespace KVApproximation.Tensor

/-- Lemma B.2 (`lem:bv_compact`): integrated positive coefficient bounds
give the paper's essential Frobenius bound. -/
theorem HasFieldBounds.eLpNorm_top_le {d : ℕ} {α β : ℝ}
    (A : CoefficientField d ⊤) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hA : HasFieldBounds α β A) :
    eLpNorm A ⊤ (cellMeasure d) ≤
      ENNReal.ofReal (Real.sqrt (strainDimension d) * β) := by
  sorry

/-- Lemma B.1, as used in Proposition B.3: the actual L² multiplication
operators converge strongly under a common essential bound and L¹ convergence. -/
theorem multiplication_strong_tendsto {d : ℕ}
    (A : CoefficientField d ⊤) (Aseq : ℕ → CoefficientField d ⊤)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hbounded : ∀ n, eLpNorm (Aseq n) ⊤ (cellMeasure d) ≤ ENNReal.ofReal κ)
    (hconv : Tendsto
      (fun n => eLpNorm (fun y => Aseq n y - A y) 1 (cellMeasure d)) atTop (𝓝 0))
    (e : StrainField d) :
    Tendsto (fun n => multiplication (Aseq n) e) atTop (𝓝 (multiplication A e)) := by
  sorry

end KVApproximation.Tensor
