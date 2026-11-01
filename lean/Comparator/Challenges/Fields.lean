module

public import KVApproximation.Tensor.Fields

/-!
# Periodic tensor-field statements
-/

public section

open MeasureTheory Filter
open scoped Topology
open KVApproximation.Analysis

namespace KVApproximation.Tensor

/-- Proposition 3.3, coefficient hypotheses: pointwise and integrated
quadratic-form bounds agree for essentially bounded tensor fields. -/
theorem hasFieldBounds_iff_ae {d : ℕ} {α β : ℝ}
    (A : CoefficientField d ⊤) :
    HasFieldBounds α β A ↔ ∀ᵐ y ∂cellMeasure d, HasBounds α β (A y) := by
  sorry

/-- Lemma B.1 (`lem:strong_conv_tensor`): uniform essential boundedness
and L¹ convergence imply strong convergence of tensor multiplication on L². -/
theorem multiplication_converges {d : ℕ}
    {A : CoefficientField d 1} {Aseq : ℕ → CoefficientField d 1}
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hbounded : ∀ n, eLpNorm (Aseq n) ⊤ (cellMeasure d) ≤ ENNReal.ofReal κ)
    (hconv : Tendsto Aseq atTop (𝓝 A)) :
    MemLp A ⊤ (cellMeasure d) ∧
      eLpNorm A ⊤ (cellMeasure d) ≤ ENNReal.ofReal κ ∧
      ∀ e : StrainField d,
        Tendsto (fun n => eLpNorm
          (fun y => action (Aseq n y - A y) (e y)) 2 (cellMeasure d))
          atTop (𝓝 0) := by
  sorry

end KVApproximation.Tensor
