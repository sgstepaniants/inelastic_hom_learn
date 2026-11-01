module

public import KVApproximation.Spectral.TensorActionIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Interchanging finite-time and tensor-measure integration
-/

public section

open MeasureTheory
open KVApproximation.Tensor

namespace KVApproximation.Spectral

/-- Proposition B.10, memory representation: Fubini for the physical
tensor action and an arbitrary finite scalar measure. -/
theorem integral_tensorActionIntegral_swap {X : Type*} [MeasurableSpace X] {d : ℕ}
    (η : Measure X) [IsFiniteMeasure η] (ν : TensorMeasure d)
    (hνfinite : totalVariation ν Set.univ < ⊤) (f : X → ℝ → Symmetric d)
    (hf : Integrable (Function.uncurry f) (η.prod ν.variation)) :
    (∫ x, tensorActionIntegral ν (f x) ∂η) =
      tensorActionIntegral ν (fun r => ∫ x, f x r ∂η) := by
  sorry

end KVApproximation.Spectral
