module

public import KVApproximation.Spectral.TensorActionIntegral
public import Mathlib.MeasureTheory.VectorMeasure.Prod

/-!
# Scalar and tensor-measure Fubini
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
  let : NormedAddCommGroup (Symmetric d) := (symmetricSubmodule d).normedAddCommGroup
  let : NormedSpace ℝ (Symmetric d) := (symmetricSubmodule d).normedSpace
  let : NormedAddCommGroup (Elasticity d) := (elasticitySubmodule d).normedAddCommGroup
  let : NormedSpace ℝ (Elasticity d) := (elasticitySubmodule d).normedSpace
  let : IsFiniteMeasure ν.variation := ⟨hνfinite⟩
  let : IsFiniteMeasure η.toSignedMeasure.variation := by
    rw [Measure.variation_toSignedMeasure]
    infer_instance
  let B := (actionL d).flip
  let S := (ContinuousLinearMap.lsmul ℝ ℝ (E := Symmetric d)).flip
  have hfi : Integrable (Function.uncurry f)
      (η.toSignedMeasure.variation.prod ν.variation) := by
    rw [Measure.variation_toSignedMeasure]
    exact hf
  have h := VectorMeasure.integral_integral_swap (μ := η.toSignedMeasure) (ν := ν)
    (B := B) (C := S) (A := S) (D := B) hfi (fun x y z => by
      change z • (actionL d y x) = actionL d y (z • x)
      exact (map_smul (actionL d y) z x).symm)
  simpa only [S, B, tensorActionIntegral, VectorMeasure.integral_toSignedMeasure] using h

end KVApproximation.Spectral
