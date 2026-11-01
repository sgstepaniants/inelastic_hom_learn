module

public import KVApproximation.Spectral.TensorMeasure
public import KVApproximation.Tensor.LinearAction

/-!
# Tensor-measure action on vector-valued responses
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Spectral

/-- Proposition B.10, memory representation: the tensor-valued measure
acts on a strain-valued integrand by physical tensor contraction. -/
def tensorActionIntegral {d : ℕ} (ν : TensorMeasure d) (f : ℝ → Tensor.Symmetric d) :
    Tensor.Symmetric d :=
  MeasureTheory.VectorMeasure.integral ν f (Tensor.actionL d).flip

end KVApproximation.Spectral
