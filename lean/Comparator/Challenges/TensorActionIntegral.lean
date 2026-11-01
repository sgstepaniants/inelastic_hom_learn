module

public import KVApproximation.Spectral.TensorActionIntegral

/-!
# Vector-valued tests of the spectral tensor measure
-/

public section

open MeasureTheory
open KVApproximation.Tensor

namespace KVApproximation.Spectral

/-- Proposition B.10: a continuous vector test on the supported compact
spectral interval is integrable against the full Frobenius variation. -/
theorem TensorMeasure.integrable_continuousOn_vector {d : ℕ} {a b : ℝ}
    {F : Type*} [NormedAddCommGroup F] (ν : TensorMeasure d)
    (hfinite : totalVariation ν Set.univ < ⊤) (hsupport : ν.SupportedOn (Set.Icc a b))
    (f : ℝ → F) (hf : ContinuousOn f (Set.Icc a b)) : Integrable f ν.variation := by
  sorry

/-- Proposition B.10, coefficient assembly: a fixed strain commutes with
the scalar test integral and the tensor action. -/
theorem tensorActionIntegral_smul {d : ℕ} (ν : TensorMeasure d)
    (f : ℝ → ℝ) (hf : Integrable f ν.variation) (e : Symmetric d) :
    tensorActionIntegral ν (fun r => f r • e) = action (tensorIntegral ν f) e := by
  sorry

/-- Proposition B.10, error estimate: tensor contraction has norm at most
one, so integration costs only the Frobenius total variation. -/
theorem norm_tensorActionIntegral_le {d : ℕ} (ν : TensorMeasure d)
    (hfinite : totalVariation ν Set.univ < ⊤) (f : ℝ → Symmetric d)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ r ∂ν.variation, ‖f r‖ ≤ C) :
    ‖tensorActionIntegral ν f‖ ≤ C * (totalVariation ν Set.univ).toReal := by
  sorry

/-- Proposition B.10, weighted memory representation: the resolvent
weight passes from the tensor measure to a continuous vector-valued test. -/
theorem weightedMeasure_actionIntegral {d : ℕ} {lower upper c : ℝ}
    (hlower : 0 < lower) (hc : 0 < c) (ν : TensorMeasure d)
    (hνpos : ν.Positive) (hνsupport : ν.SupportedOn (Set.Icc lower upper))
    (hνfinite : totalVariation ν Set.univ < ⊤)
    (f : ℝ → Symmetric d) (hf : ContinuousOn f (Set.Icc lower upper)) :
    tensorActionIntegral (weightedMeasure c ν) f =
      tensorActionIntegral ν (fun r => resolventWeight c r • f r) := by
  sorry

end KVApproximation.Spectral
