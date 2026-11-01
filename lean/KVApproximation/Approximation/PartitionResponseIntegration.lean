import KVApproximation.Approximation.PartitionResponseError
import KVApproximation.Spectral.TensorActionIntegration

/-!
# Integrated interpolation error
-/

open MeasureTheory
open KVApproximation.Dynamics KVApproximation.Tensor KVApproximation.Spectral

namespace KVApproximation.Approximation

/-- Proposition B.10: the integrated partition error costs only the
Frobenius total variation of the measure; positivity is unnecessary here. -/
theorem norm_integrated_partition_error_le {d : ℕ}
    (ν : TensorMeasure d) {βE βV δ lower upper t : ℝ}
    (hνfinite : totalVariation ν Set.univ < ⊤)
    (hνsupport : ν.SupportedOn (Set.Icc lower upper))
    (e : BoundedTrajectory (Symmetric d))
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (horder : lower < upper) (ht : 0 ≤ t)
    {m : ℕ} (hm : 1 ≤ m) :
    ‖tensorActionIntegral ν (realWeightedResponse (βE / βV) e t) -
      tensorActionIntegral ν (partitionResponse (βE / βV) lower upper m e t)‖ ≤
      localResponseErrorBound δ βV m * (totalVariation ν Set.univ).toReal := by
  have hW := ν.integrable_continuousOn_vector hνfinite hνsupport _
    (continuous_realWeightedResponse (βE / βV) e ht).continuousOn
  have hp := ν.integrable_continuousOn_vector hνfinite hνsupport _
    (continuousOn_partitionResponse (βE / βV) hlower m e t)
  have hnonneg : 0 ≤ localResponseErrorBound δ βV m :=
    (norm_nonneg _).trans (partition_response_error e hβE hβV he hlower horder ht hm
      (show lower ∈ Set.Icc lower upper from ⟨le_rfl, horder.le⟩))
  rw [tensorActionIntegral, tensorActionIntegral, ← VectorMeasure.integral_sub hW hp]
  apply norm_tensorActionIntegral_le ν hνfinite _ hnonneg
  filter_upwards [ae_iff.mpr hνsupport] with r hr
  exact partition_response_error e hβE hβV he hlower horder ht hm hr

end KVApproximation.Approximation
