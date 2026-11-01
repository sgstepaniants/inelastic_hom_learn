module

public import KVApproximation.Approximation.PartitionResponse
public import KVApproximation.Spectral.TensorActionIntegral

/-!
# Partition error and tensor integration contracts
-/

public section

open KVApproximation.Dynamics KVApproximation.Tensor KVApproximation.Spectral

namespace KVApproximation.Approximation

/-- Proposition B.10: the partitioned interpolant is continuous on the
positive spectral interval, with signed Lagrange coefficients. -/
theorem continuousOn_partitionResponse {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c : ℝ) {lower upper : ℝ} (hlower : 0 < lower) (m : ℕ)
    (e : BoundedTrajectory E) (t : ℝ) :
    ContinuousOn (partitionResponse c lower upper m e t) (Set.Icc lower upper) := by
  sorry

/-- Proposition B.10: nonnegative partition weights preserve the local
error constant without any factor counting patches or interpolation nodes. -/
theorem partition_response_error {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : BoundedTrajectory E) {βE βV δ lower upper t : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (horder : lower < upper) (ht : 0 ≤ t)
    {m : ℕ} (hm : 1 ≤ m) {r : ℝ} (hr : r ∈ Set.Icc lower upper) :
    ‖realWeightedResponse (βE / βV) e t r -
      partitionResponse (βE / βV) lower upper m e t r‖ ≤
      localResponseErrorBound δ βV m := by
  sorry

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
  sorry

end KVApproximation.Approximation
