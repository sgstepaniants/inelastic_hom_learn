module

public import KVApproximation.Approximation.WeightedResponse

/-!
# The weighted-response statements
-/

public section

open KVApproximation.Dynamics

namespace KVApproximation.Approximation

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

/-- Lemma B.7 (`lem:weighted_response`), analyticity: the finite-time
response is entire in its complex spectral parameter. -/
theorem weightedResponse_entire (J : E →L[ℝ] F) (c : ℝ)
    (e : BoundedTrajectory E) {t : ℝ} (ht : 0 ≤ t) :
    AnalyticOnNhd ℂ (weightedResponse J c e t) Set.univ := by
  sorry

/-- Lemma B.7 (`eq:weighted_response_bound`): the uniform bound in the
open right half-plane, with the original stress-scale constraint. -/
theorem norm_weightedResponse_le (J : E →ₗᵢ[ℝ] F)
    (e : BoundedTrajectory E) {βE βV δ t : ℝ} {z : ℂ}
    (hβE : 0 < βE) (hβV : 0 < βV)
    (he : e.Admissible βE βV δ) (ht : 0 ≤ t) (hz : 0 < z.re) :
    ‖weightedResponse J.toContinuousLinearMap (βE / βV) e t z‖ ≤
      (1 + ‖z‖ / z.re) * δ / βV := by
  sorry

end KVApproximation.Approximation
