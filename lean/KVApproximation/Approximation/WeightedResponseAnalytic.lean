module

public import KVApproximation.Approximation.WeightedResponse
public import KVApproximation.Analysis.FiniteLaplace
public import KVApproximation.Dynamics.TrajectoryBounds

/-!
# Analyticity of the weighted relaxation response
-/

public section

open MeasureTheory
open KVApproximation.Dynamics KVApproximation.Analysis

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
  have hv := e.velocity_intervalIntegrable le_rfl ht
  have hJ : IntervalIntegrable (fun s => J (e.velocity s)) volume 0 t :=
    ⟨J.integrable_comp hv.1, J.integrable_comp hv.2⟩
  exact (analyticOnNhd_const.add analyticOnNhd_id).smul
    (finiteLaplace_entire (fun s => J (e.velocity s)) ht hJ)

end KVApproximation.Approximation
