module

public import KVApproximation.Approximation.RealResponse

/-!
# Real and complex weighted response contracts
-/

public section

open KVApproximation.Dynamics

namespace KVApproximation.Approximation

/-- Lemma B.7 and Proposition B.10: real-linear embedding of the real
weighted response agrees with the analytic response at real rates. -/
theorem map_realWeightedResponse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (J : E →L[ℝ] F) (c : ℝ) (e : BoundedTrajectory E)
    {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    J (realWeightedResponse c e t r) = weightedResponse J c e t r := by
  sorry

/-- Proposition B.10: the real weighted response is continuous in the
spectral rate for every finite nonnegative time. -/
theorem continuous_realWeightedResponse {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c : ℝ) (e : BoundedTrajectory E) {t : ℝ} (ht : 0 ≤ t) :
    Continuous (realWeightedResponse c e t) := by
  sorry

/-- Proposition B.10, applying Lemma B.9: the real local interpolant has
the exact same error as its complexified counterpart, including one node. -/
theorem real_local_response_error {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : BoundedTrajectory E) {βE βV δ lower R t : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (hR : 0 < R) (ht : 0 ≤ t)
    {m : ℕ} (hm : 1 ≤ m) (j : Fin (logPartitionCount R))
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖realWeightedResponse (βE / βV) e t (localRate lower R j x) -
      realLocalResponseInterpolant (βE / βV) lower R m j e t x‖ ≤
      localResponseErrorBound δ βV m := by
  sorry

end KVApproximation.Approximation
