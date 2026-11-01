module

public import KVApproximation.Approximation.LocalResponse

/-!
# Local interpolation of the weighted response
-/

public section

open KVApproximation.Dynamics

namespace KVApproximation.Approximation

/-- Lemma B.9: the complex rate map extends the real change of variables. -/
theorem complexLocalRate_ofReal (lower R : ℝ)
    (j : Fin (logPartitionCount R)) (x : ℝ) :
    complexLocalRate lower R j x = (localRate lower R j x : ℂ) := by
  sorry

/-- Lemma B.9: the radius-two ellipse maps into the open right half-plane,
with the exact secant bound used in the paper. -/
theorem complexLocalRate_ellipse {lower R : ℝ} (hlower : 0 < lower) (hR : 0 < R)
    (j : Fin (logPartitionCount R)) {z : ℂ} (hz : z ∈ bernsteinEllipse 2) :
    0 < (complexLocalRate lower R j z).re ∧
      ‖complexLocalRate lower R j z‖ / (complexLocalRate lower R j z).re ≤
        (Real.cos (3 / 4))⁻¹ := by
  sorry

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

/-- Lemma B.9 (`eq:chebyshev_interp_bound_iv`): the uniform local error,
including the case of interpolation at a single node. -/
theorem local_weighted_response_error (J : E →ₗᵢ[ℝ] F)
    (e : BoundedTrajectory E) {βE βV δ lower R t : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (hR : 0 < R) (ht : 0 ≤ t)
    {m : ℕ} (hm : 1 ≤ m) (j : Fin (logPartitionCount R))
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖localWeightedResponse J.toContinuousLinearMap (βE / βV) lower R j e t x -
      chebyshevInterpolant m
        (localWeightedResponse J.toContinuousLinearMap (βE / βV) lower R j e t) x‖ ≤
      localResponseErrorBound δ βV m := by
  sorry

end KVApproximation.Approximation
