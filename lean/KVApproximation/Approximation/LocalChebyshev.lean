import KVApproximation.Approximation.LocalRateGeometry
import KVApproximation.Approximation.ChebyshevInterpolation
import KVApproximation.Approximation.WeightedResponseAnalytic
import KVApproximation.Approximation.WeightedResponseBound

/-!
# Local Chebyshev approximation of the weighted response
-/

open KVApproximation.Dynamics

namespace KVApproximation.Approximation

-- Use the scalar structures of the independent interpolation interface.
attribute [local instance 2000] NormedField.toNormedCommRing
attribute [local instance 3000] Real.normedCommRing

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
  let M := δ / βV * ellipseResponseFactor
  have hδ : 0 ≤ δ :=
    (add_nonneg (mul_nonneg hβE.le ENNReal.toReal_nonneg)
      (mul_nonneg hβV.le ENNReal.toReal_nonneg)).trans he
  have hcos : 0 ≤ Real.cos (3 / 4 : ℝ) := by linarith [cos_three_quarters_lower]
  have hM : 0 ≤ M :=
    mul_nonneg (div_nonneg hδ hβV.le) (add_nonneg zero_le_one (inv_nonneg.mpr hcos))
  have hrate (z : ℂ) : AnalyticAt ℂ (complexLocalRate lower R j) z := by
    unfold complexLocalRate
    fun_prop
  have hweighted := weightedResponse_entire J.toContinuousLinearMap (βE / βV) e ht
  have hanalytic : AnalyticOnNhd ℂ
      (localWeightedResponse J.toContinuousLinearMap (βE / βV) lower R j e t)
      (bernsteinEllipse 2) := by
    intro z _
    exact (hweighted (complexLocalRate lower R j z) (Set.mem_univ _)).comp (hrate z)
  have hbound (z : ℂ) (hz : z ∈ bernsteinEllipse 2) :
      ‖localWeightedResponse J.toContinuousLinearMap (βE / βV) lower R j e t z‖ ≤ M := by
    have hgeom := complexLocalRate_ellipse hlower hR j hz
    calc
      _ ≤ (1 + ‖complexLocalRate lower R j z‖ / (complexLocalRate lower R j z).re) * δ / βV :=
        norm_weightedResponse_le J e hβE hβV he ht hgeom.1
      _ ≤ (1 + (Real.cos (3 / 4))⁻¹) * δ / βV :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (add_le_add le_rfl hgeom.2) hδ) hβV.le
      _ = M := by dsimp only [M, ellipseResponseFactor]; ring
  calc
    _ ≤ chebyshevErrorBound M 2 m :=
      chebyshevInterpolant_error_le (by norm_num) hM (lt_of_lt_of_le Nat.zero_lt_one hm)
        hanalytic hbound x hx
    _ = localResponseErrorBound δ βV m := by
      unfold chebyshevErrorBound localResponseErrorBound
      dsimp only [M]
      norm_num
      ring

end KVApproximation.Approximation
