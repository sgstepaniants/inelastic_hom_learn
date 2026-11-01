module

public import KVApproximation.Approximation.GlobalResponse
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Coordinates and continuity on the global spectral interval
-/

public section

open KVApproximation.Dynamics

namespace KVApproximation.Approximation

/-- Remark 4.6: the global logarithmic coordinate maps the spectral interval
into the reference interval. -/
theorem globalLogCoordinate_mem {lower upper r : ℝ} (hlower : 0 < lower)
    (horder : lower < upper) (hr : r ∈ Set.Icc lower upper) :
    globalLogCoordinate lower upper r ∈ Set.Icc (-1 : ℝ) 1 := by
  have hR : 0 < logarithmicSpan lower upper :=
    Real.log_pos ((one_lt_div hlower).mpr horder)
  have ha : 0 ≤ Real.log (r / lower) := Real.log_nonneg ((one_le_div hlower).mpr hr.1)
  have hb : Real.log (r / lower) ≤ logarithmicSpan lower upper :=
    Real.log_le_log (div_pos (hlower.trans_le hr.1) hlower)
      (div_le_div_of_nonneg_right hr.2 hlower.le)
  unfold globalLogCoordinate
  constructor
  · have hdiv : 0 ≤ 2 * Real.log (r / lower) / logarithmicSpan lower upper := by positivity
    linarith
  · have hdiv : 2 * Real.log (r / lower) / logarithmicSpan lower upper ≤ 2 :=
      (div_le_iff₀ hR).mpr (by linarith)
    linarith

/-- Remark 4.6: the global exponential map inverts its logarithmic coordinate. -/
theorem globalLogRate_globalLogCoordinate {lower upper r : ℝ} (hlower : 0 < lower)
    (horder : lower < upper) (hr : 0 < r) :
    globalLogRate lower upper (globalLogCoordinate lower upper r) = r := by
  have hR : 0 < logarithmicSpan lower upper :=
    Real.log_pos ((one_lt_div hlower).mpr horder)
  unfold globalLogRate globalLogCoordinate
  rw [show logarithmicSpan lower upper / 2 *
      (1 + (2 * Real.log (r / lower) / logarithmicSpan lower upper - 1)) =
        Real.log (r / lower) by field_simp; ring]
  rw [Real.exp_log (div_pos hr hlower), mul_div_cancel₀ _ hlower.ne']

/-- Remark 4.6: the global interpolant is continuous on the positive spectral interval. -/
theorem continuousOn_globalResponseInterpolant {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c : ℝ) {lower upper : ℝ} (hlower : 0 < lower) (n : ℕ)
    (e : BoundedTrajectory E) (t : ℝ) :
    ContinuousOn (globalResponseInterpolant c lower upper n e t) (Set.Icc lower upper) := by
  have hcoord : ContinuousOn (globalLogCoordinate lower upper) (Set.Icc lower upper) := by
    intro r hr
    have hlog : ContinuousAt (fun r : ℝ => Real.log (r / lower)) r :=
      (continuousAt_id.div_const lower).log (div_pos (hlower.trans_le hr.1) hlower).ne'
    exact (((continuousAt_const.mul hlog).div_const _).sub continuousAt_const).continuousWithinAt
  unfold globalResponseInterpolant
  apply continuousOn_finsetSum
  intro i _
  exact ((chebyshevLagrange n i).continuous.continuousOn.comp hcoord (Set.mapsTo_univ _ _)).smul
    continuousOn_const

end KVApproximation.Approximation
