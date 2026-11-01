module

public import KVApproximation.Approximation.GlobalResponse
public import KVApproximation.Spectral.TensorActionIntegration

/-!
# One global logarithmic interpolant
-/

public section

open MeasureTheory
open KVApproximation.Dynamics KVApproximation.Tensor KVApproximation.Spectral

namespace KVApproximation.Approximation

/-- Remark 4.6: the complex global rate restricts to the real rate. -/
theorem complexGlobalLogRate_ofReal (lower upper x : ℝ) :
    complexGlobalLogRate lower upper x = (globalLogRate lower upper x : ℂ) := by
  sorry

/-- Remark 4.6: the global logarithmic coordinate maps the spectral interval
into the reference interval. -/
theorem globalLogCoordinate_mem {lower upper r : ℝ} (hlower : 0 < lower)
    (horder : lower < upper) (hr : r ∈ Set.Icc lower upper) :
    globalLogCoordinate lower upper r ∈ Set.Icc (-1 : ℝ) 1 := by
  sorry

/-- Remark 4.6: the global exponential map inverts its logarithmic coordinate. -/
theorem globalLogRate_globalLogCoordinate {lower upper r : ℝ} (hlower : 0 < lower)
    (horder : lower < upper) (hr : 0 < r) :
    globalLogRate lower upper (globalLogCoordinate lower upper r) = r := by
  sorry

/-- Remark 4.6: the ellipse of parameter `1 + 1/R` keeps the global rate
in the same right-half-plane sector used for local interpolation. -/
theorem complexGlobalLogRate_ellipse {lower upper : ℝ} (hlower : 0 < lower)
    (hR : 1 ≤ logarithmicSpan lower upper) {z : ℂ}
    (hz : z ∈ bernsteinEllipse (1 + 1 / logarithmicSpan lower upper)) :
    0 < (complexGlobalLogRate lower upper z).re ∧
      ‖complexGlobalLogRate lower upper z‖ / (complexGlobalLogRate lower upper z).re ≤
        (Real.cos (3 / 4))⁻¹ := by
  sorry

/-- Remark 4.6: Chebyshev interpolation on the full logarithmic interval,
with the explicit linear span factor. -/
theorem global_weighted_response_error {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (J : E →ₗᵢ[ℝ] F) (e : BoundedTrajectory E) {βE βV δ lower upper t : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (hR : 1 ≤ logarithmicSpan lower upper) (ht : 0 ≤ t)
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖globalWeightedResponse J.toContinuousLinearMap (βE / βV) lower upper e t x -
      chebyshevInterpolant n
        (globalWeightedResponse J.toContinuousLinearMap (βE / βV) lower upper e t) x‖ ≤
      (4 * δ / βV * ellipseResponseFactor) * logarithmicSpan lower upper /
        (1 + 1 / logarithmicSpan lower upper) ^ (n - 1) := by
  sorry

/-- Remark 4.6: the real global interpolant inherits the complex error estimate. -/
theorem real_global_response_error {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : BoundedTrajectory E) {βE βV δ lower upper t : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (horder : lower < upper)
    (hR : 1 ≤ logarithmicSpan lower upper) (ht : 0 ≤ t)
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : r ∈ Set.Icc lower upper) :
    ‖realWeightedResponse (βE / βV) e t r -
      globalResponseInterpolant (βE / βV) lower upper n e t r‖ ≤
      (4 * δ / βV * ellipseResponseFactor) * logarithmicSpan lower upper /
        (1 + 1 / logarithmicSpan lower upper) ^ (n - 1) := by
  sorry

/-- Remark 4.6: the global interpolant is continuous on the positive spectral interval. -/
theorem continuousOn_globalResponseInterpolant {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c : ℝ) {lower upper : ℝ} (hlower : 0 < lower) (n : ℕ)
    (e : BoundedTrajectory E) (t : ℝ) :
    ContinuousOn (globalResponseInterpolant c lower upper n e t) (Set.Icc lower upper) := by
  sorry

/-- Remark 4.6: integration of the global interpolation error costs only total variation. -/
theorem norm_integrated_global_response_error_le {d : ℕ}
    (ν : TensorMeasure d) {βE βV δ lower upper t : ℝ}
    (hνfinite : totalVariation ν Set.univ < ⊤)
    (hνsupport : ν.SupportedOn (Set.Icc lower upper))
    (e : BoundedTrajectory (Symmetric d))
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (horder : lower < upper)
    (hR : 1 ≤ logarithmicSpan lower upper) (ht : 0 ≤ t)
    {n : ℕ} (hn : 0 < n) :
    ‖tensorActionIntegral ν (realWeightedResponse (βE / βV) e t) -
      tensorActionIntegral ν (globalResponseInterpolant (βE / βV) lower upper n e t)‖ ≤
      ((4 * δ / βV * ellipseResponseFactor) * logarithmicSpan lower upper /
        (1 + 1 / logarithmicSpan lower upper) ^ (n - 1)) *
          (totalVariation ν Set.univ).toReal := by
  sorry

/-- Remark 4.6: the global Prony coefficients assemble the weighted interpolant. -/
theorem global_prony_stress_eq_responseIntegral {M : Type*} {d : ℕ}
    (ν : M → TensorMeasure d) (Vhom Ehom : M → Elasticity d)
    {c lower upper : ℝ} (hlower : 0 < lower) (hc : 0 < c) (n : ℕ) (a : M)
    (hνpos : (ν a).Positive) (hνsupport : (ν a).SupportedOn (Set.Icc lower upper))
    (hνfinite : totalVariation (ν a) Set.univ < ⊤)
    (e : BoundedTrajectory (Symmetric d)) {t : ℝ} (ht : 0 ≤ t) :
    (globalPronyModel ν Vhom Ehom c lower upper n).stress a e t =
      action (Vhom a) (e.velocity t) + action (Ehom a) (e.value t) +
        tensorActionIntegral (weightedMeasure c (ν a))
          (globalResponseInterpolant c lower upper n e t) := by
  sorry

end KVApproximation.Approximation
