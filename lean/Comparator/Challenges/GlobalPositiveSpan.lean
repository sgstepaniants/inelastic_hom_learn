module

public import KVApproximation.Approximation.GlobalResponse
public import KVApproximation.Spectral.TensorActionIntegration
public import KVApproximation.KelvinVoigt.PronyProblem

/-!
# Global interpolation on every positive logarithmic span
-/

public section

open MeasureTheory
open KVApproximation.Dynamics KVApproximation.Tensor KVApproximation.Spectral

namespace KVApproximation.Approximation

/-- Remark 4.6: the ellipse of parameter `1 + 1/R` keeps the global rate
in the same right-half-plane sector used for local interpolation. -/
theorem complexGlobalLogRate_ellipse_of_span_pos {lower upper : ℝ} (hlower : 0 < lower)
    (hR : 0 < logarithmicSpan lower upper) {z : ℂ}
    (hz : z ∈ bernsteinEllipse (1 + 1 / logarithmicSpan lower upper)) :
    0 < (complexGlobalLogRate lower upper z).re ∧
      ‖complexGlobalLogRate lower upper z‖ / (complexGlobalLogRate lower upper z).re ≤
        (Real.cos (3 / 4))⁻¹ := by
  sorry

/-- Remark 4.6: Chebyshev interpolation on the full logarithmic interval,
with the explicit linear span factor. -/
theorem global_weighted_response_error_of_span_pos {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (J : E →ₗᵢ[ℝ] F) (e : BoundedTrajectory E) {βE βV δ lower upper t : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (hR : 0 < logarithmicSpan lower upper) (ht : 0 ≤ t)
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖globalWeightedResponse J.toContinuousLinearMap (βE / βV) lower upper e t x -
      chebyshevInterpolant n
        (globalWeightedResponse J.toContinuousLinearMap (βE / βV) lower upper e t) x‖ ≤
      (4 * δ / βV * ellipseResponseFactor) * logarithmicSpan lower upper /
        (1 + 1 / logarithmicSpan lower upper) ^ (n - 1) := by
  sorry

/-- Remark 4.6: the real global interpolant inherits the complex error estimate. -/
theorem real_global_response_error_of_span_pos {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : BoundedTrajectory E) {βE βV δ lower upper t : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (horder : lower < upper)
    (hR : 0 < logarithmicSpan lower upper) (ht : 0 ≤ t)
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : r ∈ Set.Icc lower upper) :
    ‖realWeightedResponse (βE / βV) e t r -
      globalResponseInterpolant (βE / βV) lower upper n e t r‖ ≤
      (4 * δ / βV * ellipseResponseFactor) * logarithmicSpan lower upper /
        (1 + 1 / logarithmicSpan lower upper) ^ (n - 1) := by
  sorry

/-- Remark 4.6: integration of the global interpolation error costs only total variation. -/
theorem norm_integrated_global_response_error_le_of_span_pos {d : ℕ}
    (ν : TensorMeasure d) {βE βV δ lower upper t : ℝ}
    (hνfinite : totalVariation ν Set.univ < ⊤)
    (hνsupport : ν.SupportedOn (Set.Icc lower upper))
    (e : BoundedTrajectory (Symmetric d))
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (horder : lower < upper)
    (hR : 0 < logarithmicSpan lower upper) (ht : 0 ≤ t)
    {n : ℕ} (hn : 0 < n) :
    ‖tensorActionIntegral ν (realWeightedResponse (βE / βV) e t) -
      tensorActionIntegral ν (globalResponseInterpolant (βE / βV) lower upper n e t)‖ ≤
      ((4 * δ / βV * ellipseResponseFactor) * logarithmicSpan lower upper /
        (1 + 1 / logarithmicSpan lower upper) ^ (n - 1)) *
          (totalVariation ν Set.univ).toReal := by
  sorry

/-- Remark 4.6, global order selection: the logarithmic ceiling reaches
the prescribed tolerance. The strict analytic estimate leaves a positive margin. -/
theorem globalInterpolationOrder_error_le_of_span_pos {tensorDimension : ℕ}
    (hn : 0 < tensorDimension) {R E : ℝ} (hR : 0 < R) (hE : 0 < E) :
    globalPronyErrorBound tensorDimension 1 R
      (globalInterpolationOrder tensorDimension R E) ≤ E := by
  sorry

end KVApproximation.Approximation

namespace KVApproximation.KelvinVoigt

open KVApproximation.Approximation

variable {d : ℕ} {αV βV γV αE βE γE δ : ℝ}
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hαE : 0 < αE) (hEorder : αE ≤ βE)
variable (C : CellFamily d αV βV γV αE βE γE hαV hαE) (S : SpectralFamily C)

include hVorder hEorder

/-- Remark 4.6: one weighted interpolant on the full logarithmic interval
has error of order `R * (1 + 1/R)^(-(n-1))` for every `R > 0`. -/
theorem global_prony_error_lt_of_span_pos (hd : 0 < d) (hδ : 0 < δ)
    (hspan : 0 < logarithmicSpan (αE / βV) (βE / αV)) {n : ℕ} (hn : 0 < n) :
    uniformPronyError C
      (globalPronyModel S.measure (fun M => (C M).viscosity)
        (fun M => (C M).elasticity) (βE / βV) (αE / βV) (βE / αV) n) δ <
      ENNReal.ofReal (globalPronyErrorBound (strainDimension d) δ
        (logarithmicSpan (αE / βV) (βE / αV)) n) := by
  sorry

end KVApproximation.KelvinVoigt
