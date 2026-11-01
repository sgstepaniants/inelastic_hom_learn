import KVApproximation.Approximation.GlobalCoordinates
import KVApproximation.Approximation.GlobalRateGeometry
import KVApproximation.Approximation.ChebyshevInterpolation
import KVApproximation.Approximation.WeightedResponseBound
import KVApproximation.Approximation.RealResponseIdentities
import KVApproximation.Spectral.TensorActionIntegration

/-!
# Weighted interpolation on the full logarithmic interval
-/

open MeasureTheory
open KVApproximation.Dynamics KVApproximation.Tensor KVApproximation.Spectral

namespace KVApproximation.Approximation

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
  let R := logarithmicSpan lower upper
  let M := δ / βV * ellipseResponseFactor
  have hRpos : 0 < R := hR
  have hρ : 1 < 1 + 1 / R := by linarith [one_div_pos.mpr hRpos]
  have hδ : 0 ≤ δ :=
    (add_nonneg (mul_nonneg hβE.le ENNReal.toReal_nonneg)
      (mul_nonneg hβV.le ENNReal.toReal_nonneg)).trans he
  have hcos : 0 < Real.cos (3 / 4 : ℝ) := by linarith [cos_three_quarters_lower]
  have hM : 0 ≤ M := by dsimp [M, ellipseResponseFactor]; positivity
  have hrate (z : ℂ) : AnalyticAt ℂ (complexGlobalLogRate lower upper) z := by
    unfold complexGlobalLogRate
    fun_prop
  have hweighted := weightedResponse_entire J.toContinuousLinearMap (βE / βV) e ht
  have hanalytic : AnalyticOnNhd ℂ
      (globalWeightedResponse J.toContinuousLinearMap (βE / βV) lower upper e t)
      (bernsteinEllipse (1 + 1 / R)) := by
    intro z _
    exact (hweighted (complexGlobalLogRate lower upper z) (Set.mem_univ _)).comp (hrate z)
  have hbound (z : ℂ) (hz : z ∈ bernsteinEllipse (1 + 1 / R)) :
      ‖globalWeightedResponse J.toContinuousLinearMap (βE / βV) lower upper e t z‖ ≤ M := by
    have hgeom := complexGlobalLogRate_ellipse_of_span_pos hlower hR hz
    calc
      _ ≤ (1 + ‖complexGlobalLogRate lower upper z‖ / (complexGlobalLogRate lower upper z).re) * δ / βV :=
        norm_weightedResponse_le J e hβE hβV he ht hgeom.1
      _ ≤ (1 + (Real.cos (3 / 4))⁻¹) * δ / βV :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (add_le_add le_rfl hgeom.2) hδ) hβV.le
      _ = M := by dsimp [M, ellipseResponseFactor]; ring
  calc
    _ ≤ chebyshevErrorBound M (1 + 1 / R) n :=
      chebyshevInterpolant_error_le hρ hM hn hanalytic hbound x hx
    _ = _ := by
      change 4 * M / (((1 + 1 / R) - 1) * (1 + 1 / R) ^ (n - 1)) =
        (4 * δ / βV * ellipseResponseFactor) * R / (1 + 1 / R) ^ (n - 1)
      dsimp [M]
      field_simp
      ring

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
  let J := TauCeti.Complexification.ofRealLI E
  have hmap (x : ℝ) : J (realWeightedResponse (βE / βV) e t (globalLogRate lower upper x)) =
      globalWeightedResponse J.toContinuousLinearMap (βE / βV) lower upper e t x := by
    rw [globalWeightedResponse, complexGlobalLogRate_ofReal]
    exact map_realWeightedResponse J.toContinuousLinearMap _ e ht _
  have hpoly : J (globalResponseInterpolant (βE / βV) lower upper n e t r) =
      chebyshevInterpolant n
        (globalWeightedResponse J.toContinuousLinearMap (βE / βV) lower upper e t)
          (globalLogCoordinate lower upper r) := by
    simp only [globalResponseInterpolant, chebyshevInterpolant, map_sum, map_smul,
      hmap, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have h := global_weighted_response_error_of_span_pos J e hβE hβV he hlower hR ht hn
    (globalLogCoordinate_mem hlower horder hr)
  rw [← hmap (globalLogCoordinate lower upper r), ← hpoly, ← J.map_sub, J.norm_map,
    globalLogRate_globalLogCoordinate hlower horder (hlower.trans_le hr.1)] at h
  exact h

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
  have hW := ν.integrable_continuousOn_vector hνfinite hνsupport _
    (continuous_realWeightedResponse (βE / βV) e ht).continuousOn
  have hp := ν.integrable_continuousOn_vector hνfinite hνsupport _
    (continuousOn_globalResponseInterpolant (βE / βV) hlower n e t)
  have hnonneg : 0 ≤ (4 * δ / βV * ellipseResponseFactor) * logarithmicSpan lower upper /
      (1 + 1 / logarithmicSpan lower upper) ^ (n - 1) :=
    (norm_nonneg _).trans (real_global_response_error_of_span_pos e hβE hβV he hlower horder hR ht hn
      (show lower ∈ Set.Icc lower upper from ⟨le_rfl, horder.le⟩))
  rw [tensorActionIntegral, tensorActionIntegral, ← VectorMeasure.integral_sub hW hp]
  apply norm_tensorActionIntegral_le ν hνfinite _ hnonneg
  filter_upwards [ae_iff.mpr hνsupport] with r hr
  exact real_global_response_error_of_span_pos e hβE hβV he hlower horder hR ht hn hr

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
  exact global_weighted_response_error_of_span_pos J e hβE hβV he hlower
    (lt_of_lt_of_le zero_lt_one hR) ht hn hx

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
  exact real_global_response_error_of_span_pos e hβE hβV he hlower horder
    (lt_of_lt_of_le zero_lt_one hR) ht hn hr

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
  exact norm_integrated_global_response_error_le_of_span_pos ν hνfinite hνsupport e
    hβE hβV he hlower horder (lt_of_lt_of_le zero_lt_one hR) ht hn

end KVApproximation.Approximation
