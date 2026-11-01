module

public import KVApproximation.Approximation.AlternativeProny
public import KVApproximation.Approximation.PartitionResponse
public import KVApproximation.Spectral.TensorActionIntegration

/-!
# Unweighted logarithmic interpolation
-/

public section

open MeasureTheory
open KVApproximation.Dynamics KVApproximation.Tensor KVApproximation.Spectral

namespace KVApproximation.Approximation

/-- Remark 4.6: the unweighted response uses only the velocity bound. -/
theorem norm_unweightedResponse_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (J : E →ₗᵢ[ℝ] F) (e : BoundedTrajectory E) {t : ℝ} {z : ℂ}
    (ht : 0 ≤ t) (hz : 0 < z.re) :
    ‖weightedResponse J.toContinuousLinearMap 0 e t z‖ ≤
      ‖z‖ / z.re * e.velocityBound := by
  sorry

/-- Remark 4.6, local Chebyshev estimate without resolvent reweighting. -/
theorem local_unweighted_response_error {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (J : E →ₗᵢ[ℝ] F) (e : BoundedTrajectory E) {βE βV δ lower R t : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (hR : 0 < R) (ht : 0 ≤ t)
    {m : ℕ} (hm : 1 ≤ m) (j : Fin (logPartitionCount R))
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖localWeightedResponse J.toContinuousLinearMap 0 lower R j e t x -
      chebyshevInterpolant m (localWeightedResponse J.toContinuousLinearMap 0 lower R j e t) x‖ ≤
      (4 * δ / (βV * Real.cos (3 / 4))) / (2 : ℝ) ^ (m - 1) := by
  sorry

/-- Remark 4.6: real coordinates preserve the local unweighted error. -/
theorem real_local_unweighted_response_error {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : BoundedTrajectory E) {βE βV δ lower R t : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (hR : 0 < R) (ht : 0 ≤ t)
    {m : ℕ} (hm : 1 ≤ m) (j : Fin (logPartitionCount R))
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖realWeightedResponse 0 e t (localRate lower R j x) -
      realLocalResponseInterpolant 0 lower R m j e t x‖ ≤
      (4 * δ / (βV * Real.cos (3 / 4))) / (2 : ℝ) ^ (m - 1) := by
  sorry

/-- Remark 4.6: nonnegative patch weights preserve the unweighted error constant. -/
theorem partition_unweighted_response_error {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : BoundedTrajectory E) {βE βV δ lower upper t : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (horder : lower < upper) (ht : 0 ≤ t)
    {m : ℕ} (hm : 1 ≤ m) {r : ℝ} (hr : r ∈ Set.Icc lower upper) :
    ‖realWeightedResponse 0 e t r - partitionResponse 0 lower upper m e t r‖ ≤
      (4 * δ / (βV * Real.cos (3 / 4))) / (2 : ℝ) ^ (m - 1) := by
  sorry

/-- Remark 4.6: integration costs the unweighted spectral measure's total variation. -/
theorem norm_integrated_unweighted_partition_error_le {d : ℕ}
    (ν : TensorMeasure d) {βE βV δ lower upper t : ℝ}
    (hνfinite : totalVariation ν Set.univ < ⊤)
    (hνsupport : ν.SupportedOn (Set.Icc lower upper))
    (e : BoundedTrajectory (Symmetric d))
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (horder : lower < upper) (ht : 0 ≤ t)
    {m : ℕ} (hm : 1 ≤ m) :
    ‖tensorActionIntegral ν (realWeightedResponse 0 e t) -
      tensorActionIntegral ν (partitionResponse 0 lower upper m e t)‖ ≤
      ((4 * δ / (βV * Real.cos (3 / 4))) / (2 : ℝ) ^ (m - 1)) *
        (totalVariation ν Set.univ).toReal := by
  sorry

/-- Remark 4.6: the unweighted response integral equals the cell memory convolution. -/
theorem memory_eq_unweightedResponseIntegral {d : ℕ} {lower upper : ℝ}
    (hlower : 0 < lower) (ν : TensorMeasure d) (K : ℝ → Elasticity d)
    (hrep : IsSpectralRepresentation ν K lower upper)
    (e : BoundedTrajectory (Symmetric d)) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, action (K (t - s)) (e.velocity s)) =
      tensorActionIntegral ν (realWeightedResponse 0 e t) := by
  sorry

/-- Remark 4.6: signed unweighted coefficients assemble the partitioned interpolant. -/
theorem unweighted_prony_stress_eq_partitionIntegral {M : Type*} {d : ℕ}
    (ν : M → TensorMeasure d) (Vhom Ehom : M → Elasticity d)
    {lower upper : ℝ} (hlower : 0 < lower) (m : ℕ) (a : M)
    (hνsupport : (ν a).SupportedOn (Set.Icc lower upper))
    (hνfinite : totalVariation (ν a) Set.univ < ⊤)
    (e : BoundedTrajectory (Symmetric d)) {t : ℝ} (ht : 0 ≤ t) :
    (unweightedLocalModel ν Vhom Ehom lower upper m).stress a e t =
      action (Vhom a) (e.velocity t) + action (Ehom a) (e.value t) +
        tensorActionIntegral (ν a) (partitionResponse 0 lower upper m e t) := by
  sorry

end KVApproximation.Approximation
