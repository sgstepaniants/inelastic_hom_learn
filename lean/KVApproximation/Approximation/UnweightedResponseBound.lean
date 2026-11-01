module

public import KVApproximation.Approximation.WeightedResponse
public import KVApproximation.Analysis.ExponentialIntegralBounds
public import KVApproximation.Dynamics.TrajectoryBounds

/-!
# The unweighted response in the right half-plane
-/

public section

open MeasureTheory
open KVApproximation.Dynamics KVApproximation.Analysis

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
  let q := ∫ s in (0 : ℝ)..t, Complex.exp (-z * ((t - s : ℝ) : ℂ)) • J (e.velocity s)
  have hvelocity : 0 ≤ e.velocityBound := ENNReal.toReal_nonneg
  have hvbound : ∀ᵐ s ∂volume.restrict (Set.Ioc 0 t), ‖J (e.velocity s)‖ ≤ e.velocityBound := by
    have h := ae_restrict_of_ae_restrict_of_subset
      (show Set.Ioc 0 t ⊆ Set.Ici 0 from fun _ hs => hs.1.le) e.norm_velocity_ae_le
    simpa only [J.norm_map] using h
  have hq : ‖q‖ ≤ e.velocityBound / z.re := by
    calc
      ‖q‖ ≤ e.velocityBound * (1 - Real.exp (-z.re * t)) / z.re :=
        norm_exponential_integral_le (fun s => J (e.velocity s)) ht hz hvbound
      _ ≤ e.velocityBound / z.re := by
        apply div_le_div_of_nonneg_right _ hz.le
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (sub_le_self 1 (Real.exp_pos _).le) hvelocity
  simp only [weightedResponse, Complex.ofReal_zero, zero_add]
  change ‖z • q‖ ≤ _
  calc
    ‖z • q‖ = ‖z‖ * ‖q‖ := norm_smul _ _
    _ ≤ ‖z‖ * (e.velocityBound / z.re) := mul_le_mul_of_nonneg_left hq (norm_nonneg _)
    _ = _ := by ring

end KVApproximation.Approximation
