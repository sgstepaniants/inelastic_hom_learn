module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Uniform local averaging of continuous families
-/

public section

noncomputable section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Remark 4.3, Fourier projection ingredient: a single local average
approximates evaluation at a fixed point uniformly over a compact parameter
family. The neighborhood has strictly positive finite measure. -/
theorem exists_uniform_local_average
    {P X E : Type*} [TopologicalSpace P] [CompactSpace P]
    [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (F : C(P × X, E)) (x₀ : X) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ 0 < μ.real (Metric.ball x₀ r) ∧ ∀ p : P,
      ‖(μ.real (Metric.ball x₀ r))⁻¹ •
          (∫ x in Metric.ball x₀ r, F (p, x) ∂μ) - F (p, x₀)‖ < ε := by
  let G : C(X, C(P, E)) := (F.comp ⟨Prod.swap, continuous_swap⟩).curry
  obtain ⟨r, hr, hnear⟩ := Metric.continuousAt_iff.mp
    (G.continuous.continuousAt (x := x₀)) (ε / 2) (half_pos hε)
  have hmass : 0 < μ.real (Metric.ball x₀ r) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos μ x₀ hr).ne' (measure_ne_top _ _)
  refine ⟨r, hr, hmass, ?_⟩
  intro p
  have hpoint (x : X) (hx : x ∈ Metric.ball x₀ r) :
      ‖F (p, x) - F (p, x₀)‖ ≤ ε / 2 := by
    have hdist : dist (F (p, x)) (F (p, x₀)) < ε / 2 :=
      lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist (f := G x) (g := G x₀) p)
        (hnear hx)
    simpa only [dist_eq_norm] using hdist.le
  have hcontinuous : Continuous (fun x : X => F (p, x)) :=
    F.continuous.comp (continuous_const.prodMk continuous_id)
  have hint : Integrable (fun x : X => F (p, x)) μ :=
    hcontinuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hconst : Integrable (fun _ : X => F (p, x₀)) μ := integrable_const _
  have hcenter :
      (∫ x in Metric.ball x₀ r, (F (p, x) - F (p, x₀)) ∂μ) =
        (∫ x in Metric.ball x₀ r, F (p, x) ∂μ) -
          μ.real (Metric.ball x₀ r) • F (p, x₀) := by
    rw [integral_sub hint.restrict hconst.restrict, setIntegral_const]
  have heq : (μ.real (Metric.ball x₀ r))⁻¹ •
      (∫ x in Metric.ball x₀ r, F (p, x) ∂μ) - F (p, x₀) =
        (μ.real (Metric.ball x₀ r))⁻¹ •
          (∫ x in Metric.ball x₀ r, (F (p, x) - F (p, x₀)) ∂μ) := by
    rw [hcenter, smul_sub, smul_smul, inv_mul_cancel₀ hmass.ne', one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmass)]
  calc
    _ ≤ (μ.real (Metric.ball x₀ r))⁻¹ * ((ε / 2) * μ.real (Metric.ball x₀ r)) :=
      mul_le_mul_of_nonneg_left
        (norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) hpoint)
        (inv_nonneg.mpr hmass.le)
    _ = ε / 2 := by rw [mul_left_comm, inv_mul_cancel₀ hmass.ne', mul_one]
    _ < ε := half_lt_self hε

end KVApproximation.Analysis
