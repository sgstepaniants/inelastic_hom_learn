module

public import KVApproximation.Analysis.VectorMeasureIntegral
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# Scalar tests of vector measures with density
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Lemma B.6, scalar tests of the weighted measure: multiplying a vector
measure by an integrable scalar density preserves its scalarization identity. -/
theorem scalarization_withDensity_apply {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (ν : VectorMeasure X F) (φ : F →L[ℝ] ℝ) (μ : Measure X) [IsFiniteMeasure μ]
    (hφ : ∀ s : Set X, MeasurableSet s → φ (ν s) = μ.real s)
    (w : X → ℝ) (hνw : Integrable w ν.variation) (hμw : Integrable w μ)
    (s : Set X) (hs : MeasurableSet s) :
    φ (ν.withDensity w (ContinuousLinearMap.lsmul ℝ ℝ (E := F)) s) =
      ∫ x in s, w x ∂μ := by
  rw [VectorMeasure.withDensity_apply hνw, ← VectorMeasure.integral_indicator hs]
  rw [integral_scalarization ν φ μ hφ (s.indicator w) (hνw.indicator hs) (hμw.indicator hs)]
  exact integral_indicator hs

end KVApproximation.Analysis
