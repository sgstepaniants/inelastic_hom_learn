module

public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-!
# Scalar tests of vector-measure integrals
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Appendix A.2: a continuous linear scalar test commutes with vector-measure
integration when its values on measurable sets equal a finite scalar measure. -/
theorem integral_scalarization {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (ν : VectorMeasure X F) (φ : F →L[ℝ] ℝ) (μ : Measure X) [IsFiniteMeasure μ]
    (hφ : ∀ s : Set X, MeasurableSet s → φ (ν s) = μ.real s)
    (f : X → ℝ) (hνf : Integrable f ν.variation) (hμf : Integrable f μ) :
    φ (VectorMeasure.integral ν f (ContinuousLinearMap.lsmul ℝ ℝ (E := F))) =
      ∫ x, f x ∂μ := by
  sorry

end KVApproximation.Analysis
