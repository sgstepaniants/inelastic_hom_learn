module

public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-!
# Scalar tests of vector-measure integrals

Equality of scalar tests on measurable sets extends to integrable functions.
The transpose formulation of the vector integral makes the common set function
explicit; both integrability hypotheses are retained.
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
  let D : ℝ →L[ℝ] F →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ F F ℝ φ).comp (ContinuousLinearMap.lsmul ℝ ℝ)
  let S : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  have htranspose : ν.transpose D = μ.toSignedMeasure.transpose S := by
    apply VectorMeasure.ext
    intro s hs
    apply ContinuousLinearMap.ext
    intro r
    change φ (r • ν s) = μ.toSignedMeasure s • r
    rw [map_smul, hφ s hs, Measure.toSignedMeasure_apply_measurable hs]
    exact mul_comm _ _
  have hsigned : μ.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hμf
  calc
    _ = VectorMeasure.integral ν f D :=
      VectorMeasure.continuousLinearMap_apply_integral
        (μ := ν) (B := ContinuousLinearMap.lsmul ℝ ℝ (E := F)) (C := φ) hνf
    _ = VectorMeasure.integral μ.toSignedMeasure f S := by
      rw [VectorMeasure.integral_eq_setToFun_transpose (μ := ν) (B := D) hνf,
        VectorMeasure.integral_eq_setToFun_transpose (μ := μ.toSignedMeasure) (B := S) hsigned]
      simp only [htranspose]
    _ = _ := VectorMeasure.integral_toSignedMeasure

end KVApproximation.Analysis
