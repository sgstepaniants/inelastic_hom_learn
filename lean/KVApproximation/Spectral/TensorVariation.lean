module

public import KVApproximation.Spectral.TensorMeasure
public import KVApproximation.Tensor.FormRepresentation

/-!
# Variation of positive tensor measures

The trace bounds the Frobenius norm on every part of a finite measurable
partition. Finite additivity then bounds the variation by the trace of the mass.
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Tensor
open scoped ENNReal

namespace KVApproximation.Spectral

/-- Appendix A.2: the physical-index trace is a continuous linear functional. -/
private def tensorTraceL (d : ℕ) : Elasticity d →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := tensorTrace
      map_add' := by
        intro A B
        simp [tensorTrace, Finset.sum_add_distrib]
      map_smul' := by
        intro r A
        simp [tensorTrace, Finset.mul_sum] }

/-- Appendix A.2: partition sums of a positive tensor measure are bounded
by the trace of its mass, giving the Frobenius total-variation bound. -/
theorem TensorMeasure.variation_le_trace {d : ℕ} (ν : TensorMeasure d) (hν : ν.Positive)
    {B : Set ℝ} (hB : MeasurableSet B) :
    totalVariation ν B ≤ ENNReal.ofReal (tensorTrace (ν B)) := by
  classical
  simp only [totalVariation, VectorMeasure.variation, preVariation,
    VectorMeasure.ennrealToMeasure_apply hB, ennrealPreVariation_apply, preVariationFun,
    hB, dite_true, iSup_le_iff]
  intro P
  have hnonneg (p : Subtype (MeasurableSet : Set ℝ → Prop)) :
      0 ≤ tensorTrace (ν p.val) :=
    (norm_nonneg _).trans (norm_le_tensorTrace _ (hν p.val p.property))
  have hsum : (∑ p ∈ P.parts, tensorTrace (ν p.val)) = tensorTrace (ν B) := by
    change (∑ p ∈ P.parts, tensorTraceL d (ν p.val)) = tensorTraceL d (ν B)
    rw [← map_sum, ν.sum_finpartition P]
  calc
    (∑ p ∈ P.parts, ‖ν p.val‖ₑ) ≤
        ∑ p ∈ P.parts, ENNReal.ofReal (tensorTrace (ν p.val)) := by
      apply Finset.sum_le_sum
      intro p _
      simpa only [ofReal_norm] using
        ENNReal.ofReal_le_ofReal (norm_le_tensorTrace _ (hν p.val p.property))
    _ = ENNReal.ofReal (∑ p ∈ P.parts, tensorTrace (ν p.val)) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro p _
      exact hnonneg p
    _ = _ := by rw [hsum]

end KVApproximation.Spectral
