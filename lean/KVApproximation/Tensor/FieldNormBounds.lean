module

public import KVApproximation.Tensor.FieldBounds
public import KVApproximation.Tensor.ActionBounds

/-!
# Essential Frobenius bounds for coefficient fields
-/

public section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.Tensor

/-- Lemma B.2 (`lem:bv_compact`): integrated positive coefficient bounds
give the paper's essential Frobenius bound. -/
theorem HasFieldBounds.eLpNorm_top_le {d : ℕ} {α β : ℝ}
    (A : CoefficientField d ⊤) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hA : HasFieldBounds α β A) :
    eLpNorm A ⊤ (cellMeasure d) ≤
      ENNReal.ofReal (Real.sqrt (strainDimension d) * β) := by
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable A)]
  apply eLpNormEssSup_le_of_ae_bound
  exact ((hasFieldBounds_iff_ae A).mp hA).mono
    fun _ hy => hy.norm_le_sqrt_dimension hα hβ

end KVApproximation.Tensor
