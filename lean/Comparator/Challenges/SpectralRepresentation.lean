module

public import KVApproximation.Homogenization.CellOperators
public import KVApproximation.Spectral.Bounds
public import KVApproximation.Spectral.TensorMeasure

/-!
# Spectral representation of the cell memory kernel
-/

public section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.Homogenization

namespace KVApproximation.Spectral

/-- Proposition 3.3 (`prop:spectral_rep`): a positive tensor measure
represents the actual cell memory kernel, with the stated spectral support
and Frobenius total-variation bound. -/
theorem spectral_representation {d : ℕ} (V E : CoerciveField d)
    (C : CellConstitutiveModel V E) {αV βV αE βE : ℝ}
    (hαV : 0 < αV) (hβV : 0 < βV) (hαE : 0 < αE) (hβE : 0 < βE)
    (hV : HasFieldBounds αV βV V.field) (hE : HasFieldBounds αE βE E.field) :
    ∃ ν : TensorMeasure d,
      ν.Positive ∧
      ν.SupportedOn (Set.Icc (lowerRate αE βV) (upperRate βE αV)) ∧
      totalVariation ν Set.univ ≤
        ENNReal.ofReal (spectralVariationBound (strainDimension d) βV βE αE) ∧
      ∀ t : ℝ, 0 ≤ t →
        C.kernel t = tensorIntegral ν (fun r => r * Real.exp (-r * t)) := by
  sorry

end KVApproximation.Spectral
