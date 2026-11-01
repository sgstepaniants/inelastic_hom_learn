module

public import KVApproximation.Homogenization.CorrectorSpace

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Proposition 4.7 (`prop:no_spectral_stability`), localized correctors:
each positive-width coordinate strip contains a unit strain corrector
arising from an actual zero-mean periodic displacement. -/
theorem exists_unit_corrector_in_coordinate_strip {d : ℕ} (i : Fin d)
    {a : ℝ} (ha : 0 < a) (ha_one : a ≤ 1) :
    ∃ u : ZeroMeanPeriodicH1 d,
      ∃ η : (correctorSubspace d).toSubmodule,
        (η : StrainField d) = correctorGradientL d u ∧
        ‖η‖ = 1 ∧
        ∀ᵐ y ∂cellMeasure d,
          y ∉ {y : PeriodicCell d |
            0 < cellRepresentative y i ∧ cellRepresentative y i < a} →
            (η : StrainField d) y = 0 := by
  sorry

end KVApproximation.Homogenization
