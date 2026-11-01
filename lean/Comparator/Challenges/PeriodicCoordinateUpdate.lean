module

public import KVApproximation.Analysis.PeriodicCell

/-!
# Coordinate replacement in normalized cell measure
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Proposition 4.7 (`prop:no_spectral_stability`), periodic slicing:
replacing one torus coordinate by an independent normalized circle
coordinate preserves normalized cell measure. -/
theorem measurePreserving_coordinate_update {d : ℕ} (i : Fin d) :
    MeasurePreserving
      (fun z : PeriodicCell d × UnitAddCircle => Function.update z.1 i z.2)
      ((cellMeasure d).prod (AddCircle.haarAddCircle : Measure UnitAddCircle))
      (cellMeasure d) := by
  sorry

end KVApproximation.Analysis
