module

public import KVApproximation.Analysis.PeriodicCell
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Coordinate replacement in normalized cell measure
-/

public section

noncomputable section

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
  let U : PeriodicCell d × UnitAddCircle →+ PeriodicCell d :=
    { toFun := fun z => Function.update z.1 i z.2
      map_zero' := by
        funext j
        by_cases hj : j = i <;> simp [Function.update, hj]
      map_add' := by
        intro z w
        funext j
        by_cases hj : j = i <;> simp [Function.update, hj] }
  have hcont : Continuous U := continuous_update i
  have hsurj : Function.Surjective U := by
    intro y
    exact ⟨(y, y i), Function.update_eq_self i y⟩
  have : (cellMeasure d).IsAddHaarMeasure := by
    unfold cellMeasure
    infer_instance
  exact U.measurePreserving hcont hsurj (by simp)

end KVApproximation.Analysis
