module

public import KVApproximation.Analysis.PeriodicCell

/-!
# Coordinate intervals in the periodic cell
-/

public section

noncomputable section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Proposition 4.7 (`prop:no_spectral_stability`), strip measure:
a representative coordinate carries normalized torus measure to Lebesgue
measure restricted to the fundamental interval `(0,1]`. -/
theorem measurePreserving_cellRepresentative_coordinate {d : ℕ} (i : Fin d) :
    MeasurePreserving (fun y : PeriodicCell d => cellRepresentative y i)
      (cellMeasure d) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  sorry

/-- Proposition 4.7 (`prop:no_spectral_stability`), strip measure:
an open coordinate interval inside the fundamental cell has its usual length.
Empty and reversed intervals are included through `ENNReal.ofReal`. -/
theorem cellMeasure_coordinate_interval {d : ℕ} (i : Fin d)
    (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    cellMeasure d {y : PeriodicCell d | a < cellRepresentative y i ∧
      cellRepresentative y i < b} = ENNReal.ofReal (b - a) := by
  sorry

end KVApproximation.Analysis
