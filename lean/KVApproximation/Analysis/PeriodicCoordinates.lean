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
  have hrepr : MeasurePreserving
      (fun y : UnitAddCircle => (AddCircle.equivIoc 1 0 y).val)
      (AddCircle.haarAddCircle : Measure UnitAddCircle)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    simpa only [zero_add, Function.comp_def, AddCircle.volume_eq_smul_haarAddCircle,
      ENNReal.ofReal_one, one_smul] using
      (measurePreserving_subtype_coe (μa := (volume : Measure ℝ))
        (s := Set.Ioc (0 : ℝ) (0 + 1)) measurableSet_Ioc).comp
        (AddCircle.measurePreserving_equivIoc (1 : ℝ) (a := 0))
  simpa only [cellRepresentative, cellMeasure, Function.comp_def] using
    hrepr.comp (measurePreserving_eval
      (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) i)

/-- Proposition 4.7 (`prop:no_spectral_stability`), strip measure:
an open coordinate interval inside the fundamental cell has its usual length.
Empty and reversed intervals are included through `ENNReal.ofReal`. -/
theorem cellMeasure_coordinate_interval {d : ℕ} (i : Fin d)
    (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    cellMeasure d {y : PeriodicCell d | a < cellRepresentative y i ∧
      cellRepresentative y i < b} = ENNReal.ofReal (b - a) := by
  have hsub : Set.Ioo a b ⊆ Set.Ioc (0 : ℝ) 1 := fun _ hx =>
    ⟨lt_of_le_of_lt ha hx.1, le_trans hx.2.le hb⟩
  change cellMeasure d
    ((fun y : PeriodicCell d => cellRepresentative y i) ⁻¹' Set.Ioo a b) = _
  calc
    _ = (volume.restrict (Set.Ioc (0 : ℝ) 1)) (Set.Ioo a b) :=
      (measurePreserving_cellRepresentative_coordinate i).measure_preimage
        measurableSet_Ioo.nullMeasurableSet
    _ = volume (Set.Ioo a b) := by
      rw [Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.mpr hsub]
    _ = ENNReal.ofReal (b - a) := Real.volume_Ioo

end KVApproximation.Analysis
