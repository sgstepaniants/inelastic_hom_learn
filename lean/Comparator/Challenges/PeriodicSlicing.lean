module

public import KVApproximation.Analysis.PeriodicSmooth
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Coordinate slices of periodic derivatives
-/

public section

noncomputable section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Proposition 4.7 (`prop:no_spectral_stability`), strip variation:
integration of a periodic coordinate derivative over an open strip gives
the difference of its two face traces in the normal direction and zero
in every transverse direction. Cell measure is normalized. -/
theorem PeriodicC1.integral_coordinate_strip_partial
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (φ : PeriodicC1 d F) (i j : Fin d) {a : ℝ} (ha : 0 ≤ a) (ha_one : a ≤ 1) :
    (∫ y in {y : PeriodicCell d | 0 < cellRepresentative y i ∧ cellRepresentative y i < a},
      φ.partial j y ∂cellMeasure d) =
      if j = i then
        ∫ y : PeriodicCell d,
          (φ.value (Function.update y i (a : UnitAddCircle)) -
            φ.value (Function.update y i (0 : UnitAddCircle))) ∂cellMeasure d
      else 0 := by
  sorry

/-- Proposition 4.7 (`prop:no_spectral_stability`), strip variation:
the integrated derivative is bounded by the two boundary traces, with
no factor depending on the dimension or strip width. -/
theorem PeriodicC1.norm_integral_coordinate_strip_partial_le
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (φ : PeriodicC1 d F) (i j : Fin d) {a M : ℝ}
    (ha : 0 ≤ a) (ha_one : a ≤ 1) (hφ : ∀ y, ‖φ.value y‖ ≤ M) :
    ‖∫ y in {y : PeriodicCell d | 0 < cellRepresentative y i ∧ cellRepresentative y i < a},
      φ.partial j y ∂cellMeasure d‖ ≤ 2 * M := by
  sorry

end KVApproximation.Analysis
