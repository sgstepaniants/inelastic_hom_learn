module

public import KVApproximation.Analysis.PeriodicVariation

/-!
# Variation bounds for periodic strip fields
-/

public section

noncomputable section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Proposition 4.7 (`prop:no_spectral_stability`), constant coefficients:
a constant periodic field has zero distributional variation. -/
theorem periodicVariation_const {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] (c : F) :
    periodicVariation (fun _ : PeriodicCell d => c) = 0 := by
  sorry

/-- Proposition 4.7 (`prop:no_spectral_stability`), uniform strip bound:
adding a constant jump on an open coordinate strip contributes at most
twice its norm to variation, independently of the width and dimension. -/
theorem periodicVariation_const_add_coordinate_strip_le {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (i : Fin d) (c₀ c₁ : F) {a : ℝ} (ha : 0 ≤ a) (ha_one : a ≤ 1) :
    periodicVariation (fun y : PeriodicCell d => c₀ +
      {z : PeriodicCell d | 0 < cellRepresentative z i ∧ cellRepresentative z i < a}.indicator
        (fun _ => c₁) y) ≤ ENNReal.ofReal (2 * ‖c₁‖) := by
  sorry

end KVApproximation.Analysis
