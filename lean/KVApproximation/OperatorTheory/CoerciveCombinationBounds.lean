module

public import KVApproximation.OperatorTheory.CoerciveCombinations

/-!
# Energy bounds for positive form combinations
-/

public section

namespace KVApproximation.OperatorTheory

/-- Theorem 3.1 and Lemma B.6: the positive linear combination preserves
the corresponding linear combinations of lower and upper energy bounds. -/
theorem CoerciveForm.addScaled_bounds
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (V E : CoerciveForm H) (c : ℝ) (hc : 0 ≤ c) {αV βV αE βE : ℝ}
    (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE) :
    (V.addScaled E c hc).HasBounds (αV + c * αE) (βV + c * βE) := by
  intro u
  change (αV + c * αE) * ‖u‖ ^ 2 ≤ V.form u u + c * E.form u u ∧
    V.form u u + c * E.form u u ≤ (βV + c * βE) * ‖u‖ ^ 2
  constructor
  · calc
      _ = αV * ‖u‖ ^ 2 + c * (αE * ‖u‖ ^ 2) := by ring
      _ ≤ _ := add_le_add (hV u).1 (mul_le_mul_of_nonneg_left (hE u).1 hc)
  · calc
      _ ≤ βV * ‖u‖ ^ 2 + c * (βE * ‖u‖ ^ 2) :=
        add_le_add (hV u).2 (mul_le_mul_of_nonneg_left (hE u).2 hc)
      _ = _ := by ring

end KVApproximation.OperatorTheory
