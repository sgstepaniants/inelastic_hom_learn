module

public import KVApproximation.OperatorTheory.CoerciveCombinations

public section

namespace KVApproximation.OperatorTheory

/-- Theorem 3.1 and Lemma B.6: the positive linear combination preserves
the corresponding linear combinations of lower and upper energy bounds. -/
theorem CoerciveForm.addScaled_bounds
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (V E : CoerciveForm H) (c : ℝ) (hc : 0 ≤ c) {αV βV αE βE : ℝ}
    (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE) :
    (V.addScaled E c hc).HasBounds (αV + c * αE) (βV + c * βE) := by
  sorry

end KVApproximation.OperatorTheory
