module

public import KVApproximation.Spectral.Bounds

/-!
# Scalar mass-gap statement for Lemma B.6
-/

@[expose] public section

namespace KVApproximation.Spectral

/-- Lemma B.6, proof: the same strict gap holds for every admissible material,
before any supremum is taken. No nonempty material class is assumed. -/
theorem weightedVariationBound_lt
    {tensorDimension : ℕ} (hdim : 0 < tensorDimension)
    {viscosityLower viscosityUpper elasticityLower elasticityUpper : ℝ}
    (hvl : 0 < viscosityLower) (hvu : 0 < viscosityUpper)
    (hel : 0 < elasticityLower) (heu : 0 < elasticityUpper) :
    weightedVariationBound tensorDimension
        viscosityLower viscosityUpper elasticityLower elasticityUpper <
      2 * (tensorDimension : ℝ) * viscosityUpper := by
  sorry

end KVApproximation.Spectral
