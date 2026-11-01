module

public import KVApproximation.OperatorTheory.WeightedRelaxation
public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus

/-!
# Spectral transport for the viscous Hilbert structure
-/

public section

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Appendix A.2: changing to the equivalent viscous Hilbert norm preserves the spectrum. -/
theorem weightedRelaxation_spectrum_eq (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H) :
    spectrum ℝ (weightedRelaxation V E X) = spectrum ℝ (relaxation V E X) := by
  sorry

/-- Section 3.2: only the elastic lower and viscous upper bounds are needed
for the lower relaxation bound. -/
theorem weightedRelaxation_lower_bound (V E : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) {αV βV αE βE : ℝ} (hβV : 0 < βV) (hαE : 0 < αE)
    (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE) :
    algebraMap ℝ _ (αE / βV) ≤ weightedRelaxation V E X := by
  sorry

/-- Appendix A.2: complexification preserves the common spectral interval. -/
theorem weightedRelaxation_complex_spectrum_subset (V E : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) {αV βV αE βE : ℝ}
    (hαV : 0 < αV) (hβV : 0 < βV) (hαE : 0 < αE) (hβE : 0 < βE)
    (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE) :
    ∀ z ∈ spectrum ℂ (weightedRelaxation V E X).complexifyL2,
      z.re ∈ Set.Icc (αE / βV) (βE / αV) := by
  sorry

end KVApproximation.OperatorTheory
