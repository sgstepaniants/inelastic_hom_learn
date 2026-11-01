module

public import KVApproximation.OperatorTheory.CoerciveSolvers
public import Mathlib.Analysis.Normed.Algebra.Spectrum

public section

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Remark 1.2 (`rem:2`), relaxation rates: the full-space relative
Riesz operator has the same positive spectral bounds as its variational
realization, with the spectrum taken in the original Hilbert norm. -/
theorem relativeRiesz_spectrum_subset (V E : CoerciveForm H)
    {αV βV αE βE : ℝ} (hαV : 0 < αV) (hβV : 0 < βV)
    (hαE : 0 < αE) (hβE : 0 < βE)
    (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE) :
    spectrum ℝ (relativeRiesz V E) ⊆ Set.Icc (αE / βV) (βE / αV) := by
  sorry

end KVApproximation.OperatorTheory
