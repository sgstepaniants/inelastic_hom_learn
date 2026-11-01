module

public import Mathlib.Analysis.Complex.Basic

@[expose] public section

noncomputable section

namespace KVApproximation.Analysis

/-- Lemma B.9, analytic coefficient proof: the Joukowski map from the
annulus to the Bernstein ellipse. -/
def joukowski (z : ℂ) : ℂ := (z + z⁻¹) / 2

end KVApproximation.Analysis
