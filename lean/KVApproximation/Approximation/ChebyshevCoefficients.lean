module

public import KVApproximation.Analysis.Joukowski
public import KVApproximation.Analysis.AnnulusCoefficients

@[expose] public section

noncomputable section

namespace KVApproximation.Approximation

/-- Lemma B.9, proof: the Chebyshev coefficients of a scalar function.
The constant mode is unscaled; positive modes pair opposite Laurent coefficients. -/
def chebyshevCoefficient (f : ℂ → ℂ) (k : ℕ) : ℂ :=
  if k = 0 then Analysis.circleCoefficient (f ∘ Analysis.joukowski) 1 0
  else 2 * Analysis.circleCoefficient (f ∘ Analysis.joukowski) 1 k

end KVApproximation.Approximation
