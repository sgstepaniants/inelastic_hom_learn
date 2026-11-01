module

public import Mathlib.Basic.Real.Basic

/-!
# Scalar bounds for the spectral measure

These are the numerical expressions in Proposition 3.3 and Lemma B.6.
They do not assume the existence of a material in the admissible class.
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Spectral

/-- Proposition 3.3 (`prop:spectral_rep`): the lower spectral endpoint. -/
def lowerRate (elasticityLower viscosityUpper : ℝ) : ℝ :=
  elasticityLower / viscosityUpper

/-- Proposition 3.3 (`prop:spectral_rep`): the upper spectral endpoint. -/
def upperRate (elasticityUpper viscosityLower : ℝ) : ℝ :=
  elasticityUpper / viscosityLower

/-- Proposition 3.3 (`eq:uniform_TV_bound_nu_explicit`): the upper bound on
Frobenius total variation of the compressed spectral measure. -/
def spectralVariationBound (tensorDimension : ℕ)
    (viscosityUpper elasticityUpper elasticityLower : ℝ) : ℝ :=
  (tensorDimension : ℝ) * viscosityUpper * elasticityUpper / elasticityLower

/-- Lemma B.6, proof of `eq:weighted_measure_mass`: the common quantitative
bound used before taking the supremum over materials. -/
def weightedVariationBound (tensorDimension : ℕ)
    (viscosityLower viscosityUpper elasticityLower elasticityUpper : ℝ) : ℝ :=
  (tensorDimension : ℝ) *
    (2 * viscosityUpper - viscosityLower -
      viscosityUpper * elasticityLower / elasticityUpper)

end KVApproximation.Spectral
