module

public import KVApproximation.Approximation.Dimension

/-!
# Dimensions for alternative Prony constructions
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Approximation

/-- Remark 4.6: the explicit unweighted interpolation constant from the
unweighted response bound and Proposition 3.3's total-variation estimate. -/
def unweightedErrorConstant (tensorDimension : ℕ) (stressScale elasticityContrast : ℝ) : ℝ :=
  4 * (tensorDimension : ℝ) * stressScale * elasticityContrast / Real.cos (3 / 4)

/-- Remark 4.6: a sufficient dimension for unweighted local interpolation.
The factor two leaves a positive error margin for neural-response approximation. -/
def unweightedDimension (tensorDimension : ℕ) (R relativeError elasticityContrast : ℝ) : ℕ :=
  tensorDimension * logPartitionCount R *
    interpolationOrder (2 * unweightedErrorConstant tensorDimension 1 elasticityContrast) relativeError

/-- Remark 4.6: the error bound for the ellipse parameter `1 + 1/R`, used
when `R ≥ 1`. -/
def globalPronyErrorBound (tensorDimension : ℕ) (stressScale R : ℝ) (n : ℕ) : ℝ :=
  pronyConstant tensorDimension stressScale * R / (1 + 1 / R) ^ (n - 1)

/-- Remark 4.6: the interpolation order for one global logarithmic patch. -/
def globalInterpolationOrder (tensorDimension : ℕ) (R relativeError : ℝ) : ℕ :=
  1 + ⌈max 0 (Real.log (pronyConstant tensorDimension 1 * R / relativeError) /
    Real.log (1 + 1 / R))⌉₊

/-- Remark 4.6: scalar state dimension of the global logarithmic construction. -/
def globalPronyDimension (tensorDimension : ℕ) (R relativeError : ℝ) : ℕ :=
  tensorDimension * globalInterpolationOrder tensorDimension R relativeError


end KVApproximation.Approximation
