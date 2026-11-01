module

public import KVApproximation.Approximation.Constants
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Interpolation order and internal-variable dimension
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Approximation

/-- Theorem 4.5 (`thm:sufficient_dimension`): the nonnegative part of the
base-two logarithm. Its approximation-theoretic uses have a positive argument. -/
def log2Positive (x : ℝ) : ℝ :=
  max 0 (Real.log x / Real.log 2)

/-- Theorem 4.5, proof: the positive interpolation order chosen from a Prony
constant `κ` and a positive absolute error tolerance `ε`. -/
def interpolationOrder (κ ε : ℝ) : ℕ :=
  1 + ⌈log2Positive (κ / ε)⌉₊

/-- Definition B.8 (`def:prony_series_approximation`): the number of
logarithmic partition intervals for a positive logarithmic spectral span. -/
def logPartitionIntervals (logSpan : ℝ) : ℕ :=
  ⌈logSpan⌉₊

/-- Definition B.8: the number of overlapping logarithmic hat functions in
the nonsingleton construction. -/
def logPartitionCount (logSpan : ℝ) : ℕ :=
  logPartitionIntervals logSpan + 1

/-- Definition B.8: the logarithmic mesh width. The nonsingleton construction
proves that both `logSpan` and its ceiling are positive. -/
def logPartitionWidth (logSpan : ℝ) : ℝ :=
  logSpan / (logPartitionIntervals logSpan : ℝ)

/-- Theorem 4.5 (`thm:sufficient_dimension`): the nonsingleton scalar
internal-variable dimension, with `logSpan > 0` and relative stress error
`relativeError > 0`. The singleton dimension is stated separately. -/
def nonsingletonStateDimension
    (tensorDimension : ℕ) (logSpan relativeError : ℝ) : ℕ :=
  tensorDimension * logPartitionCount logSpan *
    interpolationOrder (pronyConstant tensorDimension 1) relativeError

end KVApproximation.Approximation
