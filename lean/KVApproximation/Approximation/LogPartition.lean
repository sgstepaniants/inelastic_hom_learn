module

public import KVApproximation.Approximation.Dimension

/-!
# Local logarithmic coordinates for relaxation rates
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Approximation

/-- Definition B.8: the logarithmic spectral span. The local construction
uses positive endpoints with `lower < upper`. -/
def logarithmicSpan (lower upper : ℝ) : ℝ := Real.log (upper / lower)

/-- Definition B.8: the centre `τⱼ` of a logarithmic hat function.
The Lean index starts at zero. -/
def logPartitionCenter (R : ℝ) (j : Fin (logPartitionCount R)) : ℝ :=
  (j.val : ℝ) * logPartitionWidth R

/-- Definition B.8: the left endpoint `aⱼ` of a logarithmic patch. -/
def logPatchLeft (R : ℝ) (j : Fin (logPartitionCount R)) : ℝ :=
  max 0 (logPartitionCenter R j - logPartitionWidth R)

/-- Definition B.8: the right endpoint `bⱼ` of a logarithmic patch. -/
def logPatchRight (R : ℝ) (j : Fin (logPartitionCount R)) : ℝ :=
  min R (logPartitionCenter R j + logPartitionWidth R)

/-- Definition B.8: a hat function in the logarithmic variable. -/
def logHat (R : ℝ) (j : Fin (logPartitionCount R)) (x : ℝ) : ℝ :=
  max (1 - |x - logPartitionCenter R j| / logPartitionWidth R) 0

/-- Definition B.8: the spectral partition weight `θⱼ`. -/
def spectralWeight (lower upper : ℝ)
    (j : Fin (logPartitionCount (logarithmicSpan lower upper))) (rate : ℝ) : ℝ :=
  logHat (logarithmicSpan lower upper) j (Real.log (rate / lower))

/-- Definition B.8 (`eq:log_spectral_coordinate`): the local map `gⱼ`
from the reference interval to a patch of relaxation rates. -/
def localRate (lower R : ℝ) (j : Fin (logPartitionCount R)) (x : ℝ) : ℝ :=
  lower * Real.exp ((logPatchLeft R j + logPatchRight R j) / 2 +
    (logPatchRight R j - logPatchLeft R j) / 2 * x)

/-- Definition B.8 (`eq:log_spectral_coordinate`): the inverse reference
coordinate `ψⱼ` on a nondegenerate patch. -/
def localCoordinate (lower R : ℝ) (j : Fin (logPartitionCount R)) (rate : ℝ) : ℝ :=
  (2 * Real.log (rate / lower) - logPatchLeft R j - logPatchRight R j) /
    (logPatchRight R j - logPatchLeft R j)

end KVApproximation.Approximation
