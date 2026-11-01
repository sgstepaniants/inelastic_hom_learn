module

public import KVApproximation.Approximation.LogPartition
public import KVApproximation.Approximation.Interpolation
public import KVApproximation.Spectral.TensorMeasure

/-!
# Prony coefficients from local Chebyshev interpolation
-/

@[expose] public section

noncomputable section

open KVApproximation.Tensor KVApproximation.Spectral

namespace KVApproximation.Approximation

/-- Definition B.8 (`eq:Ki_def`): the material-independent rate of a
Chebyshev node in one logarithmic patch. -/
def localPronyRate (lower upper : ℝ) (m : ℕ)
    (j : Fin (logPartitionCount (logarithmicSpan lower upper))) (i : Fin m) : ℝ :=
  localRate lower (logarithmicSpan lower upper) j (chebyshevNode m i)

/-- Definition B.8 (`eq:Ki_def`): the signed coefficient tensor obtained
by integrating the partition weight and local Lagrange polynomial against
the weighted spectral measure. -/
def localPronyCoefficient {d : ℕ} (ν : TensorMeasure d) (c lower upper : ℝ) (m : ℕ)
    (j : Fin (logPartitionCount (logarithmicSpan lower upper))) (i : Fin m) :
    Elasticity d :=
  (c + localPronyRate lower upper m j i) •
    tensorIntegral (weightedMeasure c ν) (fun r =>
      spectralWeight lower upper j r *
        (chebyshevLagrange m i).eval (localCoordinate lower (logarithmicSpan lower upper) j r))

/-- Definition B.8 (`eq:Ki_def_degenerate`): the single coefficient for
a singleton spectral interval. -/
def singletonPronyCoefficient {d : ℕ} (ν : TensorMeasure d) : Elasticity d :=
  tensorIntegral ν (fun r => r)

/-- Definition B.8 (`eq:Kn_def`): the nonsingleton Prony kernel, retaining
the two local indices before their identification with `Fin (J*m)`. -/
def localPronyKernel {d : ℕ} (ν : TensorMeasure d) (c lower upper : ℝ) (m : ℕ)
    (t : ℝ) : Elasticity d :=
  ∑ j, ∑ i, Real.exp (-localPronyRate lower upper m j i * t) •
    localPronyCoefficient ν c lower upper m j i

end KVApproximation.Approximation
